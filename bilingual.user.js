// ==UserScript==
// @name         双语
// @namespace    bilingual-reader
// @version      0.1.0
// @description  使用 Google 或 Microsoft 翻译网页正文，保留原文。
// @license      GPL-3.0-only
// @match        http://*/*
// @match        https://*/*
// @noframes
// @run-at       document-idle
// @grant        GM_xmlhttpRequest
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_registerMenuCommand
// @grant        GM_unregisterMenuCommand
// @grant        GM_addValueChangeListener
// @connect      translate.googleapis.com
// @connect      edge.microsoft.com
// ==/UserScript==

(() => {
  'use strict';

  const MARK = 'data-bilingual-reader';
  const SKIP = `script,style,noscript,textarea,input,select,button,pre,rt,rp,svg,math,canvas,iframe,nav,aside,footer,form,dialog,menu,[role="navigation"],[role="banner"],[role="complementary"],[role="contentinfo"],[role="dialog"],[role="toolbar"],.sidebar,.breadcrumbs,.breadcrumb,.pagination,.comments,#comments,.comment-list,.social-share,.sr-only,.visually-hidden,[role="img"],[contenteditable]:not([contenteditable="false"]),[translate="no"],[hidden],[aria-hidden="true"],.notranslate,[${MARK}]`;
  const ARTICLE = '[itemprop="articleBody"],article,[role="article"],.article-body,.article-content,.post-content,.post-body,.entry-content,.markdown-body';
  const MAIN = 'main,[role="main"],#main-content,#mainContent,#content,.main-content';
  const records = new Map();
  const cache = new Map();
  const pending = new Map();
  const requests = new Set();
  const dirty = new Set();
  let reselect = true;
  let limit = 12;
  let successes = 0;
  let timeouts = 0;
  let resumeAt = 0;
  let resumeTimer;
  let provider = GM_getValue('provider', 'google');
  if (!['google', 'microsoft'].includes(provider)) provider = 'google';
  let target = GM_getValue('target', navigator.language || 'zh-CN');
  const concurrency = 12;
  const siteKey = `siteEnabled:${location.hostname}`;
  let siteEnabled = GM_getValue(siteKey, true);
  let enabled = false;
  let region;
  let pageUrl = location.href;
  let epoch = 0;
  let active = 0;
  let timer;
  let queue = [];
  let menuIds = [];

  function request(url, data) {
    return new Promise((resolve, reject) => {
      let handle;
      const finish = (error, value) => {
        requests.delete(handle);
        if (error) reject(error);
        else resolve(value);
      };
      handle = GM_xmlhttpRequest({
        url,
        method: data === undefined ? 'GET' : 'POST',
        headers: data === undefined ? {} : { 'Content-Type': 'application/json' },
        data: data === undefined ? undefined : JSON.stringify(data),
        anonymous: true,
        timeout: 15000,
        onload: (response) => {
          if (response.status < 200 || response.status >= 300) {
            const error = new Error(`HTTP ${response.status}`);
            error.status = response.status;
            const retry = response.responseHeaders?.match(/^retry-after:\s*(.+)$/im)?.[1]?.trim();
            error.delay = retry ? (/^\d+$/.test(retry) ? Number(retry) * 1000 : Math.max(0, Date.parse(retry) - Date.now())) : 0;
            finish(error);
            return;
          }
          try { finish(null, JSON.parse(response.responseText)); }
          catch { finish(new Error('翻译接口返回了无效数据')); }
        },
        onerror: () => finish(new Error('网络请求失败')),
        ontimeout: () => finish(Object.assign(new Error('翻译请求超时'), { timeout: true })),
        onabort: () => finish(new Error('翻译已停止')),
      });
      requests.add(handle);
    });
  }

  function splitText(text) {
    const chunks = [];
    while (text.length > 1200) {
      const sample = text.slice(0, 1200);
      const boundaries = [...sample.matchAll(/[。！？.!?]\s*|\s+/g)];
      const last = boundaries.at(-1);
      let end = last && last.index > 600 ? last.index + last[0].length : 1200;
      const tokenStart = text.lastIndexOf('⟦B', end - 1);
      if (tokenStart >= 0 && text.indexOf('⟧', tokenStart) >= end) end = tokenStart;
      if (/[\uD800-\uDBFF]/.test(text[end - 1])) end--;
      chunks.push(text.slice(0, end));
      text = text.slice(end);
    }
    if (text) chunks.push(text);
    return chunks;
  }

  function baseLanguage(language) {
    return String(language || '').toLowerCase().split('-')[0];
  }

  function languageForm(code) {
    const language = baseLanguage(code);
    if (language !== 'zh') return language;
    return /hant|tw|hk|mo/i.test(code) ? 'zh-Hant' : /hans|cn|sg/i.test(code) ? 'zh-Hans' : 'zh';
  }

  function isSameLanguage(source, destination) {
    if (!source || baseLanguage(source) !== baseLanguage(destination)) return false;
    if (baseLanguage(destination) !== 'zh' || languageForm(destination) === 'zh') return true;
    return languageForm(source) === languageForm(destination);
  }

  // 中文简繁不明确时交给服务转换，不按汉字占比直接跳过。
  function isTargetScript(text, element) {
    const letters = text.match(/\p{L}/gu) || [];
    if (!letters.length) return true;
    const ratio = pattern => (text.match(pattern) || []).length / letters.length;
    const language = baseLanguage(target);
    const declared = element.closest('[lang]')?.lang;
    if (declared && baseLanguage(declared) !== language) return false;
    if (language === 'zh') return languageForm(target) === 'zh' && ratio(/\p{Script=Han}/gu) > 0.95 && !/[\p{Script=Hiragana}\p{Script=Katakana}\p{Script=Hangul}]/u.test(text);
    if (language === 'ja') return /[\p{Script=Hiragana}\p{Script=Katakana}]/u.test(text) && ratio(/[\p{Script=Han}\p{Script=Hiragana}\p{Script=Katakana}]/gu) > 0.95;
    if (language === 'ko') return ratio(/\p{Script=Hangul}/gu) > 0.95;
    return false;
  }

  function translate(text, service, language, generation) {
    const key = JSON.stringify([service, language, text]);
    if (cache.has(key)) return Promise.resolve(cache.get(key));
    if (pending.has(key)) return pending.get(key);
    const task = translateText(text, service, language, generation).then(result => {
      if (generation === epoch) {
        if (cache.size >= 500) cache.delete(cache.keys().next().value);
        cache.set(key, result);
      }
      return result;
    }).finally(() => {
      if (pending.get(key) === task) pending.delete(key);
    });
    pending.set(key, task);
    return task;
  }

  async function translateText(text, service, language, generation) {
    const output = [];
    let sameLanguage = true;
    for (const chunk of splitText(text)) {
      if (generation !== epoch) throw new Error('翻译已停止');
      let value;
      let detected;
      if (service === 'google') {
        const params = new URLSearchParams({ client: 'gtx', sl: 'auto', tl: language, dt: 't', q: chunk });
        const result = await request(`https://translate.googleapis.com/translate_a/single?${params}`);
        if (!Array.isArray(result?.[0])) throw new Error('Google 返回格式异常');
        value = result[0].map((part) => part?.[0] || '').join('');
        detected = result[2];
      } else {
        const msLanguage = baseLanguage(language) === 'zh'
          ? (/tw|hk|hant/i.test(language) ? 'zh-Hant' : 'zh-Hans') : language;
        const escaped = chunk.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;').replace(/'/g, '&apos;');
        const result = await request(`https://edge.microsoft.com/translate/translatetext?from=&to=${encodeURIComponent(msLanguage)}&isEnterpriseClient=false`, [escaped]);
        value = result?.[0]?.translations?.[0]?.text;
        detected = result?.[0]?.detectedLanguage?.language;
        if (typeof value === 'string') {
          value = value.replace(/&(amp|lt|gt|quot|apos|#39);/g, (_, entity) => ({ amp: '&', lt: '<', gt: '>', quot: '"', apos: "'", '#39': "'" })[entity]);
        }
      }
      if (typeof value !== 'string' || !value.trim()) throw new Error('翻译结果为空');
      output.push(value);
      sameLanguage &&= Boolean(detected) && isSameLanguage(detected, language);
    }
    return { text: output.join(''), sameLanguage };
  }

  function isExcluded(element) {
    if (element.isContentEditable || element.closest(SKIP)) return true;
    const header = element.closest('header');
    return Boolean(header && !header.closest(ARTICLE));
  }

  function* textNodes(root) {
    const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT | NodeFilter.SHOW_ELEMENT, {
      acceptNode(node) {
        const element = node.nodeType === Node.ELEMENT_NODE ? node : node.parentElement;
        if (isExcluded(element) || !isVisible(element)) return NodeFilter.FILTER_REJECT;
        return node.nodeType === Node.TEXT_NODE || node.tagName === 'BR'
          ? NodeFilter.FILTER_ACCEPT : NodeFilter.FILTER_SKIP;
      },
    });
    while (walker.nextNode()) yield walker.currentNode;
  }

  function selectRegion() {
    const texts = new WeakMap();
    function textOf(element) {
      if (!texts.has(element)) {
        let text = '';
        for (const node of textNodes(element)) text += node.nodeType === Node.TEXT_NODE ? node.textContent : '\n';
        texts.set(element, text.trim());
      }
      return texts.get(element);
    }
    const candidates = new Set(document.querySelectorAll(`${ARTICLE},${MAIN}`));
    // 无语义容器时，仅从连续长段落向上寻找正文，不回退到整个页面。
    for (const paragraph of document.querySelectorAll('p')) {
      if (isExcluded(paragraph) || !isVisible(paragraph) || textOf(paragraph).length < 80) continue;
      let parent = paragraph.parentElement;
      for (let depth = 0; parent && parent !== document.body && depth < 3; depth++, parent = parent.parentElement) {
        candidates.add(parent);
      }
    }
    let best = null;
    let bestScore = 0;
    for (const element of candidates) {
      if (isExcluded(element) || !isVisible(element)) continue;
      const explicit = element.matches(ARTICLE);
      const paragraphs = [...element.querySelectorAll('p,blockquote')].filter(part =>
        !(part.tagName === 'BLOCKQUOTE' && part.querySelector('p')) &&
        !isExcluded(part) && isVisible(part) && textOf(part).length >= 40);
      // 多篇文章组成的列表不作为一篇正文处理。
      if ([...element.querySelectorAll('article,[role="article"]')].filter(part =>
        !isExcluded(part) && isVisible(part)).length > 1) continue;
      if (!explicit && paragraphs.length < 2) continue;
      const length = paragraphs.length
        ? paragraphs.reduce((sum, part) => sum + textOf(part).length, 0) : textOf(element).length;
      if (length < (explicit ? 60 : 200)) continue;
      const links = [...element.querySelectorAll('a')].reduce((sum, link) => sum + textOf(link).length, 0);
      const total = textOf(element).length;
      if (links / Math.max(total, 1) > 0.35) continue;
      const density = Math.min(1, length / Math.max(total, 1));
      const body = element.matches('[itemprop="articleBody"],.article-body,.article-content,.post-content,.post-body,.entry-content,.markdown-body');
      const score = length * density * (body ? 1.8 : explicit ? 1.4 : 1) + paragraphs.length * 40;
      if (score > bestScore || (score === bestScore && best?.contains(element))) {
        best = element;
        bestScore = score;
      }
    }
    return best;
  }

  function collect(root = region) {
    const groups = new Map();
    if (!root?.isConnected) return groups;
    function walk(element) {
      if (isExcluded(element) || !isVisible(element)) return;
      const style = getComputedStyle(element);
      const layout = /^(inline-)?(flex|grid)$/.test(style.display);
      const preserve = /^(pre|pre-wrap|pre-line|break-spaces)$/.test(style.whiteSpace);
      let nodes = [];
      let parts = [];
      let protectedNodes = [];
      function flush() {
        if (nodes.length && !layout) {
          const text = parts.join('');
          groups.set(nodes[0], {
            element, end: nodes.at(-1), protectedNodes,
            text: text.replace(/[^\S\n]+/g, ' ').trim(),
          });
        }
        nodes = [];
        parts = [];
        protectedNodes = [];
      }
      function inline(node) {
        if (node.nodeType === Node.TEXT_NODE) {
          nodes.push(node);
          parts.push(preserve ? node.data.replace(/\r\n?/g, '\n') : node.data.replace(/\s+/g, ' '));
          return;
        }
        if (node.nodeType !== Node.ELEMENT_NODE || node.hasAttribute(MARK)) return;
        if (node.matches('code,kbd,samp,var,math,.katex,.MathJax,.MathJax_Display') && isVisible(node)) {
          nodes.push(node);
          const token = `⟦B${protectedNodes.length}⟧`;
          protectedNodes.push({ token, node, value: node.outerHTML });
          parts.push(token);
          return;
        }
        if (isExcluded(node) || !isVisible(node)) {
          parts.push(' ');
          return;
        }
        if (node.tagName === 'BR') {
          nodes.push(node);
          parts.push('\n');
          return;
        }
        const childStyle = getComputedStyle(node);
        const dropCap = childStyle.float === 'left' && node.nextSibling;
        const atomic = node.matches('code,kbd,samp,var,ruby');
        const isInline = atomic || dropCap || childStyle.display.startsWith('inline') || childStyle.display.startsWith('ruby') || childStyle.display === 'contents';
        if (!isInline) {
          flush();
          walk(node);
        } else if (atomic) {
          nodes.push(node);
          if (node.tagName === 'RUBY') {
            parts.push([...textNodes(node)].map(part => part.nodeType === Node.TEXT_NODE ? part.data : ' ').join(''));
          } else {
            parts.push(node.textContent);
          }
        } else {
          for (const child of node.childNodes) inline(child);
        }
      }
      for (const child of element.childNodes) {
        if (layout && child.nodeType === Node.ELEMENT_NODE && !child.hasAttribute(MARK)) walk(child);
        else inline(child);
      }
      flush();
    }
    walk(root);
    return groups;
  }

  function discard(key) {
    records.get(key)?.output?.remove();
    records.delete(key);
  }

  function shouldTranslate(text, element) {
    text = text.replace(/⟦B\d+⟧/g, '').trim();
    if (!/\p{L}/u.test(text) || /^@\S+$/.test(text) || /^(https?:\/\/|www\.)\S+$/i.test(text)) return false;
    if (/^[\w.+-]+@[\w.-]+\.[a-z]+$/i.test(text)) return false;
    if (!element.matches('h1,h2,h3,h4,h5,h6') && (text.match(/\p{L}/gu) || []).length < 3) return false;
    return !isTargetScript(text, element);
  }

  function scan() {
    clearTimeout(timer);
    timer = undefined;
    if (!enabled) return;
    if (pageUrl !== location.href) {
      pageUrl = location.href;
      restart();
      return;
    }
    let roots;
    if (reselect || !region?.isConnected || isExcluded(region) || !isVisible(region)) {
      const next = selectRegion();
      if (next !== region) {
        for (const key of records.keys()) discard(key);
        region = next;
      }
      roots = region ? [region] : [];
    } else {
      roots = [...dirty].filter(root => root.isConnected && region.contains(root));
    }
    reselect = false;
    dirty.clear();
    roots = roots.filter(root => !roots.some(other => other !== root && other.contains(root)));
    const groups = new Map();
    for (const root of roots) for (const entry of collect(root)) groups.set(...entry);
    for (const [key, record] of records) {
      if (!key.isConnected || !region?.contains(record.element) || (roots.some(root => root.contains(record.element)) && !groups.has(key))) discard(key);
    }
    for (const [key, group] of groups) {
      const { text, element, end, protectedNodes } = group;
      if (!shouldTranslate(text, element)) {
        discard(key);
        continue;
      }
      let record = records.get(key);
      if (!record || record.element !== element || record.text !== text || record.end !== end || record.protectedNodes.some((part, index) => part.value !== protectedNodes[index]?.value) || record.protectedNodes.length !== protectedNodes.length || (record.output && !element.contains(record.output))) {
        discard(key);
        record = { ...group, pending: false, output: null, retries: 0 };
        records.set(key, record);
      }
      if (!record.pending) viewport.observe(element);
    }
    queue = queue.filter(([key, record]) => records.get(key) === record && key.isConnected);
  }

  function scheduleScan() {
    if (timer === undefined) timer = setTimeout(scan, 150);
  }

  function isVisible(element) {
    const style = getComputedStyle(element);
    const font = style.fontFamily.split(',')[0].replace(/["']/g, '').trim().toLowerCase();
    if (/^(material icons|material symbols|google symbols|font awesome|fontawesome)(\s|$)/.test(font)) return false;
    return style.visibility === 'visible' && style.display !== 'none' && (element.getClientRects().length > 0 || style.display === 'contents');
  }

  function isCurrent(key, record) {
    if (!key.isConnected || !region?.contains(record.element) || !isVisible(record.element)) return false;
    const current = collect(record.element).get(key);
    return current?.text === record.text && current.end === record.end &&
      current.protectedNodes.length === record.protectedNodes.length &&
      current.protectedNodes.every((part, index) => part.node === record.protectedNodes[index].node && part.value === record.protectedNodes[index].value);
  }

  function render(record, text) {
    for (const part of record.protectedNodes) {
      if (text.split(part.token).length !== 2) throw new Error('受保护内容未完整返回');
    }
    const output = document.createElement('span');
    output.setAttribute(MARK, 'translation');
    output.setAttribute('translate', 'no');
    output.lang = target;
    output.dir = 'auto';
    output.append(document.createElement('br'));
    for (const part of text.split(/(⟦B\d+⟧|\n)/g)) {
      const protectedPart = record.protectedNodes.find(item => item.token === part);
      if (protectedPart) {
        const clone = protectedPart.node.cloneNode(true);
        clone.removeAttribute('id');
        for (const child of clone.querySelectorAll('[id]')) child.removeAttribute('id');
        output.append(clone);
      } else if (part === '\n') output.append(document.createElement('br'));
      else output.append(document.createTextNode(part));
    }
    let anchor = record.end;
    while (anchor.parentElement !== record.element && anchor.parentElement?.lastChild === anchor) anchor = anchor.parentElement;
    for (let parent = anchor.parentElement; parent && parent !== record.element; parent = parent.parentElement) {
      if (parent.matches('a,button,code,kbd,ruby')) anchor = parent;
    }
    anchor.after(output);
    record.output = output;
  }

  function pump() {
    if (!enabled) return;
    if (Date.now() < resumeAt) {
      clearTimeout(resumeTimer);
      resumeTimer = setTimeout(pump, Math.min(resumeAt - Date.now(), 2147483647));
      return;
    }
    while (enabled && active < limit && queue.length) {
      const [element, record] = queue.shift();
      if (records.get(element) !== record || !element.isConnected) continue;
      const generation = epoch;
      const service = provider;
      const language = target;
      active++;
      translate(record.text, service, language, generation).then((result) => {
        if (generation !== epoch || records.get(element) !== record || !element.isConnected) return;
        if (!isCurrent(element, record)) {
          discard(element);
          dirty.add(record.element);
          scheduleScan();
          return;
        }
        timeouts = 0;
        if (++successes >= 12) { limit = Math.min(concurrency, limit + 1); successes = 0; }
        if (result.sameLanguage) return;
        if (result.text.trim() !== record.text) render(record, result.text);
      }).catch((error) => {
        if (generation !== epoch || records.get(element) !== record || !element.isConnected) return;
        if (error.timeout) timeouts++;
        if (error.status === 429 || (error.timeout && timeouts >= 2)) {
          limit = Math.max(1, Math.floor(limit / 2));
          successes = 0;
          timeouts = 0;
          resumeAt = Math.max(resumeAt, Date.now() + Math.max(error.delay || 0, 2000 * 2 ** record.retries));
          if (record.retries++ < 2) queue.push([element, record]);
        }
        console.warn('[双语]', error.message);
      }).finally(() => {
        active--;
        pump();
      });
    }
  }

  const viewport = new IntersectionObserver((entries) => {
    for (const entry of entries) {
      if (!enabled || !entry.isIntersecting || !isVisible(entry.target)) continue;
      for (const [key, record] of records) {
        if (record.element !== entry.target || record.pending || !key.isConnected) continue;
        record.pending = true;
        queue.push([key, record]);
      }
      viewport.unobserve(entry.target);
    }
    queue.sort((a, b) => Math.abs(a[1].element.getBoundingClientRect().top) - Math.abs(b[1].element.getBoundingClientRect().top));
    pump();
  }, { rootMargin: '500px' });

  function affectedRoot(element) {
    if (!region?.contains(element)) return null;
    while (element !== region) {
      const display = getComputedStyle(element).display;
      if (!display.startsWith('inline') && display !== 'contents') break;
      element = element.parentElement;
    }
    return element;
  }

  const observer = new MutationObserver(mutations => {
    let changed = false;
    for (const mutation of mutations) {
      const element = mutation.target.nodeType === Node.ELEMENT_NODE ? mutation.target : mutation.target.parentElement;
      if (!element || element.closest(`[${MARK}]`)) continue;
      if (mutation.type === 'childList' && [...mutation.addedNodes, ...mutation.removedNodes].every(node =>
        node.nodeType === Node.ELEMENT_NODE && node.hasAttribute(MARK))) continue;
      if (pageUrl !== location.href || !region?.isConnected || !isVisible(region)) reselect = true;
      const root = affectedRoot(element);
      if (root) {
        dirty.add(root);
        if (mutation.type === 'attributes' && root === region) reselect = true;
        if (mutation.type === 'childList' && [...mutation.addedNodes, ...mutation.removedNodes].some(node =>
          node.nodeType === Node.ELEMENT_NODE && !getComputedStyle(node).display.startsWith('inline'))) reselect = true;
        for (const [key, record] of records) {
          if (root.contains(record.element)) discard(key);
        }
        changed = true;
      } else if ((region && element.contains(region)) || element.matches(`${ARTICLE},${MAIN}`) || element.querySelector(`${ARTICLE},${MAIN}`)) {
        reselect = true;
        changed = true;
      }
      if (reselect) changed = true;
    }
    if (changed) scheduleScan();
  });

  function updateMenus() {
    for (const id of menuIds) GM_unregisterMenuCommand(id);
    menuIds = [
      GM_registerMenuCommand(`站点翻译：${siteEnabled ? '开启' : '关闭'}`, () => {
        siteEnabled = !siteEnabled;
        GM_setValue(siteKey, siteEnabled);
        applySiteState();
      }),
      GM_registerMenuCommand(`翻译服务：${provider === 'google' ? 'Google' : 'Microsoft'}`, () => {
        provider = provider === 'google' ? 'microsoft' : 'google';
        GM_setValue('provider', provider);
        restart();
        updateMenus();
      }),
      GM_registerMenuCommand(`目标语言：${target}`, chooseLanguage),
    ];
  }

  function stop() {
    enabled = false;
    epoch++;
    clearTimeout(timer);
    timer = undefined;
    observer.disconnect();
    viewport.disconnect();
    queue = [];
    for (const handle of requests) handle.abort();
    requests.clear();
    pending.clear();
    dirty.clear();
    reselect = true;
    clearTimeout(resumeTimer);
    resumeAt = 0;
    limit = concurrency;
    successes = timeouts = 0;
    for (const record of records.values()) record.output?.remove();
    records.clear();
    region = null;
  }

  function start() {
    if (enabled) return;
    enabled = true;
    observer.observe(document.body, {
      childList: true, subtree: true, characterData: true, attributes: true,
      attributeFilter: ['hidden', 'aria-hidden', 'class', 'style', 'lang', 'translate', 'contenteditable'],
    });
    scan();
  }

  function applySiteState() {
    if (siteEnabled) start();
    else stop();
    updateMenus();
  }

  function restart() {
    stop();
    if (siteEnabled) start();
  }

  function chooseLanguage() {
    const answer = prompt('目标语言', target);
    if (answer === null) return;
    const value = answer.trim();
    if (!value) return;
    let code;
    try { [code] = Intl.getCanonicalLocales(value); }
    catch { return; }
    if (!code || code === target || !/^[a-z]{2,3}(?:-[a-z0-9]{2,8})*$/i.test(code)) return;
    target = code;
    GM_setValue('target', target);
    restart();
    updateMenus();
  }

  GM_addValueChangeListener('provider', (_key, _previous, value, remote) => {
    if (!remote || !['google', 'microsoft'].includes(value) || value === provider) return;
    provider = value;
    restart();
    updateMenus();
  });
  GM_addValueChangeListener('target', (_key, _previous, value, remote) => {
    if (!remote || typeof value !== 'string' || value === target) return;
    target = value;
    restart();
    updateMenus();
  });
  GM_addValueChangeListener(siteKey, (_key, _previous, value, remote) => {
    if (!remote) return;
    siteEnabled = value;
    applySiteState();
  });
  applySiteState();
})();
