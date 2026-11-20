// ==UserScript==
// @name         双语
// @namespace    bilingual
// @version      0.2.0
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
// @connect      translate-pa.googleapis.com
// @connect      edge.microsoft.com
// ==/UserScript==

(() => {
  'use strict';

  const MARK = 'data-bilingual';
  // Default full-page DOM rules adapted from Read Frog (GPL-3.0).
  // https://github.com/mengxi-ream/read-frog/tree/main/src/utils/host
  const HEADINGS = 'h1,h2,h3,h4,h5,h6';
  const NAVIGATION = 'nav,[role="navigation"]';
  const HEADER_NAVIGATION = `:is(header,[role="banner"]) :is(${NAVIGATION}),nav[role="banner"]`;
  const SKIP = `head,title,hr,input,textarea,img,video,audio,canvas,source,track,meta,script,noscript,style,link,rt,rp,pre,svg,math,[${MARK}],.sr-only,.visually-hidden,[hidden="until-found" i],${HEADER_NAVIGATION}`;
  const FORCE_BLOCK = `body,${HEADINGS},br,form,select,button,label,ul,ol,li,blockquote,pre,article,section,figure,figcaption,header,footer,main,nav`;
  const FORCE_INLINE_TRANSLATION = 'a,button,select,option,span';
  const ATOMIC_CONTROL = 'a,button,summary,[role="link"],[role="button"],[role="menuitem"],[role="tab"],[aria-expanded][aria-controls],code,kbd,ruby,sub,sup';
  const INTERACTIVE_REGION = `${ATOMIC_CONTROL},${NAVIGATION},[role="menu"],[role="menubar"],[role="toolbar"],[role="tablist"]`;
  const STRUCTURAL_PARENT = 'table,thead,tbody,tfoot,tr,colgroup,ul,ol,menu,dl,select,optgroup,picture,details';
  const records = new Map();
  const recordsByElement = new Map();
  const PRELOAD = 500;
  const CACHE_KEY = 'bilingualCache:v3';
  const CACHE_LIMIT = 200;
  const savedCache = GM_getValue(CACHE_KEY, {});
  const cache = new Map(savedCache && typeof savedCache === 'object' && !Array.isArray(savedCache) ? Object.entries(savedCache) : []);
  const pending = new Map();
  const requests = new Set();
  const retryTimers = new Set();
  const dirty = new Set();
  let limit = 12;
  let successes = 0;
  let timeouts = 0;
  let resumeAt = 0;
  let resumeTimer;
  let provider = GM_getValue('provider', 'google');
  if (!['google', 'microsoft'].includes(provider)) provider = 'google';
  let target = GM_getValue('target', navigator.language || 'zh-CN');
  const concurrency = 18;
  const siteKey = `siteEnabled:${location.hostname}`;
  let siteEnabled = GM_getValue(siteKey, true);
  let enabled = false;
  let pageUrl = location.href;
  let epoch = 0;
  let active = 0;
  let timer;
  let queue = [];
  let menuIds = [];
  let renderQueue = [];
  let renderTimer;
  let cacheTimer;

  function saveCache() {
    if (cacheTimer !== undefined) return;
    cacheTimer = setTimeout(() => {
      cacheTimer = undefined;
      let size = 0;
      const value = {};
      for (const [key, result] of [...cache].reverse()) {
        size += key.length + result.text.length;
        if (size > 60000) break;
        value[key] = result;
      }
      GM_setValue(CACHE_KEY, value);
    }, 300);
  }

  function remember(service, language, text, result) {
    const key = JSON.stringify([service, language, text]);
    cache.delete(key);
    cache.set(key, result);
    while (cache.size > CACHE_LIMIT) cache.delete(cache.keys().next().value);
    saveCache();
  }

  function request(url, data, headers = { 'Content-Type': 'application/json' }) {
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
        headers: data === undefined ? {} : headers,
        data: data === undefined ? undefined : JSON.stringify(data),
        anonymous: true,
        timeout: 12000,
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
        onerror: () => finish(Object.assign(new Error('网络请求失败'), { network: true })),
        ontimeout: () => finish(Object.assign(new Error('翻译请求超时'), { timeout: true })),
        onabort: () => finish(new Error('翻译已停止')),
      });
      requests.add(handle);
    });
  }

  function escapeText(text) {
    return text.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  }

  function decodeText(text) {
    const template = document.createElement('template');
    template.innerHTML = text.replace(/</g, '&lt;');
    return template.content.textContent;
  }

  async function googleTranslate(text, language, generation) {
    const marker = '<br data-read-frog-lb="1">';
    const lines = text.split('\n');
    try {
      const result = await request('https://translate-pa.googleapis.com/v1/translateHtml',
        [[[lines.map(escapeText).join(marker.repeat(2))], 'auto', language], 'wt_lib'], {
          'Content-Type': 'application/json+protobuf',
          'X-Goog-API-Key': 'AIzaSyATBXajvzQLTDHEQbcpq0Ihe0vWDHmO520',
        });
      const value = result?.[0]?.[0];
      if (typeof value !== 'string' || !value.trim()) throw new Error('Google 返回格式异常');
      const translated = value.split(/(?:[^\S\r\n]*<br data-read-frog-lb="1"\s*\/?>[^\S\r\n]*){2}/);
      if (translated.length === lines.length) {
        return { text: translated.map(decodeText).join('\n'), sameLanguage: isSameLanguage(result[1]?.[0], language) };
      }
    } catch (error) {
      if (error.status === 429 || error.status >= 500 || error.timeout) throw error;
    }
    if (generation !== epoch) throw new Error('翻译已停止');
    const params = new URLSearchParams({ client: 'gtx', sl: 'auto', tl: language, dt: 't', q: text });
    const result = await request(`https://translate.googleapis.com/translate_a/single?${params}`);
    if (!Array.isArray(result?.[0])) throw new Error('Google 返回格式异常');
    return { text: result[0].map(part => part?.[0] || '').join(''), sameLanguage: isSameLanguage(result[2], language) };
  }

  async function microsoftTranslate(texts, language) {
    const form = languageForm(language);
    const destination = baseLanguage(language) === 'zh' ? (form === 'zh-Hant' ? form : 'zh-Hans') : language;
    const result = await request(`https://edge.microsoft.com/translate/translatetext?from=&to=${encodeURIComponent(destination)}&isEnterpriseClient=false`, texts.map(escapeText));
    if (!Array.isArray(result) || result.length !== texts.length) throw new Error('Microsoft 返回格式异常');
    return result.map(item => {
      const value = item?.translations?.[0]?.text;
      if (typeof value !== 'string' || !value.trim()) return null;
      return { text: decodeText(value), sameLanguage: isSameLanguage(item.detectedLanguage?.language, language) };
    });
  }

  function splitText(text) {
    const chunks = [];
    while (text.length > 1800) {
      const sample = text.slice(0, 1800);
      const boundaries = [...sample.matchAll(/[。！？.!?]\s*|\s+/g)];
      const last = boundaries.at(-1);
      let end = last && last.index > 900 ? last.index + last[0].length : 1800;
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
        remember(service, language, text, result);
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
      const result = service === 'google'
        ? await googleTranslate(chunk, language, generation)
        : (await microsoftTranslate([chunk], language))[0];
      if (!result?.text.trim()) throw new Error('翻译结果为空');
      output.push(result.text);
      sameLanguage &&= result.sameLanguage;
    }
    return { text: output.join(''), sameLanguage };
  }

  async function translateMany(texts, service, language, generation) {
    if (texts.length < 2 || texts.some(text => text.length > 1800)) {
      return Promise.allSettled(texts.map(text => translate(text, service, language, generation)));
    }
    const keyFor = text => JSON.stringify([service, language, text]);
    const missing = [...new Set(texts)].filter(text => !cache.has(keyFor(text)) && !pending.has(keyFor(text)));
    const results = new Map();
    if (missing.length) {
      const batch = microsoftTranslate(missing, language);
      missing.forEach((text, index) => {
        const key = keyFor(text);
        const task = batch.then(values => {
          const result = values[index];
          if (!result) throw Object.assign(new Error('Microsoft 翻译结果为空'), { single: true });
          if (generation === epoch) remember(service, language, text, result);
          return result;
        }).finally(() => {
          if (pending.get(key) === task) pending.delete(key);
        });
        pending.set(key, task);
        results.set(text, task);
      });
    }
    return Promise.allSettled(texts.map(text => results.get(text) ?? translate(text, service, language, generation)));
  }

  function isExcluded(element) {
    return element.isContentEditable || Boolean(element.closest(SKIP));
  }

  function isInsideClosedDetails(element) {
    for (let details = element.closest('details:not([open])'); details;
      details = details.parentElement?.closest('details:not([open])')) {
      if (details !== element && ![...details.children].find(child => child.tagName === 'SUMMARY')?.contains(element)) return true;
    }
    return false;
  }

  function isOpaque(element) {
    return element.matches('code,time') ||
      (element !== document.body && element !== document.documentElement && element.classList.contains('notranslate'));
  }

  function isInline(element, style) {
    return !element.matches(FORCE_BLOCK) &&
      ((style.float === 'left' && Boolean(element.nextSibling?.textContent?.trim())) ||
        /^(inline|ruby)/.test(style.display) || style.display === 'contents');
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

  let titleState = { url: location.href, source: '', translated: '' };
  let titlePending;
  function translateTitle() {
    if (location.href !== titleState.url) titleState = { url: location.href, source: '', translated: '' };
    if (!enabled || titlePending || !document.title.trim() ||
      isTargetScript(document.title, document.documentElement)) return;
    const source = document.title;
    if (source === titleState.translated && titleState.translated || source === titleState.source) return;
    titlePending = { source, url: location.href };
    const job = titlePending;
    const generation = epoch;
    translate(source, provider, target, generation).then(result => {
      if (generation !== epoch || job.url !== location.href || source !== document.title) return;
      titleState.source = source;
      titleState.translated = result.sameLanguage ? source : result.text;
      if (!result.sameLanguage) document.title = result.text;
    }).catch(error => console.warn('[双语]', error.message)).finally(() => { if (titlePending === job) {
      titlePending = undefined;
      if (source !== document.title && document.title !== titleState.translated) translateTitle();
    } });
  }

  function collect(root) {
    const groups = new Map();
    for (const group of walkGroups(root)) if (group) groups.set(...group);
    return groups;
  }

  function* walkGroups(root) {
    if (!root?.isConnected || isOpaque(root) || isInsideClosedDetails(root)) return;
    for (let parent = root.parentElement; parent; parent = parent.parentElement) {
      if (isOpaque(parent) || !isVisible(parent)) return;
    }
    function* walk(element) {
      yield;
      const style = getComputedStyle(element);
      if (isExcluded(element) || !isVisible(element, style)) return;
      const layout = /^(inline-)?(flex|grid)$/.test(style.display);
      const preserve = /^(pre|pre-wrap|pre-line|break-spaces)$/.test(style.whiteSpace);
      let nodes = [];
      let parts = [];
      let protectedNodes = [];
      function* flush() {
        if (nodes.length) {
          const text = parts.join('');
          yield [nodes[0], {
            element, end: nodes.at(-1), protectedNodes,
            text: text.replace(/[^\S\n]+/g, ' ').trim(),
          }];
        }
        nodes = [];
        parts = [];
        protectedNodes = [];
      }
      function* inline(node) {
        if (node.nodeType === Node.TEXT_NODE) {
          nodes.push(node);
          parts.push(preserve ? node.data.replace(/\r\n?/g, '\n') : node.data.replace(/\s+/g, ' '));
          return;
        }
        if (node.nodeType !== Node.ELEMENT_NODE || node.hasAttribute(MARK)) return;
        const childStyle = getComputedStyle(node);
        if (!isVisible(node, childStyle)) return;
        if (node.matches('math,kbd,samp,var,.katex,.MathJax,.MathJax_Display') && !isExcluded(element)) {
          nodes.push(node);
          const token = `⟦B${protectedNodes.length}⟧`;
          protectedNodes.push({ token, node, value: node.outerHTML });
          parts.push(token);
          return;
        }
        if (isExcluded(node)) {
          parts.push(' ');
          return;
        }
        if (node.tagName === 'BR') {
          nodes.push(node);
          parts.push('\n');
          return;
        }
        const atomic = isOpaque(node) || node.matches('ruby');
        if (!atomic && !isInline(node, childStyle)) {
          yield* flush();
          yield* walk(node);
        } else if (atomic) {
          nodes.push(node);
          if (node.tagName === 'RUBY') {
            parts.push([...textNodes(node)].map(part => part.nodeType === Node.TEXT_NODE ? part.data : ' ').join(''));
          } else {
            parts.push(node.textContent);
          }
        } else {
          for (const child of node.childNodes) yield* inline(child);
        }
      }
      for (const child of element.childNodes) {
        if (element.matches('details:not([open])') &&
          (child.nodeType !== Node.ELEMENT_NODE || child.tagName !== 'SUMMARY' ||
            child !== element.querySelector(':scope > summary'))) continue;
        if (layout && child.nodeType === Node.ELEMENT_NODE && !child.hasAttribute(MARK) && !isOpaque(child)) {
          yield* flush();
          yield* walk(child);
        }
        else yield* inline(child);
      }
      yield* flush();
    }
    yield* walk(root);
  }

  function discard(key) {
    const record = records.get(key);
    if (!record) return;
    record.output?.remove();
    const siblings = recordsByElement.get(record.element);
    siblings.delete(record);
    if (!siblings.size) {
      recordsByElement.delete(record.element);
      viewport.unobserve(record.element);
    }
    records.delete(key);
  }

  function shouldTranslate(text, element) {
    text = text.replace(/⟦B\d+⟧/g, '').trim();
    if (!/\p{L}/u.test(text) || /^@\S+$/.test(text) || /^(https?:\/\/|www\.)\S+$/i.test(text)) return false;
    if (element.closest('a')?.getAttribute('href')?.startsWith('#')) return false;
    if (/^[\w.+-]+@[\w.-]+\.[a-z]+$/i.test(text)) return false;
    if (!element.matches(HEADINGS) && (text.match(/\p{L}/gu) || []).length < 3) return false;
    return !isTargetScript(text, element);
  }

  let scanning;
  async function scan() {
    clearTimeout(timer);
    timer = undefined;
    if (!enabled || scanning === epoch) return;
    translateTitle();
    if (pageUrl !== location.href) {
      pageUrl = location.href;
      restart();
      return;
    }
    const roots = [...dirty].filter(root => root.isConnected &&
      ![...dirty].some(other => other !== root && other.contains(root)));
    dirty.clear();
    if (!roots.length) return;
    const generation = epoch;
    scanning = generation;
    const seen = new Set();
    let deadline = performance.now() + 8;
    for (const root of roots) {
      for (const entry of walkGroups(root)) {
        if (entry) {
          seen.add(entry[0]);
          observeGroup(...entry);
        }
        if (performance.now() >= deadline) {
          await new Promise(resolve => setTimeout(resolve, 0));
          if (generation !== epoch) return;
          deadline = performance.now() + 8;
        }
      }
    }
    for (const [key, record] of records) {
      if (!key.isConnected || !document.body.contains(record.element) || (roots.some(root => root.contains(record.element)) && !seen.has(key))) discard(key);
    }
    scanning = undefined;
    if (dirty.size) scheduleScan();
  }

  function observeGroup(key, group) {
    if (!key.isConnected) return;
    const { text, element } = group;
    if (!shouldTranslate(text, element)) {
      discard(key);
      return;
    }
    let record = records.get(key);
    if (!record || !matchesSource(record, group) ||
      (record.output && (!record.output.isConnected || record.output.previousSibling !== record.anchor))) {
      discard(key);
      record = { ...group, key, pending: false, output: null, retries: 0 };
      records.set(key, record);
      if (!recordsByElement.has(element)) recordsByElement.set(element, new Set());
      recordsByElement.get(element).add(record);
    }
    if (!record.pending) viewport.observe(element);
  }

  function scheduleScan() {
    if (timer === undefined) timer = setTimeout(scan, 150);
  }

  function isVisible(element, style = getComputedStyle(element)) {
    const font = style.fontFamily.split(',')[0].replace(/["']/g, '').trim().toLowerCase();
    if (/^(material icons|material symbols|google symbols|font awesome|fontawesome)(\s|$)/.test(font)) return false;
    return style.visibility !== 'hidden' && style.display !== 'none';
  }

  function matchesSource(record, current) {
    return current?.text === record.text && current.end === record.end &&
      current.element === record.element &&
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
    renderQueue.push([output, record]);
    if (renderTimer === undefined) renderTimer = requestAnimationFrame(flushRender);
  }

  function translationAnchor(record) {
    let anchor = record.end;
    while (anchor.parentElement && anchor.parentElement !== record.element &&
      anchor.parentElement.lastChild === anchor) anchor = anchor.parentElement;
    for (let parent = anchor.parentElement; parent; parent = parent.parentElement) {
      if (parent.matches(ATOMIC_CONTROL)) anchor = parent;
    }
    while (anchor.nextSibling) {
      const next = anchor.nextSibling;
      if (next.nodeType === Node.TEXT_NODE && !next.textContent.trim() ||
        next.nodeType === Node.ELEMENT_NODE && next.matches('img,picture')) {
        anchor = next;
      } else break;
    }
    return anchor;
  }

  function canInsertAfter(anchor, styleOf) {
    const parent = anchor.parentElement;
    if (!parent || parent.closest('select,datalist') || parent.matches(STRUCTURAL_PARENT)) return false;
    let container = parent;
    while (container && styleOf(container).display === 'contents') container = container.parentElement;
    // An inline span still becomes a layout item at this boundary.
    return Boolean(container && !container.matches(STRUCTURAL_PARENT) &&
      !/flex|grid|table-(?:row|header|footer|column)/.test(styleOf(container).display));
  }

  function findInsertionAnchor(record, groups, styleOf) {
    const anchor = translationAnchor(record);
    if (!anchor.isConnected) return null;
    if (canInsertAfter(anchor, styleOf)) return anchor;

    const { element, key } = record;
    // Move a single complete text group past its own layout boundary.
    if (element.matches(`${HEADINGS},p`) && element.contains(anchor) &&
      !element.closest(INTERACTIVE_REGION) &&
      [...groups].every(([groupKey, group]) => groupKey === key || !group.text) &&
      canInsertAfter(element, styleOf)) return element;
    return null;
  }

  function styleTranslation(anchor, output, record, styleOf) {
    const { element, text } = record;
    const sourceStyle = styleOf(element);
    const outside = anchor === element && element.matches(`${HEADINGS},p`);
    const flow = styleOf(anchor.parentElement);
    const short = !text.includes('\n') && text.length <= 24 && text.split(/\s+/u).length <= 4;
    const inline = !outside && (isInline(anchor.parentElement, flow) ||
      (!element.matches(HEADINGS) && (element.matches(FORCE_INLINE_TRANSLATION) ||
        (short && sourceStyle.display !== 'contents') || isInline(element, sourceStyle))));
    Object.assign(output.style, {
      color: 'inherit',
      fontFamily: 'inherit',
      fontWeight: 'inherit',
      lineHeight: Number.parseFloat(flow.lineHeight) === 0 ? 'normal' : 'inherit',
      whiteSpace: 'normal',
      overflowWrap: 'anywhere',
      wordBreak: 'normal',
      unicodeBidi: 'isolate',
      userSelect: 'text',
    });
    if (inline) {
      output.style.display = 'inline';
      output.prepend(document.createTextNode('\u00a0\u00a0'));
    } else {
      output.style.display = 'block';
      output.style.marginBlock = '0.5em';
      if (outside) {
        const { color, fontFamily, fontSize, fontWeight, lineHeight } = getComputedStyle(record.element);
        Object.assign(output.style, { color, fontFamily, fontSize, fontWeight,
          lineHeight: Number.parseFloat(lineHeight) === 0 ? 'normal' : lineHeight });
      }
    }
  }

  function flushRender() {
    renderTimer = undefined;
    const styles = new WeakMap();
    const sources = new WeakMap();
    const styleOf = element => {
      if (!styles.has(element)) {
        const style = getComputedStyle(element);
        styles.set(element, {
          display: style.display, lineHeight: style.lineHeight, float: style.float,
        });
      }
      return styles.get(element);
    };
    const ready = [];
    for (const [output, record] of renderQueue.splice(0)) {
      const { key, element } = record;
      if (!key.isConnected || !document.body.contains(element) || records.get(key) !== record || record.output) continue;
      if (!sources.has(element)) sources.set(element, collect(element));
      const groups = sources.get(element);
      const source = groups.get(key);
      if (!matchesSource(record, source)) {
        discard(key);
        dirty.add(element);
        scheduleScan();
        continue;
      }
      const anchor = findInsertionAnchor(record, groups, styleOf);
      if (!anchor) continue;
      styleTranslation(anchor, output, record, styleOf);
      ready.push([anchor, output, record]);
    }
    for (const [anchor, output, record] of ready) {
      anchor.after(output);
      record.output = output;
      record.anchor = anchor;
    }
  }

  function pump() {
    if (!enabled || active >= limit || !queue.length) return;
    if (Date.now() < resumeAt) {
      if (resumeTimer === undefined) {
        resumeTimer = setTimeout(() => {
          resumeTimer = undefined;
          pump();
        }, Math.min(resumeAt - Date.now(), 2147483647));
      }
      return;
    }
    const distances = new WeakMap();
    const height = innerHeight;
    queue = queue.filter(([key, record]) => {
      if (records.get(key) !== record || !key.isConnected) return false;
      const element = record.element;
      if (!distances.has(element)) {
        const rect = element.getBoundingClientRect();
        distances.set(element, Math.max(0, -rect.bottom, rect.top - height));
      }
      const distance = distances.get(element);
      if (distance <= PRELOAD) {
        return true;
      }
      record.pending = false;
      viewport.observe(record.element);
      return false;
    });
    queue.sort((a, b) => distances.get(a[1].element) - distances.get(b[1].element));
    while (enabled && active < limit && queue.length) {
      const first = queue.shift();
      if (records.get(first[0]) !== first[1] || !first[0].isConnected) continue;
      const jobs = [first];
      let characters = first[1].text.length;
      while (provider === 'microsoft' && !first[1].single && jobs.length < 6 && queue.length && characters < 3000) {
        const next = queue[0];
        if (next[1].single || characters + next[1].text.length > 3000 || next[1].text.length > 1800) break;
        jobs.push(queue.shift());
        characters += next[1].text.length;
      }
      const activeJobs = jobs.filter(([element, record]) => records.get(element) === record && element.isConnected);
      if (!activeJobs.length) continue;
      const generation = epoch;
      const service = provider;
      const language = target;
      active++;
      translateMany(activeJobs.map(([, record]) => record.text), service, language, generation).then(results => {
        if (generation !== epoch) return;
        const errors = new Set(results.filter(result => result.status === 'rejected').map(result => result.reason));
        const rateLimit = [...errors].find(error => error.status === 429);
        timeouts += [...errors].filter(error => error.timeout).length;
        if (generation === epoch && (rateLimit || timeouts >= 2)) {
          limit = Math.max(1, Math.floor(limit / 2));
          successes = 0;
          timeouts = 0;
          resumeAt = Math.max(resumeAt, Date.now() + Math.max(rateLimit?.delay || 0, 2000));
        }
        for (const [[element, record], outcome] of activeJobs.map((job, index) => [job, results[index]])) {
          if (generation !== epoch || records.get(element) !== record || !element.isConnected) continue;
          if (outcome.status === 'rejected') {
            const error = outcome.reason;
            if (error.single) {
              record.single = true;
              queue.push([element, record]);
            } else if (error.status === 429 && record.retries++ < 2) {
              queue.push([element, record]);
            } else if ((error.network || error.timeout || error.status >= 500) && record.retries++ < 2) {
              const retryTimer = setTimeout(() => {
                retryTimers.delete(retryTimer);
                if (generation !== epoch || records.get(element) !== record) return;
                queue.push([element, record]);
                pump();
              }, 1000 * 2 ** record.retries);
              retryTimers.add(retryTimer);
            }
            continue;
          }
          const result = outcome.value;
          timeouts = 0;
          if (++successes >= 12) { limit = Math.min(concurrency, limit + 1); successes = 0; }
          if (!result.sameLanguage && result.text.trim() !== record.text) {
            try { render(record, result.text); }
            catch (error) { console.warn('[双语]', error.message); }
          }
        }
        for (const error of errors) console.warn('[双语]', error.message);
      }).catch((error) => {
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
      for (const record of recordsByElement.get(entry.target) ?? []) {
        if (record.pending || !record.key.isConnected) continue;
        record.pending = true;
        queue.push([record.key, record]);
      }
      viewport.unobserve(entry.target);
    }
    pump();
  }, { rootMargin: `${PRELOAD}px` });

  function affectedRoot(element) {
    if (!document.body.contains(element)) return null;
    while (element !== document.body) {
      if (!isOpaque(element) && !isInline(element, getComputedStyle(element))) break;
      element = element.parentElement;
    }
    return element;
  }

  const observer = new MutationObserver(mutations => {
    let changed = false;
    for (const mutation of mutations) {
      const element = mutation.target.nodeType === Node.ELEMENT_NODE ? mutation.target : mutation.target.parentElement;
      if (!element || element.closest(`[${MARK}]`)) continue;
      if (element === document.head || element.closest('title')) {
        changed = true;
        continue;
      }
      if (mutation.type === 'childList' && [...mutation.addedNodes, ...mutation.removedNodes].every(node =>
        node.nodeType === Node.ELEMENT_NODE && node.hasAttribute(MARK))) continue;
      const root = affectedRoot(element);
      if (root) dirty.add(root);
      changed = true;
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
    titlePending = undefined;
    if (titleState.translated && document.title === titleState.translated) document.title = titleState.source;
    titleState = { url: location.href, source: '', translated: '' };
    clearTimeout(timer);
    timer = undefined;
    cancelAnimationFrame(renderTimer);
    renderTimer = undefined;
    renderQueue = [];
    observer.disconnect();
    viewport.disconnect();
    queue = [];
    for (const handle of requests) handle.abort();
    requests.clear();
    pending.clear();
    dirty.clear();
    clearTimeout(resumeTimer);
    resumeTimer = undefined;
    for (const retryTimer of retryTimers) clearTimeout(retryTimer);
    retryTimers.clear();
    resumeAt = 0;
    limit = concurrency;
    successes = timeouts = 0;
    for (const record of records.values()) record.output?.remove();
    records.clear();
    recordsByElement.clear();
  }

  function start() {
    if (enabled) return;
    enabled = true;
    observer.observe(document.body, {
      childList: true, subtree: true, characterData: true, attributes: true,
      attributeFilter: ['open', 'hidden', 'class', 'style', 'lang', 'contenteditable'],
    });
    observer.observe(document.head, { childList: true, subtree: true, characterData: true });
    dirty.add(document.body);
    scan();
  }

  for (const method of ['pushState', 'replaceState']) {
    const original = history[method];
    history[method] = function (...args) {
      const result = original.apply(this, args);
      if (location.href !== pageUrl) {
        pageUrl = location.href;
        restart();
      }
      return result;
    };
  }
  addEventListener('popstate', () => {
    if (location.href !== pageUrl) {
      pageUrl = location.href;
      restart();
    }
  });

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
