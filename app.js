pdfjsLib.GlobalWorkerOptions.workerSrc = 'https://cdnjs.cloudflare.com/ajax/libs/pdf.js/3.11.174/pdf.worker.min.js';

/* ═══════════════════════════════════════════════
   STATE
═══════════════════════════════════════════════ */
let pdf = null, nPages = 0, curPg = 1, zoom = 1;
// Bumped every time a new document is parsed (fresh load or a tab switch).
// Async pipelines that read `pdf`/write shared globals after an `await`
// capture this at the start and bail out if it's changed underneath them —
// otherwise a slow-finishing call from a document the user has since
// switched away from can write its results into the wrong tab's state.
let docGen = 0;
let pdfBytes = null, pdfName = '';
let pendingDropFile = null;
const selectedPages = new Set(); // pages selected in the thumbnail panel
let lastClickedPage = null;      // anchor for shift-click range selection
let tool = 'pan', Color = 'yellow';
let fontSize = 12;
let annotOpacity = 80;
let lineStyle = 'solid'; // 'solid' | 'dashed' | 'dotted' — applies to line/arrow/rect/circle
let textBoxDefault = true; // whether new text annotations get a border/background box
let textAlignDefault = 'center'; // 'left' | 'center' | 'right' — horizontal justification for new note/text annots
let vAlignDefault = 'center';    // 'top' | 'center' | 'bottom' — vertical justification for new note/text annots
let _spTargetAnnotId = null; // set while the style popover is editing one specific annotation (right-click → Style), vs the global "next annotation" style
let annots = [];
let mergeFiles = [];
let annotIdSeq = 0;

// Status lifecycle — defined early, used in updateAnnotPanel and buildAnnotEl
const STATUS_CYCLE = ['open','progress','resolved','rejected'];
const STATUS_LABEL = { open:'Open', progress:'In Progress', resolved:'Resolved', rejected:'Rejected' };

// Page source labels — set when multiple PDFs are merged, maps pageNum→filename
const pageLabels = {}; // { 1: 'DrawingA.pdf', 2: 'DrawingA.pdf', 3: 'DrawingB.pdf', ... }

// Author
let currentAuthor = localStorage.getItem('engdoc_author') || '';

function saveAuthor() {
  const val = document.getElementById('author-input').value.trim();
  if (!val) { toast('Please enter a name'); return; }
  currentAuthor = val;
  localStorage.setItem('engdoc_author', val);
  // Update both the hidden compat span and the ribbon File tab button
  const hdr = document.getElementById('hdr-author');
  if (hdr) hdr.textContent = val;
  const hdrR = document.getElementById('hdr-author-r');
  if (hdrR) hdrR.textContent = val;
  closeM('mau');
  toast(`Name set to "${val}"`);
}

function initAuthor() {
  if (currentAuthor) {
    document.getElementById('hdr-author').textContent = currentAuthor;
    document.getElementById('author-input').value = currentAuthor;
  } else {
    // Prompt on first use — open modal automatically
    openM('mau');
    setTimeout(() => document.getElementById('author-input').focus(), 100);
  }
}

// drawing state
let drawing = false, penPoints = [], origin = null, liveEl = null, liveSvg = null;
let ctxAnnotId = null;

// virtual rendering
// stores per-page metadata for lazy rendering
const pageViewports = {};    // pageNum -> {width, height} at current zoom
const renderedPages = new Set();
const renderQueue = new Set();
let renderScheduled = false;
const OVERSCAN = 2; // extra pages above/below viewport to pre-render

const CVals = { yellow: 'rgba(251,191,36,.38)', green: 'rgba(56,247,31,.32)', red: 'rgba(250,25,59,.36)', blue: 'rgba(37,99,235,.32)', black: 'rgba(0,0,0,.35)', teal: 'rgba(45,212,191,.32)', rose: 'rgba(251,113,133,.36)' };
const CHex  = { yellow: '#fbbf24', green: '#38f71f', red: '#fa193b', blue: '#2563eb', black: '#000000', teal: '#2dd4bf', rose: '#fb7185' };

// ── Colour resolution — supports both named presets (above) and
//    arbitrary custom hex strings stored directly as an annotation's Color ──
function isHexColor(s) { return typeof s === 'string' && /^#[0-9a-f]{6}$/i.test(s); }
function colorHex(name, fallback = 'yellow') {
  if (isHexColor(name)) return name;
  if (CHex[name]) return CHex[name];
  return isHexColor(fallback) ? fallback : (CHex[fallback] || CHex.yellow);
}
function colorRgba(name, alpha = 0.35) {
  if (isHexColor(name)) {
    const r = parseInt(name.slice(1,3),16), g = parseInt(name.slice(3,5),16), b = parseInt(name.slice(5,7),16);
    return `rgba(${r},${g},${b},${alpha})`;
  }
  return CVals[name] || CVals.yellow;
}
// Pale tint of a hex colour (mix toward white) — used for light annotation fills
function tintHex(hex, amount = 0.85) {
  const r = parseInt(hex.slice(1,3),16), g = parseInt(hex.slice(3,5),16), b = parseInt(hex.slice(5,7),16);
  const mix = (c) => Math.round(c + (255 - c) * amount).toString(16).padStart(2,'0');
  return `#${mix(r)}${mix(g)}${mix(b)}`;
}
// Justification for note/text annotations — CSS values for horizontal (text-align)
// and vertical (flex justify-content) alignment, defaulting to center/center.
function hAlignCss(a) { return { left:'left', center:'center', right:'right' }[a] || 'center'; }
function vAlignCss(a) { return { top:'flex-start', center:'center', bottom:'flex-end' }[a] || 'center'; }

// SVG stroke-dasharray for a line style, scaled to the stroke width
const LINE_DASH = { dashed: [2.5, 1.6], dotted: [0.3, 1.4] };
function dashArrayFor(style, sw) {
  const pat = LINE_DASH[style];
  if (!pat) return null;
  const s = Math.max(1, sw || 2);
  return pat.map(v => (v * s).toFixed(1)).join(',');
}
const typeLabels = { highlight:'Highlight', rect:'Rectangle', strike:'Strikethrough',
  pen:'Freehand', arrow:'Arrow', text:'Text Label',
  texthighlight:'Text Highlight', cloud:'Cloud', measure:'Measure', area:'Area',
  line:'Line', rectfill:'Fill Box',
  pan:'Pan', select:'Select Text', zoombox:'Zoom', erase:'Erase' };

// ── HISTORY/UNDO stubs — full implementation below in ANNOTATION DATA MANAGEMENT ──

// Measure scale: pxPerUnit = screen pixels per real-world unit at zoom=1
let measureScale = null; // { pxPerUnit, unit } — null = uncalibrated
let lastMeasurePx = null; // screen px length of last calibration line

// Measure click-click-drag state machine
// 'idle' → click p1 → 'firstSet' → click p2 → 'secondSet' → drag label → commit
let measureState = 'idle';
let measureP1 = null;   // {x, y} in overlay pixels on page
let measureP2 = null;
let measurePageNum = null;
let measureVp = null;   // viewport at time of measurement
let measureLiveSvg = null; // persistent SVG on overlay during 2-click flow

// PDF text content cache — { pageNum: [{str, x, y, w, h, fontSize}] }
const pdfTextContent  = {};  // { pageNum: string } — for standards checker
const _pageTextItems  = {};  // { pageNum: [{str,x,y,w,h,angle}] } — for select tool
const _pageVectorGeom = {};  // { pageNum: {points:[{x,y}], segments:[{x1,y1,x2,y2}], grid:Map, cell} } — for snap-to-drawing

function nextId() { return ++annotIdSeq; }

// Text input popover state
let txtPopCallback = null;

function showTxtPop(screenX, screenY, cb, initialVal = '', emmaData = null) {
  txtPopCallback = cb;
  const pop = document.getElementById('txt-pop');
  const ta  = document.getElementById('txt-pop-input');
  const btn = pop.querySelector('.hbtn.primary');
  ta.value = initialVal;
  btn.textContent = initialVal ? 'Save' : 'Add';
  // Reset EMMA fields
  document.getElementById('pop-discipline').value = emmaData?.discipline || '';
  document.getElementById('pop-priority').value   = emmaData?.priority   || '';
  document.getElementById('pop-gridref').value    = emmaData?.gridRef    || '';
  document.getElementById('pop-action').value     = emmaData?.action     || '';
  // EMMA include checkbox — excluded if emmaExclude is explicitly true
  document.getElementById('pop-emma-include').checked = !(emmaData?.emmaExclude === true);
  // Show EMMA fields if editing an annotation that has them
  const hasEmma = emmaData && (emmaData.discipline || emmaData.priority || emmaData.gridRef || emmaData.action);
  document.getElementById('emma-fields').style.display = hasEmma ? 'block' : 'none';
  document.getElementById('emma-toggle-btn').textContent = hasEmma ? '− EMMA fields' : '+ EMMA fields';
  // Style controls — colour / font size / opacity, pre-filled from the
  // annotation being edited (or the current default style when adding new)
  txtPopSetColor(emmaData?.Color ?? Color);
  const startHex = emmaData?.Color ?? Color;
  document.getElementById('txtpop-hex').value = isHexColor(startHex) ? startHex : '#fbbf24';
  document.getElementById('txtpop-font').value = emmaData?.fontSize ?? fontSize;
  document.getElementById('txtpop-opacity').value = emmaData?.opacity ?? 100;
  pop.classList.add('open');
  const pw = 300, ph = 190;
  const vw = window.innerWidth, vh = window.innerHeight;
  pop.style.left = Math.min(screenX, vw - pw - 12) + 'px';
  pop.style.top  = Math.min(screenY + 8, vh - ph - 12) + 'px';
  requestAnimationFrame(() => { ta.focus(); ta.select(); });
}
let _txtPopColor = 'yellow';
function txtPopSetColor(c) {
  _txtPopColor = c;
  document.querySelectorAll('#txtpop-swatches .rcsw').forEach(s => s.classList.toggle('active', s.dataset.c === c));
}
function toggleEmmaFields() {
  const el = document.getElementById('emma-fields');
  const btn = document.getElementById('emma-toggle-btn');
  const visible = el.style.display !== 'none';
  el.style.display = visible ? 'none' : 'block';
  btn.textContent = visible ? '+ EMMA fields' : '− EMMA fields';
}
function txtPopConfirm() {
  const val = document.getElementById('txt-pop-input').value.trim();
  document.getElementById('txt-pop').classList.remove('open');
  if (val && txtPopCallback) {
    const emmaFields = {
      discipline:  document.getElementById('pop-discipline').value,
      priority:    document.getElementById('pop-priority').value,
      gridRef:     document.getElementById('pop-gridref').value.trim(),
      action:      document.getElementById('pop-action').value.trim(),
      emmaExclude: !document.getElementById('pop-emma-include').checked,
      Color:       _txtPopColor,
      fontSize:    parseInt(document.getElementById('txtpop-font').value) || 12,
      opacity:     parseInt(document.getElementById('txtpop-opacity').value) || 100,
    };
    txtPopCallback(val, emmaFields);
  }
  txtPopCallback = null;
}
function txtPopCancel() {
  document.getElementById('txt-pop').classList.remove('open');
  txtPopCallback = null;
}
// Enter to confirm (Shift+Enter = newline)
document.getElementById('txt-pop-input').addEventListener('keydown', e => {
  if (e.key === 'Enter' && !e.shiftKey) { e.preventDefault(); txtPopConfirm(); }
  if (e.key === 'Escape') { e.preventDefault(); txtPopCancel(); }
});
document.getElementById('author-input').addEventListener('keydown', e => {
  if (e.key === 'Enter') { e.preventDefault(); saveAuthor(); }
});

// Pan-drag scroll state
let panDragging = false, panStart = null, panScrollStart = null;

/* ═══════════════════════════════════════════════
   UI HELPERS
═══════════════════════════════════════════════ */
function toast(m, ms = 2600) {
  const el = document.getElementById('toast');
  el.textContent = m; el.classList.add('show');
  setTimeout(() => el.classList.remove('show'), ms);
}
function openM(id)  { document.getElementById(id).classList.add('open'); }
function closeM(id) { document.getElementById(id).classList.remove('open'); }
function hideCtx()  { document.getElementById('ctx-menu').classList.remove('open'); }
function hideQuickToolbar() { document.getElementById('ctx-quickbar').classList.remove('open'); }

/* ═══════════════════════════════════════════════
   FILE OPEN
═══════════════════════════════════════════════ */
async function openFile(e) {
  const f = e.target.files[0]; if (!f) return;
  e.target.value = '';
  if (f.name.toLowerCase().endsWith('.engdoc')) {
    // Sessions without an embedded PDF restore annotations onto whatever
    // document is already open — not a "new document" action — so this
    // stays a same-tab operation, unlike opening a plain PDF below.
    await loadSession({ target: { files: [f], value: '' } });
  } else {
    await openFileAsNewTab(f); // works whether this is tab 1 or an additional tab
  }
}
function onDragOver(e) { e.preventDefault(); document.getElementById('drop-card').classList.add('drag-over'); }
async function onDrop(e) {
  e.preventDefault(); document.getElementById('drop-card').classList.remove('drag-over');
  const files = Array.from(e.dataTransfer.files);
  if (!files.length) return;

  const pdfs    = files.filter(f => f.type === 'application/pdf' || f.name.toLowerCase().endsWith('.pdf'));
  const engdocs = files.filter(f => f.name.toLowerCase().endsWith('.engdoc'));

  if (engdocs.length) {
    // Load the first .engdoc (ignore others)
    loadSession({ target: { files: [engdocs[0]], value: '' } });
  } else if (pdfs.length === 1) {
    if (pdf !== null) {
      pendingDropFile = pdfs[0];
      document.getElementById('mpdf-drop-name').textContent = pdfs[0].name;
      document.getElementById('mpdf-drop-curpg').textContent = curPg;
      openM('mpdf-drop');
    } else {
      openFileAsNewTab(pdfs[0]); // no tabs open yet — this becomes tab 1
    }
  } else if (pdfs.length > 1) {
    loadMultiplePDFs(pdfs);
  }
}

async function loadPDF(file) {
  pdfName = file.name;
  pdfBytes = await file.arrayBuffer();
  // "Brand new document" reset — identity/annotation state that only makes
  // sense to wipe when we're not just switching back to a previously-open
  // tab (see switchTab, which restores these from the tab record instead).
  curPg = 1; annots = []; emmaRows = {};
  Object.keys(pageLabels).forEach(k => delete pageLabels[k]);
  history = []; historyIdx = -1; updateUndoRedoButtons();

  await parseAndRenderPdfBytes(pdfBytes);
  toast(`Opened: ${file.name} — ${nPages} page${nPages !== 1 ? 's' : ''}`);
}

// Parses PDF bytes into `pdf` and rebuilds everything derived from it —
// shared by loadPDF (brand-new document) and switchTab (returning to an
// already-open tab). Deliberately does NOT touch annots/emmaRows/history/
// pageLabels — those are the caller's responsibility, since the two call
// sites need opposite behaviour for them (reset vs. restore).
async function parseAndRenderPdfBytes(bytes) {
  if (pdf) { try { await pdf.destroy(); } catch (e) { /* already torn down */ } }
  docGen++;

  pdf = await pdfjsLib.getDocument({
    data: bytes.slice(0),
    // Streaming + range requests disabled (we have full bytes in memory)
    disableRange: true,
    disableStream: true,
    // Suppress console noise
    verbosityLevel: 0,
    // Larger chunk size speeds up internal page parsing
    rangeChunkSize: 65536,
    // Use canvas for all rendering (no SVG fallback)
    useSystemFonts: false,
  }).promise;
  nPages = pdf.numPages;
  renderedPages.clear(); renderQueue.clear();
  Object.keys(pdfTextContent).forEach(k => delete pdfTextContent[k]);
  Object.keys(_pageTextItems).forEach(k => delete _pageTextItems[k]);
  if (window._pageRawText) Object.keys(window._pageRawText).forEach(k => delete window._pageRawText[k]);
  Object.keys(_pageCache).forEach(k => delete _pageCache[k]); // stale page proxies from the previous doc must not leak in under the same page-number keys

  document.getElementById('doc-name').textContent = pdfName;
  document.getElementById('pgt').textContent = nPages;
  document.getElementById('pgi').max = nPages;
  document.getElementById('spc').textContent = nPages;
  document.getElementById('drop-landing').classList.add('hidden');
  document.getElementById('hdr-page-nav').classList.add('active');

  await buildPageShells();
  await buildThumbs();
  try { syncAnnots(); } catch (e) { console.error('[ENGDOC] syncAnnots failed:', e); }
  updateAnnotPanel();
  scheduleRender();

  // Extract text in background — don't block rendering
  extractPdfText().then(() => autoDetectTitleBlock());
}

/* ═══════════════════════════════════════════════
   TABS
   Only the active tab has a live, parsed pdf.js
   document — inactive tabs hold their raw bytes plus
   JS-side state (annotations, undo history, etc.) and
   get re-parsed via parseAndRenderPdfBytes() when
   switched to. This keeps memory bounded to one open
   document regardless of tab count, at the cost of a
   re-parse per switch — a deliberate trade-off for
   users who expect several tabs open at once.
═══════════════════════════════════════════════ */
let tabs = [];
let activeTabId = null;
let tabIdSeq = 0;

// Everything that represents "this document's state" and would look wrong
// or stale in the UI after switching away and back if not captured here.
function saveActiveTabState() {
  const rec = tabs.find(t => t.id === activeTabId);
  if (!rec) return;
  Object.assign(rec, {
    name: pdfName, bytes: pdfBytes, nPages,
    annots, emmaRows, annotIdSeq,
    pageLabels: { ...pageLabels },
    history, historyIdx,
    zoom, curPg,
    measureScale, lastMeasurePx,
    selectedPages: [...selectedPages], lastClickedPage,
    fileHandle: _fileHandle, loadedEngdocName: _loadedEngdocName,
    checkFindings, pdfLayers: _pdfLayers,
    searchIndex, searchPersistHits: _searchPersistHits,
    annotNavIdx: _annotNavIdx,
    emmaFields: captureEmmaFields(),
  });
}

// Inverse of saveActiveTabState — writes a tab record's fields back into
// the live globals. Does NOT re-parse the PDF or touch the DOM; the caller
// (switchTab) follows this with parseAndRenderPdfBytes(bytes).
function restoreTabState(rec) {
  pdfName = rec.name; pdfBytes = rec.bytes;
  annots = rec.annots; emmaRows = rec.emmaRows; annotIdSeq = rec.annotIdSeq;
  Object.keys(pageLabels).forEach(k => delete pageLabels[k]);
  Object.assign(pageLabels, rec.pageLabels);
  history = rec.history; historyIdx = rec.historyIdx;
  zoom = rec.zoom; curPg = rec.curPg;
  measureScale = rec.measureScale; lastMeasurePx = rec.lastMeasurePx;
  selectedPages.clear(); rec.selectedPages.forEach(p => selectedPages.add(p));
  lastClickedPage = rec.lastClickedPage;
  _fileHandle = rec.fileHandle; _loadedEngdocName = rec.loadedEngdocName;
  checkFindings = rec.checkFindings || [];
  _pdfLayers = rec.pdfLayers || [];
  searchIndex = rec.searchIndex || [];
  _searchPersistHits = rec.searchPersistHits || [];
  _annotNavIdx = rec.annotNavIdx ?? -1;

  Object.entries(rec.emmaFields || {}).forEach(([id, val]) => {
    const el = document.getElementById(id);
    if (el) el.value = val;
  });
  updateUndoRedoButtons();
  renderCheckResults(checkFindings);
  updateLayerPanel();
  clearSearchHighlights();
  updateEmmaRegister();
}

// Discards any in-progress gesture (draw/measure/select/move) before a tab
// switch — resuming a gesture against a different document's coordinate
// space is meaningless, so these are abandoned rather than carried over.
function cancelActiveGestures() {
  if (liveEl) { liveEl.remove(); liveEl = null; }
  if (liveSvg) { liveSvg.remove(); liveSvg = null; }
  drawing = false; penPoints = []; origin = null;
  measureState = 'idle'; measureP1 = null; measureP2 = null; measurePageNum = null; measureVp = null;
  if (measureLiveSvg) { measureLiveSvg.remove(); measureLiveSvg = null; }
  clearComparison();
}

async function switchDocTab(tabId) {
  if (tabId === activeTabId) return;
  const target = tabs.find(t => t.id === tabId);
  if (!target) return;

  cancelActiveGestures();
  saveActiveTabState();
  activeTabId = tabId;
  restoreTabState(target);
  await parseAndRenderPdfBytes(target.bytes);
  renderTabBar();
}

async function openFileAsNewTab(file) {
  const id = ++tabIdSeq;
  tabs.push({
    id, name: file.name, bytes: null, nPages: 0,
    annots: [], emmaRows: {}, annotIdSeq: 0, pageLabels: {},
    history: [], historyIdx: -1,
    zoom: 1, curPg: 1,
    measureScale: null, lastMeasurePx: null,
    selectedPages: [], lastClickedPage: null,
    fileHandle: null, loadedEngdocName: null,
    checkFindings: [], pdfLayers: [],
    searchIndex: [], searchPersistHits: [],
    annotNavIdx: -1, emmaFields: {},
  });
  cancelActiveGestures();
  if (activeTabId != null) saveActiveTabState();
  activeTabId = id;
  zoom = 1; // a new tab is an unrelated document — don't inherit whichever zoom the previous tab happened to be at
  await loadPDF(file); // brand-new document — correct reset semantics, unchanged
  saveActiveTabState(); // snapshot the freshly-loaded doc's derived fields (nPages, etc.) into the new record
  renderTabBar();
}

async function closeTab(tabId) {
  const idx = tabs.findIndex(t => t.id === tabId);
  if (idx === -1) return;
  const wasActive = tabId === activeTabId;
  tabs.splice(idx, 1);

  if (wasActive) {
    if (tabs.length) {
      const next = tabs[Math.min(idx, tabs.length - 1)];
      activeTabId = next.id;
      restoreTabState(next);
      await parseAndRenderPdfBytes(next.bytes);
    } else {
      await resetToEmptyState();
    }
  }
  renderTabBar();
}

// Reverses everything parseAndRenderPdfBytes/loadPDF set up, back to the
// app's pre-load state — used when the last tab is closed.
async function resetToEmptyState() {
  cancelActiveGestures();
  if (pdf) { try { await pdf.destroy(); } catch (e) {} }
  docGen++;
  pdf = null; nPages = 0; curPg = 1; annots = []; emmaRows = {}; annotIdSeq = 0;
  Object.keys(pageLabels).forEach(k => delete pageLabels[k]);
  history = []; historyIdx = -1; updateUndoRedoButtons();
  renderedPages.clear(); renderQueue.clear();
  Object.keys(pdfTextContent).forEach(k => delete pdfTextContent[k]);
  Object.keys(_pageTextItems).forEach(k => delete _pageTextItems[k]);
  if (window._pageRawText) Object.keys(window._pageRawText).forEach(k => delete window._pageRawText[k]);
  Object.keys(_pageCache).forEach(k => delete _pageCache[k]);
  selectedPages.clear(); lastClickedPage = null;
  measureScale = null; lastMeasurePx = null;
  _fileHandle = null; _loadedEngdocName = null;
  checkFindings = []; renderCheckResults(checkFindings);
  _pdfLayers = []; updateLayerPanel();
  searchIndex = []; clearSearchHighlights();
  _annotNavIdx = -1;
  updateEmmaRegister();
  activeTabId = null; pdfName = ''; pdfBytes = null;

  document.getElementById('doc-name').textContent = 'No document open';
  document.getElementById('drop-landing').classList.remove('hidden');
  document.getElementById('hdr-page-nav').classList.remove('active');
  document.getElementById('pdfpages').innerHTML = '';
  const thumbs = document.getElementById('sp-pages');
  if (thumbs) thumbs.innerHTML = '';
}

function renderTabBar() {
  const bar = document.getElementById('tab-bar');
  if (!bar) return;
  if (!tabs.length) { bar.style.display = 'none'; return; }
  bar.style.display = 'flex';
  bar.innerHTML = tabs.map(t => `
    <div class="tab-pill${t.id === activeTabId ? ' active' : ''}" onclick="switchDocTab(${t.id})" title="${escapeHtmlAttr(t.name)}">
      <span class="tab-pill-name">${escapeHtmlAttr(t.name.length > 24 ? t.name.slice(0, 22) + '…' : t.name)}</span>
      <button class="tab-pill-close" onclick="event.stopPropagation(); closeTab(${t.id})" title="Close tab">✕</button>
    </div>`).join('') +
    `<button class="tab-add-btn" onclick="document.getElementById('fopen-tab').click()" title="Open another PDF in a new tab">+</button>`;
}

function escapeHtmlAttr(s) {
  return String(s).replace(/&/g, '&amp;').replace(/"/g, '&quot;').replace(/</g, '&lt;');
}

async function openFileInNewTabFromInput(e) {
  const f = e.target.files[0]; if (!f) return;
  e.target.value = '';
  await openFileAsNewTab(f);
}

/* ═══════════════════════════════════════════════
   MULTI-PDF COLLATION
   Drag in multiple PDFs — they are merged in drop
   order. Each page is labelled with its source
   filename in the Pages panel.
═══════════════════════════════════════════════ */
async function loadMultiplePDFs(files) {
  if (!files.length) return;

  // If no tab is open yet, this collated document becomes tab 1 — same
  // bookkeeping as openFileAsNewTab, just without a single file to hand off
  // to loadPDF yet (that happens once the merge below finishes).
  if (activeTabId == null) {
    const id = ++tabIdSeq;
    tabs.push({
      id, name: files[0].name, bytes: null, nPages: 0,
      annots: [], emmaRows: {}, annotIdSeq: 0, pageLabels: {},
      history: [], historyIdx: -1,
      zoom: 1, curPg: 1,
      measureScale: null, lastMeasurePx: null,
      selectedPages: [], lastClickedPage: null,
      fileHandle: null, loadedEngdocName: null,
      checkFindings: [], pdfLayers: [],
      searchIndex: [], searchPersistHits: [],
      annotNavIdx: -1, emmaFields: {},
    });
    activeTabId = id;
  }

  // Sort alphabetically by filename so pages always appear A→Z regardless of drop order
  const sortedFiles = [...files].sort((a, b) =>
    a.name.toLowerCase().localeCompare(b.name.toLowerCase())
  );

  toast('Merging ' + sortedFiles.length + ' PDFs\u2026', 3000);

  try {
    await loadPdfLib();
    const { PDFDocument } = PDFLib;
    const merged = await PDFDocument.create();

    // Clear page labels ready for new set
    Object.keys(pageLabels).forEach(k => delete pageLabels[k]);

    let pageOffset = 0;
    const firstName = sortedFiles[0].name;

    for (const file of sortedFiles) {
      const bytes = await file.arrayBuffer();
      const src   = await PDFDocument.load(bytes, { ignoreEncryption: true });
      const pages = await merged.copyPages(src, src.getPageIndices());
      pages.forEach(p => {
        merged.addPage(p);
        pageOffset++;
        pageLabels[pageOffset] = file.name.replace(/\.pdf$/i, '');
      });
    }

    // Serialise merged PDF and load it
    const mergedBytes = await merged.save();
    const mergedFile  = new File(
      [mergedBytes],
      firstName.replace(/\.pdf$/i, '') + '_merged.pdf',
      { type: 'application/pdf' }
    );

    await loadPDF(mergedFile);

    // Re-apply labels (loadPDF cleared them)
    // We stored labels before loadPDF, so restore from our local copy
    // Actually: rebuild from files list since loadPDF clears pageLabels
    let pg = 0;
    for (const file of sortedFiles) {
      const src = await PDFDocument.load(await file.arrayBuffer(), { ignoreEncryption: true });
      for (let i = 0; i < src.getPageCount(); i++) {
        pg++;
        pageLabels[pg] = file.name.replace(/\.pdf$/i, '');
      }
    }

    // Rebuild thumbs with labels now set
    buildThumbs();
    saveActiveTabState(); // keep the tab pill's name/bytes in sync with this merge
    renderTabBar();
    toast('\u2713 Merged ' + sortedFiles.length + ' PDFs \u2014 ' + nPages + ' pages total', 3000);
  } catch(e) {
    toast('Merge failed: ' + e.message);
    console.error('[EngDoc] loadMultiplePDFs:', e);
  }
}

/* ═══════════════════════════════════════════════
   PDF INSERT / DROP CHOICE
   Insert a new PDF into the current document
   (append at end, or merge after current page).
═══════════════════════════════════════════════ */
function handleDropChoice(mode) {
  closeM('mpdf-drop');
  if (!pendingDropFile) return;
  const file = pendingDropFile;
  pendingDropFile = null;
  if (mode === 'open') {
    openFileAsNewTab(file); // "open" now means a new tab, not replacing the current one
  } else if (mode === 'append') {
    insertPDF(file, nPages);
  } else if (mode === 'merge') {
    insertPDF(file, curPg);
  }
}

async function insertPDF(file, afterPage) {
  try {
    toast('Inserting ' + file.name + '…', 3000);
    await loadPdfLib();
    const { PDFDocument } = PDFLib;
    const existingDoc = await PDFDocument.load(pdfBytes, { ignoreEncryption: true });
    const newDoc      = await PDFDocument.load(await file.arrayBuffer(), { ignoreEncryption: true });
    const merged      = await PDFDocument.create();

    const existingIndices = existingDoc.getPageIndices();
    const newIndices      = newDoc.getPageIndices();

    // Pages before insertion point
    if (afterPage > 0) {
      const before = await merged.copyPages(existingDoc, existingIndices.slice(0, afterPage));
      before.forEach(p => merged.addPage(p));
    }
    // Inserted pages
    const inserted = await merged.copyPages(newDoc, newIndices);
    inserted.forEach(p => merged.addPage(p));
    // Pages after insertion point
    if (afterPage < existingIndices.length) {
      const after = await merged.copyPages(existingDoc, existingIndices.slice(afterPage));
      after.forEach(p => merged.addPage(p));
    }

    const isAppend = afterPage >= existingIndices.length;
    const mergedBytes = await merged.save();
    const mergedFile  = new File([mergedBytes], pdfName, { type: 'application/pdf' });
    await loadPDF(mergedFile);
    if (activeTabId != null) saveActiveTabState(); // keep the tab record's bytes in sync
    const label = isAppend ? 'Appended' : `Inserted after page ${afterPage}`;
    toast(`✓ ${label}: ${file.name} — ${nPages} pages total`, 3000);
  } catch (e) {
    toast('Insert failed: ' + e.message);
    console.error('[EngDoc] insertPDF:', e);
  }
}

/* Extract text content from all pages using pdf.js — basic version,
   overridden below by the worker-based version if available */
async function extractPdfTextBasic() {
  for (let i = 1; i <= nPages; i++) {
    try {
      const page = await pdf.getPage(i);
      const tc = await page.getTextContent();
      const vp = page.getViewport({ scale: 1 }); // Use scale 1 for normalised coords
      pdfTextContent[i] = tc.items
        .filter(item => item.str && item.str.trim())
        .map(item => normalisePdfTextItem(item, vp));
    } catch(e) { /* skip page if extraction fails */ }
  }
}

// Converts a pdf.js text item's raw (page-space) position into normalised
// 0-1 viewport coordinates, using the viewport's own transform matrix rather
// than a plain width/height divide. A plain divide only works for an
// unrotated page — pdf.js reports item.transform in the page's raw content
// space, which for a rotated page (page.rotate = 90/180/270, common on
// landscape engineering sheets stored as rotated portrait) does NOT line up
// with the rotated viewport's width/height axes at all, silently swapping
// or scrambling x/y for every item on that page.
function normalisePdfTextItem(item, vp) {
  const [a, b, , , tx, ty] = item.transform;
  const start = pdfjsLib.Util.applyTransform([tx, ty], vp.transform);
  // item.width is already an absolute page-space displacement (pdf.js has
  // already applied the font-size scale) — NOT a text-space value that
  // still needs scaling by (a,b). (a,b) is only the *direction* the glyph
  // run travels in (and already has magnitude ~fontSize), so walking
  // "tx + a*width" double-applies that scale and wildly overshoots the true
  // end point. Normalise (a,b) to a unit vector first, then step by width.
  const mag = Math.hypot(a, b) || 1;
  const end = pdfjsLib.Util.applyTransform([tx + (a / mag) * item.width, ty + (b / mag) * item.width], vp.transform);
  return {
    str: item.str.trim(),
    x: start[0] / vp.width,
    y: start[1] / vp.height,
    fontSize: Math.hypot(item.transform[2], item.transform[3]) / vp.height,
    width: Math.hypot(end[0] - start[0], end[1] - start[1]) / vp.width,
  };
}

/* Try to detect common title block fields from page 1 text.
   
   Title block convention (NR / TRU / standard CAD):
   - Small label text (e.g. "Drawing Number") in top-left of a cell
   - Larger value text immediately below it in the same cell
   - Both share roughly the same x position (left edge of cell)
   
   Strategy:
   1. Find the label item (small font, matches pattern)
   2. Look for a value directly below it (larger font, same x band, within ~3 line-heights)
   3. Fall back to right-of-label only if nothing found below
   4. For multi-line values (e.g. Drawing Title), concatenate consecutive lines
*/
const ISO_SHEET_SIZES_MM = { A0: [1189, 841], A1: [841, 594], A2: [594, 420], A3: [420, 297], A4: [297, 210] };

async function autoDetectTitleBlock() {
  const items = pdfTextContent[1];
  if (!items || !items.length) return;

  // Sort by y then x for predictable order
  const sorted = [...items].sort((a, b) => a.y !== b.y ? a.y - b.y : a.x - b.x);

  // Estimate typical label font size (small items) and value font size (large items)
  const fontSizes = sorted.map(it => it.fontSize).filter(f => f > 0).sort((a,b) => a-b);
  const medianFont = fontSizes[Math.floor(fontSizes.length / 2)] || 0.01;

  // A "label" is small-font text — values are checked inline with fontSize comparisons
  const isLabel = (it) => it.fontSize <= medianFont * 1.4;

  /* Main lookup: find a SMALL-FONT label matching the pattern, then get the LARGER value below it */
  const find = (patterns, multiLine = false) => {
    for (const pat of patterns) {
      const re = new RegExp(pat, 'i');
      // Only match small-font items as labels (labels are always small in title blocks)
      const label = sorted.find(it =>
        re.test(it.str.trim()) &&
        it.str.trim().length < 50 &&
        isLabel(it)                 // ← must be small font
      );
      if (!label) continue;

      // Look for value directly below — must be in the same cell column (tight x-band)
      // and larger font than the label
      const below = sorted.filter(it =>
        it !== label &&
        it.y > label.y &&
        it.y <= label.y + 0.07 &&
        it.x >= label.x - 0.02 &&          // tight: value starts at roughly same x
        it.x <= label.x + 0.45 &&
        it.str.trim().length >= 1 &&
        it.fontSize >= label.fontSize * 1.1 // value is larger than label
      ).sort((a, b) => a.y - b.y || a.x - b.x);

      if (below.length) {
        if (!multiLine) return below[0].str.trim();
        // Multi-line: collect consecutive value lines in the same cell
        const firstY = below[0].y;
        const lines = sorted.filter(it =>
          it !== label &&
          it.y >= firstY - 0.002 &&
          it.y <= firstY + 0.15 &&
          it.x >= label.x - 0.02 &&
          it.x <= label.x + 0.45 &&
          it.fontSize >= label.fontSize * 1.1 &&
          it.str.trim().length > 0
        ).sort((a, b) => a.y - b.y || a.x - b.x);

        const result = [];
        let lastY = -999;
        for (const it of lines) {
          // Stop if we hit another small label (next cell)
          if (isLabel(it) && it.y > firstY + 0.005 && it.fontSize < label.fontSize * 1.5) break;
          if (Math.abs(it.y - lastY) < 0.003) {
            // Same line — append with space
            result[result.length - 1] += ' ' + it.str.trim();
          } else {
            result.push(it.str.trim());
            lastY = it.y;
          }
        }
        return result.filter(Boolean).join(' ').trim() || below[0].str.trim();
      }

      // No value below — try same line to the right (some title blocks are horizontal)
      const right = sorted.filter(it =>
        it !== label &&
        Math.abs(it.y - label.y) < 0.01 &&
        it.x > label.x + label.width + 0.01 &&
        it.str.trim().length >= 1 &&
        it.fontSize >= label.fontSize
      ).sort((a, b) => a.x - b.x);
      if (right.length) return right[0].str.trim();
    }
    return null;
  };

  // ── Field extraction — ordered by priority; more specific patterns first ──
  // Drawing Number (bottom of title block, longest ref string)
  const drawingNo = find([
    'drawing\\s*number', 'drg\\s*no\\.?$', 'dwg\\s*no\\.?$',
    'document\\s*number', 'doc\\s*no\\.?$', 'drawing\\s*no\\.?$'
  ]);
  // Revision
  const revision = find([
    '^revision$', '^rev\\.?$', 'revision\\s*no', 'issue\\s*no', 'issue\\s*status'
  ]);
  // Contract / Project numbers
  const contractNo = find([
    'contract\\s*no\\.?', 'contract\\s*number', 'job\\s*no', 'project\\s*no\\.?(?!t)', 'proj\\s*no'
  ]);
  // Contract Title
  const contractTitle = find(['contract\\s*title'], true);
  // Project name
  const projTitle = find(['^project$', 'project\\s*title', 'project\\s*name'], true);
  // Drawing Title
  const drawingTitle = find(['drawing\\s*title', 'document\\s*title', 'sheet\\s*title', '^title$'], true);
  // Location
  const location = find(['^location$', 'location\\s*[:/]?$', 'site\\s*location']);
  // Contractor / Organisation
  const contractor = find(['^contractor', 'contractor\\s*[:(]', '^organisation$']);
  // Type / Role → Discipline
  const typeField = find(['^type$']);
  const roleField = find(['^role$']);
  const drawn  = find(['^drawn$', '^drawn\\s*by$', 'designed\\s*by$', 'prepared\\s*by$']);
  const scale  = find(['^scale', '^scales?$']);

  let detected = 0;
  const set = (id, val) => {
    if (!val || val.length < 1 || val.length > 300) return;
    const el = document.getElementById(id);
    if (el && !el.value) { el.value = val.trim(); detected++; }
  };

  // Map to EMMA panel fields
  set('emma-doc-no',      drawingNo);
  set('emma-rev-no',      revision);
  set('emma-proj-no',     contractNo);
  set('emma-proj-title',  contractTitle || location || projTitle || contractor);
  set('emma-specific',    drawingTitle || contractTitle);

  // Discipline from type/role fields
  const discRaw = typeField || roleField;
  if (discRaw) {
    const discEl = document.getElementById('emma-discipline');
    const discMap = [
      ['civil', 'Civils'], ['drainage', 'Drainage'],
      ['track', 'Track'], ['rail engineering', 'Civils'],
      ['electrical', 'Electrical Power'], ['power', 'Electrical Power'],
      ['signal', 'Signalling'], ['telecoms', 'Telecoms'], ['telecom', 'Telecoms'],
      ['geotech', 'Geotechnical'], ['geo', 'Geotechnical'],
      ['ole', 'OLE'], ['overhead', 'OLE'],
      ['environ', 'Environmental'], ['bim', 'BIM'], ['survey', 'Survey'],
      ['project management', 'Project Management'], ['engineering management', 'Engineering Management'],
    ];
    const lc = discRaw.toLowerCase();
    for (const [key, val] of discMap) {
      if (lc.includes(key)) { discEl.value = val; detected++; break; }
    }
  }

  // Pre-fill author name from drawn field
  if (drawn && drawn.length < 40 && drawn !== drawingNo) {
    const authEl = document.getElementById('author-input');
    if (authEl && !authEl.value) authEl.value = drawn.trim();
  }

  // ── Auto-calibrate measure tool from detected scale string ──
  // The label/value cell lookup above requires the "SCALE" label and its value to be
  // separate text runs in different font sizes — many title blocks instead render
  // them as a single combined run (e.g. "SCALE 1:100") or in matching font sizes, so
  // fall back to a plain text-scan (same approach as checkScaleBar()) when it misses.
  let scaleMatch = scale ? scale.match(/1\s*[:\/]\s*(\d+)/) : null;
  if (!scaleMatch) {
    const pageStr = sorted.map(it => it.str).join(' ');
    scaleMatch = pageStr.match(/scale[^0-9]{0,15}1\s*[:\/]\s*(\d+)/i) || pageStr.match(/1\s*[:\/]\s*(\d+)/);
  }
  if (scaleMatch) {
    const ratio = parseInt(scaleMatch[1]);

    // pxPerUnit is defined as screen px per real-world unit at our own zoom=1,
    // which pdf.js's getViewport({scale:1}) already anchors at 1pt = 1/72in —
    // NOT the 96px/in CSS reference pixel. Using 96 here silently overstates
    // every auto-detected scale by a third.
    let pxPerMm = 72 / 25.4;

    // If the title block also states a paper size (A0–A4), derive px-per-mm
    // from the PDF's actual page dimensions vs. that nominal size instead.
    // Many drawings are exported/printed at a different page size than the
    // sheet they were designed for (e.g. an A1 drawing plotted to an A3 PDF),
    // so the true-to-size assumption above can be off by whatever that
    // export scale-down factor is — this self-corrects for it.
    const paperSizeStr = find(['sheet\\s*size', 'paper\\s*size', 'drawing\\s*size', '^size$']);
    const sizeSource = paperSizeStr || sorted.find(it => /^(A0|A1|A2|A3|A4)$/i.test(it.str.trim()))?.str;
    const paperMatch = sizeSource && sizeSource.match(/\b(A0|A1|A2|A3|A4)\b/i);
    if (paperMatch && typeof pdf !== 'undefined' && pdf) {
      try {
        const page1 = await getCachedPage(1);
        const vp1 = page1.getViewport({ scale: 1 });
        const [longMm, shortMm] = ISO_SHEET_SIZES_MM[paperMatch[1].toUpperCase()];
        const [longPt, shortPt] = vp1.width >= vp1.height ? [vp1.width, vp1.height] : [vp1.height, vp1.width];
        pxPerMm = ((longPt / longMm) + (shortPt / shortMm)) / 2;
      } catch (e) { /* keep the true-to-size fallback */ }
    }

    measureScale = { pxPerUnit: pxPerMm * 1000 / ratio, unit: 'm' };
    localStorage.setItem('engdoc_scale', JSON.stringify(measureScale));
    document.getElementById('sb-scale').textContent = `⚖ 1:${ratio} (m)`;
    detected++;
    toast(`✓ Scale auto-set: 1:${ratio} — measuring in metres`, 3500);
  }

  if (detected > 0) {
    toast(`✓ Title block: ${detected} field${detected !== 1 ? 's' : ''} auto-filled — check EMMA panel`, 4500);
  } else {
    toast('Title block fields not detected — fill EMMA panel manually', 3000);
  }

  console.log('[EngDoc] Title block:', { drawingNo, revision, contractNo, contractTitle, projTitle, drawingTitle, location, contractor, typeField, roleField, drawn });
  buildSearchIndex();
}

/* ─── PDF SEARCH ─── */
let searchIndex = []; // [{pageNum, str, x, y}]

function buildSearchIndex() {
  searchIndex = [];
  for (const [pgStr, items] of Object.entries(pdfTextContent)) {
    const pg = parseInt(pgStr);
    items.forEach(it => { if (it.str.length > 1) searchIndex.push({ pageNum: pg, ...it }); });
  }
}

function searchPdf(query) {
  if (!query || !searchIndex.length) return [];
  const q = query.toLowerCase();
  return searchIndex.filter(it => it.str.toLowerCase().includes(q)).slice(0, 50);
}

function onSearchInput(query) {
  const status = document.getElementById('search-status');
  const results = document.getElementById('search-results');
  results.innerHTML = '';
  if (!query.trim()) { status.textContent = `${searchIndex.length} text items indexed`; return; }
  const hits = searchPdf(query.trim());
  status.textContent = `${hits.length} result${hits.length !== 1 ? 's' : ''}${hits.length === 50 ? ' (showing first 50)' : ''}`;
  const esc = s => s.replace(/[<>&"]/g, c => ({'<':'&lt;','>':'&gt;','&':'&amp;','"':'&quot;'}[c]));
  const hi  = (str, q) => esc(str).replace(new RegExp(q.replace(/[.*+?^${}()|[\]\\]/g,'\\$&'), 'gi'), m => `<mark>${m}</mark>`);
  hits.forEach(hit => {
    const div = document.createElement('div'); div.className = 'sresult';
    div.innerHTML = `<div class="sresult-text">${hi(hit.str, query.trim())}</div><div class="sresult-pg">Page ${hit.pageNum}</div>`;
    div.addEventListener('click', () => {
      highlightSearchHit(hit);
    });
    results.appendChild(div);
  });
}

function highlightSearchHit(hit) {
  // Scroll to page first, then flash after a short delay so page is visible
  scrollToPage(hit.pageNum);
  setTimeout(() => {
    const ov = document.querySelector(`.aoverlay[data-page="${hit.pageNum}"]`);
    if (!ov) return;
    const flash = document.createElement('div');
    flash.style.cssText =
      `position:absolute;left:${hit.x * 100}%;top:${hit.y * 100}%;` +
      `width:${Math.max(hit.width * 100, 4)}%;height:${Math.max(hit.fontSize * 100 * 1.6, 1.5)}%;` +
      `background:#fef08a;border-radius:2px;pointer-events:none;z-index:20;` +
      `opacity:0;transition:opacity 0.25s ease`;
    ov.appendChild(flash);
    // Fade in
    requestAnimationFrame(() => requestAnimationFrame(() => { flash.style.opacity = '0.75'; }));
    // Hold then fade out
    setTimeout(() => {
      flash.style.transition = 'opacity 0.8s ease';
      flash.style.opacity = '0';
      setTimeout(() => flash.remove(), 900);
    }, 2000);
  }, 350);
}

/* ═══════════════════════════════════════════════
   VIRTUAL / LAZY RENDERING
   Strategy:
   1. Get page 1 viewport synchronously to seed shell sizes.
   2. Build all shells instantly using page-1 dims as estimate —
      they get corrected when renderPageContent runs per-page.
   3. renderPageContent also updates wrap + overlay to exact dims.
═══════════════════════════════════════════════ */
async function buildPageShells() {
  const container = document.getElementById('pdfpages');
  container.innerHTML = '';

  // Get page 1 viewport to estimate shell sizes — use cache if available
  const page1 = _pageCache[1] || await pdf.getPage(1);
  if (!_pageCache[1]) _pageCache[1] = page1;
  const vp1 = page1.getViewport({ scale: zoom });
  const estW = vp1.width, estH = vp1.height;

  for (let i = 1; i <= nPages; i++) {
    // Use page-1 estimate; renderPageContent will correct it per page
    const shellW = estW, shellH = estH;

    const wrap = document.createElement('div');
    wrap.className = 'pwrap unrendered';
    wrap.id = `pw-${i}`;
    wrap.style.width  = shellW + 'px';
    wrap.style.height = shellH + 'px';

    // Overlay sized to match shell — corrected in renderPageContent
    const ov = document.createElement('div');
    // In pan mode the overlay must be pass-through (no 'active' class)
    ov.className = 'aoverlay active';
    ov.dataset.page = i;
    ov.style.cssText = `position:absolute;top:0;left:0;width:${shellW}px;height:${shellH}px`;
    // Attach events with a deferred viewport — resolved when page renders
    ov._pendingAttach = i; // flag; events attached after real vp known

    const badge = document.createElement('div');
    badge.className = 'pnbadge';
    badge.textContent = pageLabels[i] ? (pageLabels[i] + '  ·  p.' + (() => { let n=0; for(let j=1;j<=i;j++){if(pageLabels[j]===pageLabels[i])n++;} return n; })()) : ('Page ' + i);

    wrap.appendChild(ov);
    wrap.appendChild(badge);
    container.appendChild(wrap);

    wrap.addEventListener('mousemove', e => {
      const r = wrap.getBoundingClientRect();
      const pv = pageViewports[i];
      if (!pv) return;
      document.getElementById('sb-pos').textContent =
        `Pg ${i} · ${Math.round((e.clientX - r.left) / zoom)}, ${Math.round((e.clientY - r.top) / zoom)}`;
    });
    wrap.addEventListener('mouseleave', () => { document.getElementById('sb-pos').textContent = '—'; });
  }
}

function getVisibleRange() {
  const viewer = document.getElementById('viewer');
  const scrollTop = viewer.scrollTop;
  const viewH     = viewer.clientHeight;
  const viewBot   = scrollTop + viewH;

  // Fast path: use cumulative page heights from pageViewports instead of
  // touching getBoundingClientRect on every page (avoids layout thrashing).
  const container = document.getElementById('pdfpages');
  const padTop = 28; // matches #pdfpages padding-top
  const gap    = 24; // matches .pwrap margin-bottom

  let cumY  = padTop;
  let first = nPages;
  let last  = 1;

  for (let i = 1; i <= nPages; i++) {
    const pv = pageViewports[i];
    const h  = pv ? pv.height : (pageViewports[1] ? pageViewports[1].height : 1000);
    const pageTop = cumY;
    const pageBot = cumY + h;

    if (pageBot > scrollTop && pageTop < viewBot) {
      if (i < first) first = i;
      if (i > last)  last  = i;
    }

    // Once we've passed the visible area we can stop
    if (pageTop > viewBot) break;
    cumY = pageBot + gap;
  }

  if (first > last) { first = 1; last = Math.min(nPages, 3); } // fallback
  return { first: Math.max(1, first - OVERSCAN), last: Math.min(nPages, last + OVERSCAN) };
}

const RENDER_CONCURRENCY = 4; // render up to 4 pages simultaneously

function scheduleRender() {
  if (renderScheduled) return;
  renderScheduled = true;
  // requestAnimationFrame: limits renders to 60fps max regardless of scroll rate.
  // During fast panning, many scroll events fire per frame — rAF collapses them
  // all into one render per display refresh. setTimeout(0) does not do this and
  // causes hundreds of concurrent render chains during a fast pan.
  requestAnimationFrame(async () => {
    renderScheduled = false;
    const myGen = docGen; // bail if a tab switch lands mid-batch below
    if (!pdf) return;
    const { first, last } = getVisibleRange();

    // Unload canvases only for pages very far from the viewport.
    // A tight threshold (e.g. 4 pages) causes black flashes during normal panning
    // because canvases are destroyed then immediately needed again as you scroll back.
    // Keep a generous buffer — GPU memory for typical PDF pages is small (1-3 MB each).
    const UNLOAD_BUFFER = Math.max(10, Math.ceil(nPages * 0.2)); // 10 pages or 20% of doc
    for (const pg of [...renderedPages]) {
      if (pg < first - UNLOAD_BUFFER || pg > last + UNLOAD_BUFFER) {
        const wrap = document.getElementById('pw-' + pg);
        if (wrap) {
          const canvas = wrap.querySelector('canvas');
          if (canvas) { canvas.width = 1; canvas.height = 1; canvas.remove(); }
          wrap.querySelector('.textLayer')?.remove();
          wrap.classList.add('unrendered');
        }
        renderedPages.delete(pg);
        delete _pageCache[pg];
      }
    }

    // Collect visible pages that need rendering
    const toRender = [];
    for (let i = first; i <= last; i++) {
      if (!renderedPages.has(i) && !renderQueue.has(i)) toRender.push(i);
    }
    if (!toRender.length) return;

    // Render 2 pages at a time — PDF.js worker is the bottleneck
    const CONCURRENCY = 2;
    for (let i = 0; i < toRender.length; i += CONCURRENCY) {
      if (myGen !== docGen) return; // a tab switch happened mid-batch — the new tab's own scheduleRender owns this now
      const batch = toRender.slice(i, i + CONCURRENCY);
      batch.forEach(pg => renderQueue.add(pg));
      await Promise.all(batch.map(pg =>
        renderPageContent(pg)
          .then(() => renderQueue.delete(pg))
          .catch(err => { renderQueue.delete(pg); console.error('[ENGDOC] renderPageContent page', pg, 'failed:', err); })
      ));
    }
  });
}

// Page object cache — avoid re-fetching already-loaded page objects
const _pageCache = {};
async function getCachedPage(num) {
  if (!_pageCache[num]) _pageCache[num] = await pdf.getPage(num);
  return _pageCache[num];
}

// ═══════════════════════════════════════════════
//  VECTOR GEOMETRY EXTRACTION (for snap-to-drawing)
//  Records every path vertex pdf.js actually draws, by intercepting the
//  canvas path methods and reading ctx.getTransform() at call time — this
//  is the real CTM pdf.js uses to render (incl. nested Form XObject / clip
//  transforms), so it's exact without us re-implementing PDF matrix math.
//  Curve control points are dropped, but each closed all-curve subpath is
//  checked against its own bounding box to see if it's (approximately) a
//  circle/ellipse — standard circle-drawing code emits 4 bezier curves
//  whose endpoints sit exactly at the top/right/bottom/left of the circle,
//  so the endpoint bbox already gives the true center, no curve math needed.
//  A uniform grid then indexes points/midpoints/centers/segments for fast
//  nearest-neighbour lookup (see findNearestInLayer / findNearestVectorEdgePoint
//  / findNearestVectorIntersection).
// ═══════════════════════════════════════════════
const VEC_GRID_CELL = 32; // px — comfortably larger than the max selectable snap radius

function beginVectorGeomRecording(ctx, dpr) {
  const points = [];
  const segments = [];
  const centers = [];
  let curX = 0, curY = 0, startX = 0, startY = 0;
  let subLineCount = 0, subCurveCount = 0;
  let subMinX = Infinity, subMinY = Infinity, subMaxX = -Infinity, subMaxY = -Infinity;
  let subFirstPx = null, subLastPx = null;
  let active = true;

  const orig = {
    moveTo: ctx.moveTo, lineTo: ctx.lineTo, rect: ctx.rect,
    bezierCurveTo: ctx.bezierCurveTo, quadraticCurveTo: ctx.quadraticCurveTo,
    closePath: ctx.closePath,
  };

  const toPx = (x, y) => {
    const m = ctx.getTransform();
    return { x: (m.a * x + m.c * y + m.e) / dpr, y: (m.b * x + m.d * y + m.f) / dpr };
  };

  const touchBBox = p => {
    if (p.x < subMinX) subMinX = p.x; if (p.x > subMaxX) subMaxX = p.x;
    if (p.y < subMinY) subMinY = p.y; if (p.y > subMaxY) subMaxY = p.y;
  };

  // A subpath is a circle/ellipse candidate iff it's built entirely from
  // curves (no straight edges), has enough segments to plausibly close a
  // loop, ends back near where it started (whether or not an explicit
  // closePath() was issued — many PDF producers just let the last curve
  // land on the start point), and its bbox is roughly square (true circles;
  // mild ellipses still pass a loose ratio check).
  const finalizeSub = () => {
    const autoClosed = subFirstPx && subLastPx && Math.hypot(subFirstPx.x - subLastPx.x, subFirstPx.y - subLastPx.y) < 1.5;
    if (subCurveCount >= 3 && subLineCount === 0 && autoClosed &&
        Number.isFinite(subMinX) && subMaxX > subMinX && subMaxY > subMinY) {
      const w = subMaxX - subMinX, h = subMaxY - subMinY;
      const ratio = w > h ? w / h : h / w;
      if (ratio < 1.35) {
        centers.push({ x: (subMinX + subMaxX) / 2, y: (subMinY + subMaxY) / 2, r: (w + h) / 4 });
      }
    }
    subLineCount = 0; subCurveCount = 0;
    subMinX = Infinity; subMinY = Infinity; subMaxX = -Infinity; subMaxY = -Infinity;
    subFirstPx = null; subLastPx = null;
  };

  ctx.moveTo = function (x, y) {
    if (active) {
      finalizeSub();
      const p = toPx(x, y);
      points.push(p); touchBBox(p);
      subFirstPx = p; subLastPx = p;
      curX = x; curY = y; startX = x; startY = y;
    }
    return orig.moveTo.call(this, x, y);
  };
  ctx.lineTo = function (x, y) {
    if (active) {
      const p0 = toPx(curX, curY), p1 = toPx(x, y);
      points.push(p1); touchBBox(p1);
      segments.push({ x1: p0.x, y1: p0.y, x2: p1.x, y2: p1.y });
      subLineCount++;
      subLastPx = p1;
      curX = x; curY = y;
    }
    return orig.lineTo.call(this, x, y);
  };
  ctx.rect = function (x, y, w, h) {
    if (active) {
      finalizeSub();
      const c1 = toPx(x, y), c2 = toPx(x + w, y), c3 = toPx(x + w, y + h), c4 = toPx(x, y + h);
      points.push(c1, c2, c3, c4);
      segments.push({ x1: c1.x, y1: c1.y, x2: c2.x, y2: c2.y }, { x1: c2.x, y1: c2.y, x2: c3.x, y2: c3.y },
                     { x1: c3.x, y1: c3.y, x2: c4.x, y2: c4.y }, { x1: c4.x, y1: c4.y, x2: c1.x, y2: c1.y });
      curX = x; curY = y; startX = x; startY = y;
      finalizeSub(); // rect is its own closed subpath, but never a circle candidate
    }
    return orig.rect.call(this, x, y, w, h);
  };
  ctx.bezierCurveTo = function (c1x, c1y, c2x, c2y, x, y) {
    if (active) {
      const p = toPx(x, y);
      points.push(p); touchBBox(p);
      subCurveCount++;
      subLastPx = p;
      curX = x; curY = y;
    }
    return orig.bezierCurveTo.call(this, c1x, c1y, c2x, c2y, x, y);
  };
  ctx.quadraticCurveTo = function (cx, cy, x, y) {
    if (active) {
      const p = toPx(x, y);
      points.push(p); touchBBox(p);
      subCurveCount++;
      subLastPx = p;
      curX = x; curY = y;
    }
    return orig.quadraticCurveTo.call(this, cx, cy, x, y);
  };
  ctx.closePath = function () {
    if (active) {
      if (curX !== startX || curY !== startY) {
        const p0 = toPx(curX, curY), p1 = toPx(startX, startY);
        segments.push({ x1: p0.x, y1: p0.y, x2: p1.x, y2: p1.y });
      }
      finalizeSub();
      curX = startX; curY = startY;
    }
    return orig.closePath.call(this);
  };

  const restore = () => {
    if (!active) return;
    active = false;
    ctx.moveTo = orig.moveTo; ctx.lineTo = orig.lineTo; ctx.rect = orig.rect;
    ctx.bezierCurveTo = orig.bezierCurveTo; ctx.quadraticCurveTo = orig.quadraticCurveTo;
    ctx.closePath = orig.closePath;
  };

  return {
    restore,
    finish() {
      restore();
      finalizeSub(); // flush the final subpath so it's included if it qualifies
      return buildVectorGeomIndex(points, segments, centers);
    },
  };
}

function buildVectorGeomIndex(rawPoints, segments, rawCenters) {
  // Dedupe near-identical vertices (overlapping strokes/hatching draw the same
  // corner many times) so the grid stays small and lookups stay fast.
  const dedupe = (list) => {
    const seen = new Set();
    const out = [];
    for (const p of list) {
      if (!Number.isFinite(p.x) || !Number.isFinite(p.y)) continue;
      const key = Math.round(p.x * 4) + ',' + Math.round(p.y * 4); // 0.25px buckets
      if (seen.has(key)) continue;
      seen.add(key);
      out.push(p);
    }
    return out;
  };
  const points = dedupe(rawPoints);
  const centers = dedupe(rawCenters);
  const midpoints = segments.map(s => ({ x: (s.x1 + s.x2) / 2, y: (s.y1 + s.y2) / 2 }));

  const grid = new Map();
  const addToGrid = (cx, cy, kind, idx) => {
    const k = cx + ',' + cy;
    let bucket = grid.get(k);
    if (!bucket) { bucket = { pt: [], mid: [], ctr: [], seg: [] }; grid.set(k, bucket); }
    bucket[kind].push(idx);
  };
  const addPointLayer = (list, kind) => list.forEach((p, i) =>
    addToGrid(Math.floor(p.x / VEC_GRID_CELL), Math.floor(p.y / VEC_GRID_CELL), kind, i));

  addPointLayer(points, 'pt');
  addPointLayer(midpoints, 'mid');
  addPointLayer(centers, 'ctr');
  segments.forEach((s, i) => {
    const x0 = Math.min(s.x1, s.x2), x1 = Math.max(s.x1, s.x2);
    const y0 = Math.min(s.y1, s.y2), y1 = Math.max(s.y1, s.y2);
    const cx0 = Math.floor(x0 / VEC_GRID_CELL), cx1 = Math.floor(x1 / VEC_GRID_CELL);
    const cy0 = Math.floor(y0 / VEC_GRID_CELL), cy1 = Math.floor(y1 / VEC_GRID_CELL);
    // Bound the cell span so a very long segment can't blow up index size
    for (let cx = cx0; cx <= cx1 && cx <= cx0 + 200; cx++) {
      for (let cy = cy0; cy <= cy1 && cy <= cy0 + 200; cy++) addToGrid(cx, cy, 'seg', i);
    }
  });

  return { points, midpoints, centers, segments, grid };
}

// Nearest point in a given layer ('pt' | 'mid' | 'ctr') within `radius` px
// of (mx,my), or null.
function findNearestInLayer(geom, layerName, bucketKind, mx, my, radius) {
  if (!geom) return null;
  const layer = geom[layerName];
  const cx = Math.floor(mx / VEC_GRID_CELL), cy = Math.floor(my / VEC_GRID_CELL);
  let best = null, bestDist = radius;
  for (let dx = -1; dx <= 1; dx++) {
    for (let dy = -1; dy <= 1; dy++) {
      const bucket = geom.grid.get((cx + dx) + ',' + (cy + dy));
      if (!bucket) continue;
      for (const i of bucket[bucketKind]) {
        const p = layer[i];
        const d = Math.hypot(mx - p.x, my - p.y);
        if (d < bestDist) { bestDist = d; best = p; }
      }
    }
  }
  return best;
}

// Nearest point ON a drawn line segment (perpendicular projection, clamped)
// within `radius` px of (mx,my), or null. Lets you snap onto an edge, not
// just its endpoints.
function findNearestVectorEdgePoint(geom, mx, my, radius) {
  if (!geom) return null;
  const cx = Math.floor(mx / VEC_GRID_CELL), cy = Math.floor(my / VEC_GRID_CELL);
  let best = null, bestDist = radius;
  const seen = new Set();
  for (let dx = -1; dx <= 1; dx++) {
    for (let dy = -1; dy <= 1; dy++) {
      const bucket = geom.grid.get((cx + dx) + ',' + (cy + dy));
      if (!bucket) continue;
      for (const i of bucket.seg) {
        if (seen.has(i)) continue;
        seen.add(i);
        const s = geom.segments[i];
        const dxs = s.x2 - s.x1, dys = s.y2 - s.y1;
        const len2 = dxs * dxs + dys * dys;
        let t = len2 > 0 ? ((mx - s.x1) * dxs + (my - s.y1) * dys) / len2 : 0;
        t = Math.max(0, Math.min(1, t));
        const px = s.x1 + t * dxs, py = s.y1 + t * dys;
        const d = Math.hypot(mx - px, my - py);
        if (d < bestDist) { bestDist = d; best = { x: px, y: py }; }
      }
    }
  }
  return best;
}

// Nearest intersection of two drawn (non-parallel) segments within `radius`
// px of (mx,my), or null. Only checks segments near the cursor — comparing
// every pair on the page would be O(n²) over thousands of paths, but the
// local neighbourhood is always small.
function findNearestVectorIntersection(geom, mx, my, radius) {
  if (!geom) return null;
  const cx = Math.floor(mx / VEC_GRID_CELL), cy = Math.floor(my / VEC_GRID_CELL);
  const seen = new Set();
  const nearby = [];
  for (let dx = -1; dx <= 1; dx++) {
    for (let dy = -1; dy <= 1; dy++) {
      const bucket = geom.grid.get((cx + dx) + ',' + (cy + dy));
      if (!bucket) continue;
      for (const i of bucket.seg) {
        if (seen.has(i)) continue;
        seen.add(i);
        nearby.push(geom.segments[i]);
        if (nearby.length >= 120) break; // safety cap on very dense hatching
      }
    }
  }
  let best = null, bestDist = radius;
  for (let i = 0; i < nearby.length; i++) {
    for (let j = i + 1; j < nearby.length; j++) {
      const a = nearby[i], b = nearby[j];
      const dax = a.x2 - a.x1, day = a.y2 - a.y1;
      const dbx = b.x2 - b.x1, dby = b.y2 - b.y1;
      const denom = dax * dby - day * dbx;
      if (Math.abs(denom) < 1e-9) continue; // parallel
      const t = ((b.x1 - a.x1) * dby - (b.y1 - a.y1) * dbx) / denom;
      const u = ((b.x1 - a.x1) * day - (b.y1 - a.y1) * dax) / denom;
      if (t < -0.01 || t > 1.01 || u < -0.01 || u > 1.01) continue; // crossing must lie on both segments
      const px = a.x1 + t * dax, py = a.y1 + t * day;
      const d = Math.hypot(mx - px, my - py);
      if (d < bestDist) { bestDist = d; best = { x: px, y: py }; }
    }
  }
  return best;
}

async function renderPageContent(pageNum) {
  const wrap = document.getElementById('pw-' + pageNum);
  if (!wrap || renderedPages.has(pageNum)) return;
  const myGen = docGen; // if a tab switch lands mid-render, don't let this write into the new tab's state

  const page = await getCachedPage(pageNum);
  if (myGen !== docGen) return;
  const vp   = page.getViewport({ scale: zoom });

  // Device pixel ratio for sharp rendering on HiDPI/Retina screens
  const dpr = Math.min(window.devicePixelRatio || 1, 2); // cap at 2x

  // Store real viewport for this page
  pageViewports[pageNum] = { width: vp.width, height: vp.height, vp };

  // Correct wrap + overlay to exact page dimensions
  wrap.style.width  = vp.width  + 'px';
  wrap.style.height = vp.height + 'px';

  let ov = wrap.querySelector('.aoverlay');
  ov.style.width  = vp.width  + 'px';
  ov.style.height = vp.height + 'px';

  // Attach drawing events on first render
  if (ov._pendingAttach) {
    ov._pendingAttach = false;
    attachEvents(ov, pageNum, vp);
    attachOverlayCtxMenu(ov); // right-click works from first render
    try { syncAnnotsOnOverlay(ov, pageNum); }
    catch (e) { console.error('[ENGDOC] syncAnnotsOnOverlay page', pageNum, 'failed:', e); }
  }

  // ── HiDPI canvas — rendered off-screen to prevent black flash on swap ──
  // alpha:false canvases are solid black until drawn, so inserting before render
  // causes a visible flash. Build and fill the canvas off-DOM, then swap atomically.
  const canvas = document.createElement('canvas');
  canvas.width  = Math.floor(vp.width  * dpr);
  canvas.height = Math.floor(vp.height * dpr);
  canvas.style.cssText = 'width:' + vp.width + 'px;height:' + vp.height + 'px;display:block';

  const ctx = canvas.getContext('2d', { alpha: false });
  ctx.scale(dpr, dpr);
  // Pre-fill white so a partially-drawn frame is never black
  ctx.fillStyle = '#ffffff';
  ctx.fillRect(0, 0, vp.width, vp.height);

  // Record every path vertex/segment pdf.js actually draws (via ctx.getTransform(),
  // which reflects the exact CTM pdf.js applies incl. nested Form XObject transforms)
  // so real drawing geometry (lines, rect corners, polylines) can be used as snap
  // targets. Cheap relative to the render itself; only runs once per page render.
  const _vecRecorder = beginVectorGeomRecording(ctx, dpr);

  // Render canvas — use 'display' intent for speed; swap to 'print' for export
  const renderTask = page.render({
    canvasContext: ctx,
    viewport: vp,
    intent: 'display',
  });

  // ── Text layer (selectable text) ──
  // On first render: fetch text content from PDF worker.
  // On re-renders (zoom change): reuse cached raw items, just rescale coordinates.
  if (!window._pageRawText) window._pageRawText = {};
  await Promise.all([renderTask.promise, Promise.resolve()]);
  if (myGen !== docGen) return;

  try { _pageVectorGeom[pageNum] = _vecRecorder.finish(); }
  catch (e) { _vecRecorder.restore(); console.warn('[ENGDOC] vector geom extraction page', pageNum, 'failed:', e); }

  if (!window._pageRawText[pageNum]) {
    try {
      const textContent = await page.getTextContent({ includeMarkedContent: false });
      if (myGen !== docGen) return;
      window._pageRawText[pageNum] = textContent.items.filter(item => item.str?.trim());
    } catch (e) {
      window._pageRawText[pageNum] = [];
      console.warn('[ENGDOC] getTextContent page', pageNum, 'failed:', e);
    }
  }

  // Map each item's raw PDF-space transform into viewport CSS-pixel space via
  // vp.transform rather than a plain e/f * zoom + flip. A plain multiply only
  // matches the viewport for an unrotated page — pdf.js reports item.transform
  // in the page's raw content space, which for a rotated page (page.rotate =
  // 90/180/270, common on landscape engineering sheets stored as rotated
  // portrait) does NOT line up with the rotated viewport's axes, silently
  // scrambling every item's x/y/angle and making the select-tool's hit-test
  // rectangles land in the wrong place.
  _pageTextItems[pageNum] = (window._pageRawText[pageNum] || []).map(item => {
    const [a, b, c, d, tx, ty] = item.transform;
    const start = pdfjsLib.Util.applyTransform([tx, ty], vp.transform);
    const magW = Math.hypot(a, b) || 1;
    const wLocal = item.width || 0;
    const end = pdfjsLib.Util.applyTransform([tx + (a / magW) * wLocal, ty + (b / magW) * wLocal], vp.transform);
    const magH = Math.hypot(c, d) || 1;
    const hLocal = item.height || magH;
    const endH = pdfjsLib.Util.applyTransform([tx + (c / magH) * hLocal, ty + (d / magH) * hLocal], vp.transform);
    const w = Math.hypot(end[0] - start[0], end[1] - start[1]);
    const h = Math.hypot(endH[0] - start[0], endH[1] - start[1]);
    // Angle of the width vector in viewport (CSS, y-down) space — already
    // accounts for any page rotation and the PDF-to-CSS y-flip, so downstream
    // rendering must use it directly (no extra negation).
    const angle = Math.atan2(end[1] - start[1], end[0] - start[0]);
    return { str: item.str, x: start[0], y: start[1], w, h, angle };
  });

  // Atomic swap: remove old canvas only after new one is fully rendered
  wrap.querySelector('canvas')?.remove();
  wrap.querySelector('.textLayer')?.remove();

  ov = wrap.querySelector('.aoverlay');
  wrap.insertBefore(canvas, ov);

  wrap.classList.remove('unrendered');
  renderedPages.add(pageNum);
  // Clear the CSS scale preview — hi-res canvas is now in place
  canvas.style.transform = '';
  canvas.style.width  = '';
  canvas.style.height = '';
}

async function rerenderAll() {
  if (!pdf) return;
  const savedPg = curPg;

  // ── Instant CSS scale preview ──
  // While hi-res renders, scale existing canvases so user sees something immediately.
  const page1Obj = _pageCache[1] || await pdf.getPage(1);
  if (!_pageCache[1]) _pageCache[1] = page1Obj;
  const unscaledVp = page1Obj.getViewport({ scale: 1 });
  const oldZoom = pageViewports[1] ? (pageViewports[1].width / unscaledVp.width) : zoom;
  const scaleFactor = zoom / oldZoom;

  if (scaleFactor !== 1 && scaleFactor > 0) {
    document.querySelectorAll('.pwrap').forEach(wrap => {
      const canvas = wrap.querySelector('canvas');
      if (!canvas) return;
      // Only scale the canvas visually — do NOT resize the wrapper or overlay.
      // Resizing those would corrupt coordinate calculations in syncAnnots/select tool
      // before renderPageContent has updated pageViewports to the new zoom.
      canvas.style.transformOrigin = 'top left';
      canvas.style.transform = 'scale(' + scaleFactor + ')';
    });
  }

  // ── Hi-res re-render ──
  // Mark all pages unrendered — DO NOT clear _pageCache (page objects are zoom-independent)
  renderedPages.clear();
  renderQueue.clear();
  // pageViewports will be updated per-page in renderPageContent.
  // Do NOT call syncAnnots() here — annotations use % coords and reposition automatically
  // when the overlay pixel size is corrected by renderPageContent. Calling syncAnnots on
  // every zoom rebuilds all annotation DOM which is the main source of zoom lag.

  // Yield once with setTimeout(0) so the CSS scale preview above can paint before
  // the first rAF render fires. Without this yield the preview and the hi-res render
  // race and the user sees neither improvement.
  setTimeout(() => {
    scheduleRender();
    // Ensure scroll position after render
    requestAnimationFrame(() => {
      const el = document.getElementById('pw-' + savedPg);
      if (el) el.scrollIntoView({ block: 'start' });
    });
  }, 0);
}

document.getElementById('viewer').addEventListener('scroll', () => {
  // Skip render scheduling while actively panning — the browser composites
  // existing canvases natively. Rendering fires once when the pan ends.
  if (!panDragging) scheduleRender();
  if (!pdf) return;

  // Find the current page using scroll-position arithmetic — zero DOM reads.
  // getBoundingClientRect on every page element forces n layout reflows per scroll event.
  const viewer  = document.getElementById('viewer');
  const viewMid = viewer.scrollTop + viewer.clientHeight / 2;
  const padTop  = 28, gap = 24;
  let cumY = padTop, best = 1;
  for (let i = 1; i <= nPages; i++) {
    const h = (pageViewports[i] || pageViewports[1] || {height: 1000}).height;
    if (cumY + h > viewMid) { best = i; break; }
    cumY += h + gap;
    best = i;
  }

  if (best !== curPg) {
    curPg = best;
    document.getElementById('pgi').value = best;
    // Debounce thumbnail highlight — querySelectorAll on every scroll event is expensive
    clearTimeout(window._thumbDebounce);
    window._thumbDebounce = setTimeout(() => {
      document.querySelectorAll('.titem').forEach(t =>
        t.classList.toggle('active', parseInt(t.dataset.page) === best));
    }, 150);
  }
}, { passive: true });

/* ═══════════════════════════════════════════════
   THUMBNAILS (lazy too, via IntersectionObserver)
═══════════════════════════════════════════════ */
async function buildThumbs() {
  const panel = document.getElementById('sp-pages');
  panel.innerHTML = '';
  const limit = Math.min(nPages, 300);
  const hasLabels = Object.keys(pageLabels).length > 0;
  let lastSource = null;

  for (let i = 1; i <= limit; i++) {
    const source = pageLabels[i] || null;

    // Insert a source divider when the PDF changes (multi-PDF mode)
    if (hasLabels && source && source !== lastSource) {
      const div = document.createElement('div');
      div.className = 'tgroup-header';
      div.textContent = source;
      div.title = source;
      panel.appendChild(div);
      lastSource = source;
    }

    const item = document.createElement('div');
    const isActive = (i === curPg);
    item.className = 'titem'
      + (isActive ? ' active' : '')
      + (selectedPages.has(i) ? ' t-selected' : '');
    item.dataset.page = i;
    item.draggable = true;

    // ── click: navigate / Ctrl-click: toggle select / Shift-click: range select ──
    item.addEventListener('click', e => {
      if (e.ctrlKey || e.metaKey) {
        if (selectedPages.has(i)) { selectedPages.delete(i); item.classList.remove('t-selected'); }
        else                       { selectedPages.add(i);    item.classList.add('t-selected'); }
        lastClickedPage = i;
        updatePagesToolbar();
      } else if (e.shiftKey && lastClickedPage !== null) {
        const lo = Math.min(i, lastClickedPage), hi = Math.max(i, lastClickedPage);
        for (let p = lo; p <= hi; p++) selectedPages.add(p);
        panel.querySelectorAll('.titem').forEach(t =>
          t.classList.toggle('t-selected', selectedPages.has(parseInt(t.dataset.page))));
        updatePagesToolbar();
      } else {
        clearPageSelection();
        scrollToPage(i);
      }
    });

    // ── drag-to-reorder (single or multi-page) ──
    item.addEventListener('dragstart', e => {
      // If dragging a selected page, carry all selected; else carry just this one
      const pages = selectedPages.has(i)
        ? [...selectedPages].sort((a, b) => a - b)
        : [i];
      e.dataTransfer.effectAllowed = 'move';
      e.dataTransfer.setData('text/plain', pages.join(','));
      setTimeout(() => {
        pages.forEach(p => {
          const el = panel.querySelector(`.titem[data-page="${p}"]`);
          if (el) el.classList.add('t-dragging');
        });
      }, 0);
    });
    item.addEventListener('dragend', () => {
      panel.querySelectorAll('.t-dragging,.t-drop-above,.t-drop-below').forEach(el =>
        el.classList.remove('t-dragging', 't-drop-above', 't-drop-below'));
    });
    item.addEventListener('dragover', e => {
      e.preventDefault();
      e.dataTransfer.dropEffect = 'move';
      const rect = item.getBoundingClientRect();
      const above = e.clientY < rect.top + rect.height / 2;
      item.classList.toggle('t-drop-above', above);
      item.classList.toggle('t-drop-below', !above);
    });
    item.addEventListener('dragleave', e => {
      if (!item.contains(e.relatedTarget))
        item.classList.remove('t-drop-above', 't-drop-below');
    });
    item.addEventListener('drop', e => {
      e.preventDefault();
      item.classList.remove('t-drop-above', 't-drop-below');
      const fromPages = new Set(e.dataTransfer.getData('text/plain').split(',').map(Number));
      const toPage = parseInt(item.dataset.page);
      if (fromPages.has(toPage) && fromPages.size === 1) return;
      const rect = item.getBoundingClientRect();
      const insertBefore = e.clientY < rect.top + rect.height / 2;
      reorderPages(fromPages, toPage, insertBefore);
    });

    const wrap = document.createElement('div'); wrap.className = 'tcwrap';
    const tc = document.createElement('canvas');
    tc.width = 0; tc.height = 0; // reset browser default (300×150) so render guard works
    wrap.appendChild(tc);

    // ── per-page delete button (visible on hover / selection) ──
    const delBtn = document.createElement('button');
    delBtn.className = 't-del-btn';
    delBtn.title = 'Delete this page';
    delBtn.innerHTML = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" width="10" height="10"><polyline points="3 6 5 6 21 6"/><path d="M19 6l-1 14H6L5 6"/><path d="M9 6V4h6v2"/></svg>';
    delBtn.addEventListener('click', e => {
      e.stopPropagation();
      deletePages(new Set([i]));
    });
    const lbl = document.createElement('div');
    lbl.className = 'tlbl';
    if (hasLabels && source) {
      let localPg = 0;
      for (let j = 1; j <= i; j++) { if (pageLabels[j] === source) localPg++; }
      lbl.textContent = localPg;
      lbl.title = source + ' — page ' + localPg;
    } else {
      lbl.textContent = i;
    }

    // delBtn is a child of item (position:relative), not wrap (overflow:hidden)
    item.appendChild(wrap); item.appendChild(lbl); item.appendChild(delBtn); panel.appendChild(item);
  }

  // Lazy-render thumbnails via IntersectionObserver
  const obs = new IntersectionObserver(async entries => {
    for (const entry of entries) {
      if (!entry.isIntersecting) continue;
      const item = entry.target;
      const pgNum = parseInt(item.dataset.page);
      const tc = item.querySelector('canvas');
      if (!tc || tc.width > 0) continue;
      obs.unobserve(item);
      try {
        const p = await pdf.getPage(pgNum);
        const base = p.getViewport({ scale: 1 });
        const scale = (50 * (window.devicePixelRatio || 1)) / base.width;
        const tv = p.getViewport({ scale });
        tc.width = tv.width; tc.height = tv.height;
        tc.style.width = '50px'; tc.style.height = '';
        await p.render({ canvasContext: tc.getContext('2d'), viewport: tv }).promise;
      } catch(e) { /* page may not be available yet */ }
    }
  }, { root: panel, rootMargin: '100px' });

  panel.querySelectorAll('.titem').forEach(item => obs.observe(item));
}

/* ═══════════════════════════════════════════════
   PAGE OPERATIONS
   Reorder, delete, and move pages in the PDF.
   All functions rebuild the PDF via PDFLib and
   reload — labels and selection are preserved.
═══════════════════════════════════════════════ */

// Core helper: rebuild PDF from a given page-order array (1-based original indices)
async function _rebuildPDF(order) {
  await loadPdfLib();
  const { PDFDocument } = PDFLib;
  const srcDoc = await PDFDocument.load(pdfBytes, { ignoreEncryption: true });
  const newDoc = await PDFDocument.create();
  const pages  = await newDoc.copyPages(srcDoc, order.map(p => p - 1));
  pages.forEach(p => newDoc.addPage(p));
  if (Object.keys(pageLabels).length > 0) {
    const old = { ...pageLabels };
    Object.keys(pageLabels).forEach(k => delete pageLabels[k]);
    order.forEach((origPg, idx) => { if (old[origPg]) pageLabels[idx + 1] = old[origPg]; });
  }
  const bytes = await newDoc.save();
  return new File([bytes], pdfName, { type: 'application/pdf' });
}

// Reload after a structural change, restoring labels and re-selecting pages
async function _reloadWithOrder(order, newSelectedPages) {
  const file = await _rebuildPDF(order);
  const savedLabels = { ...pageLabels };
  selectedPages.clear();
  if (newSelectedPages) newSelectedPages.forEach(p => selectedPages.add(p));
  await loadPDF(file);
  Object.assign(pageLabels, savedLabels);
  if (Object.keys(pageLabels).length > 0) buildThumbs();
  // Re-apply selection highlight (buildThumbs already read selectedPages, but do a sync pass)
  updatePagesToolbar();
}

// Drag-drop reorder: fromPages = Set, toPage = drop target, insertBefore = boolean
async function reorderPages(fromPages, toPage, insertBefore) {
  if (fromPages.has(toPage) && fromPages.size === 1) return;
  try {
    toast('Moving pages…', 2000);
    const fromArr  = [...fromPages].sort((a, b) => a - b);
    const remaining = [];
    for (let p = 1; p <= nPages; p++) { if (!fromPages.has(p)) remaining.push(p); }
    let toIdx = remaining.indexOf(toPage);
    if (toIdx === -1) toIdx = remaining.length;
    else if (!insertBefore) toIdx++;
    remaining.splice(toIdx, 0, ...fromArr);
    // Compute new positions of moved pages so we can re-select them
    const newSel = new Set(fromArr.map(p => remaining.indexOf(p) + 1));
    await _reloadWithOrder(remaining, newSel);
    const n = fromArr.length;
    toast(`✓ ${n === 1 ? 'Page ' + fromArr[0] : n + ' pages'} moved`, 2000);
  } catch (e) {
    toast('Reorder failed: ' + e.message);
    console.error('[EngDoc] reorderPages:', e);
  }
}

// Delete a set of pages (1-based)
async function deletePages(pageSet) {
  if (!pageSet.size) return;
  const remaining = [];
  for (let p = 1; p <= nPages; p++) { if (!pageSet.has(p)) remaining.push(p); }
  if (!remaining.length) { toast('Cannot delete all pages'); return; }
  try {
    const n = pageSet.size;
    toast(`Deleting ${n === 1 ? 'page' : n + ' pages'}…`, 2000);
    await _reloadWithOrder(remaining, null);
    toast(`✓ ${n === 1 ? 'Page deleted' : n + ' pages deleted'}`, 2500);
  } catch (e) {
    toast('Delete failed: ' + e.message);
    console.error('[EngDoc] deletePages:', e);
  }
}

function deleteSelectedPages() {
  if (!selectedPages.size) return;
  deletePages(new Set(selectedPages));
}

// Shift the entire selection up (delta=-1) or down (delta=+1) by one slot
async function moveSelectedPages(delta) {
  if (!selectedPages.size) return;
  const fromArr = [...selectedPages].sort((a, b) => a - b);
  if (delta === -1 && fromArr[0] === 1) return;
  if (delta === +1 && fromArr[fromArr.length - 1] === nPages) return;
  try {
    const fromSet   = new Set(fromArr);
    const remaining = [];
    for (let p = 1; p <= nPages; p++) { if (!fromSet.has(p)) remaining.push(p); }
    // Pivot: the non-selected page adjacent to the selection in the direction of movement
    const pivot = delta === -1 ? fromArr[0] - 1 : fromArr[fromArr.length - 1] + 1;
    let toIdx = remaining.indexOf(pivot);
    if (toIdx === -1) return;
    if (delta === -1) remaining.splice(toIdx, 0, ...fromArr);
    else              remaining.splice(toIdx + 1, 0, ...fromArr);
    const newSel = new Set(fromArr.map(p => remaining.indexOf(p) + 1));
    await _reloadWithOrder(remaining, newSel);
    updatePagesToolbar();
  } catch (e) {
    toast('Move failed: ' + e.message);
  }
}

function clearPageSelection() {
  selectedPages.clear();
  lastClickedPage = null;
  document.querySelectorAll('.titem.t-selected').forEach(el => el.classList.remove('t-selected'));
  updatePagesToolbar();
}

function updatePagesToolbar() {
  const toolbar  = document.getElementById('pages-toolbar');
  const countEl  = document.getElementById('pages-sel-count');
  if (!toolbar) return;
  if (selectedPages.size === 0) {
    toolbar.classList.add('hidden');
    return;
  }
  toolbar.classList.remove('hidden');
  const n = selectedPages.size;
  countEl.textContent = n === 1 ? '1 page selected' : `${n} pages selected`;
  // Disable move-up if selection starts at page 1, move-down if it ends at last page
  const sorted = [...selectedPages].sort((a, b) => a - b);
  document.getElementById('ptb-up').disabled   = sorted[0] === 1;
  document.getElementById('ptb-down').disabled = sorted[sorted.length - 1] === nPages;
}

/* ═══════════════════════════════════════════════
   NAVIGATION
═══════════════════════════════════════════════ */
function scrollToPage(n) {
  const el = document.getElementById(`pw-${n}`); if (!el) return;
  el.scrollIntoView({ behavior: 'smooth', block: 'start' });
  curPg = n; document.getElementById('pgi').value = n;
  document.querySelectorAll('.titem').forEach(t =>
    t.classList.toggle('active', parseInt(t.dataset.page) === n));
}
function changePage(d) { scrollToPage(Math.max(1, Math.min(nPages, curPg + d))); }
function jumpTo(v) { const p = parseInt(v); if (p >= 1 && p <= nPages) scrollToPage(p); }

let _zoomTimer = null;
async function applyZoom(val) {
  if (!pdf) return;
  // Update zoom value and labels immediately for responsiveness
  if (val === 'fit') {
    const page1 = _pageCache[1] || await pdf.getPage(1);
    if (!_pageCache[1]) _pageCache[1] = page1;
    const w = document.getElementById('viewer').clientWidth - 64;
    zoom = w / page1.getViewport({ scale: 1 }).width;
  } else {
    zoom = parseFloat(val);
  }
  const pct = Math.round(zoom * 100) + '%';
  const sbZoom = document.getElementById('sb-zoom');
  if (sbZoom) sbZoom.innerHTML = '<div class="sbdot b"></div>' + pct;
  const mobLabel = document.getElementById('mob-zoom-label');
  if (mobLabel) mobLabel.textContent = pct;

  // Debounce the actual re-render — 150ms collapses rapid changes
  clearTimeout(_zoomTimer);
  _zoomTimer = setTimeout(() => rerenderAll(), 250);
}

/* ═══════════════════════════════════════════════
   TOOL / Color SELECTION
═══════════════════════════════════════════════ */
function setTool(t) {
  tool = t;
  document.querySelectorAll('[id^="t-"]').forEach(b => {
    b.classList.remove('active');
    b.classList.remove('eraser-active');
  });
  const erBtn = document.getElementById('t-erase');
  if (t === 'erase') {
    erBtn.classList.add('active');
  } else {
    erBtn.classList.add('eraser-active');
    document.getElementById('t-' + t)?.classList.add('active');
  }

  document.getElementById('sb-tool').textContent = typeLabels[t] || t;

  // In select mode the overlay is completely transparent so text spans get events.
  // We also set cursor:text on the page wrappers themselves so there's no
  // visual gap between the overlay (transparent) and the canvas (no cursor).
  document.querySelectorAll('.aoverlay').forEach(o => {
    if (t === 'select') {
      // Active — receives mousedown for custom selection engine
      o.style.pointerEvents = '';
      o.style.cursor = '';
      o.className = 'aoverlay active cur-crosshair';
    } else if (t === 'pan') {
      // Pan mode: overlay stays active so we can detect clicks on annotations for dragging.
      // Empty-space clicks scroll the viewer (handled in overlay mousedown below).
      o.style.pointerEvents = '';
      o.style.cursor = '';
      o.className = 'aoverlay active cur-pan';
    } else {
      o.style.pointerEvents = '';
      o.style.cursor = '';
      o.className = 'aoverlay active';
      if (['highlight','rect','rectfill','strike','pen','arrow','line',
           'measure','texthighlight','cloud','area','tableextract'].includes(t)) o.classList.add('cur-cross');
      else if (t === 'text')    o.classList.add('cur-text');
      else if (t === 'erase')   o.classList.add('cur-erase');
      else if (t === 'zoombox') o.classList.add('cur-zoombox');
    }
  });

  // Page wrappers: text cursor in select mode so it shows over the canvas too
  document.querySelectorAll('.pwrap').forEach(pw => {
    pw.style.cursor = t === 'select' ? 'crosshair' : '';
  });

  // Clear any active selection when switching away from select
  if (tool === 'select' && t !== 'select') clearTextSelection();

  refreshAnnotPointerEvents();
}

// Controls which annotation DOM elements accept pointer events.
// Rules:
//   pan   → everything is none (overlay itself is pass-through)
//   erase → div-based annots: pointer-events:all
//            SVG-based (pen/arrow): wrapper stays none; path/line gets pointer-events:stroke
//            so only clicking the actual drawn line triggers deletion
//   other → only notes/text labels need pointer-events for context menu
function refreshAnnotPointerEvents() {
  document.querySelectorAll('[data-aid]').forEach(el => {
    const isSvgWrap  = el.classList.contains('asvg-wrap');
    const isTextable = el.classList.contains('an') || el.classList.contains('atxt');

    if (tool === 'select') {
      // Select mode: annotations non-interactive, overlay handles text selection
      el.style.pointerEvents = 'none';
      el.style.cursor = '';
      if (isSvgWrap) el.querySelectorAll('path, line, polyline, polygon').forEach(s => { s.style.pointerEvents = 'none'; });
    } else if (tool === 'pan') {
      // Move overlays (.ann-move-overlay) handle interaction — annotation elements themselves are pass-through
      el.style.pointerEvents = 'none';
      el.style.cursor = '';
      if (isSvgWrap) el.querySelectorAll('path, line, polyline, polygon').forEach(s => {
        s.style.pointerEvents = 'none'; s.style.cursor = '';
      });
    } else if (tool === 'erase') {
      if (isSvgWrap) {
        el.style.pointerEvents = 'none';
        el.querySelectorAll('path, line').forEach(s => {
          s.style.pointerEvents = 'stroke';
          s.style.cursor = 'crosshair';
        });
      } else {
        el.style.pointerEvents = 'all';
        el.style.cursor = 'crosshair';
      }
    } else {
      // Drawing tools — only interactive annotations stay clickable
      if (isSvgWrap) {
        el.style.pointerEvents = 'none';
        el.querySelectorAll('path, line').forEach(s => s.style.pointerEvents = 'none');
      } else {
        el.style.pointerEvents = isTextable ? 'all' : 'none';
        el.style.cursor = isTextable ? 'pointer' : '';
      }
    }
  });

  // Leader tip handles: only interactive in pan mode
  const isPan = tool === 'pan';
  document.querySelectorAll('[data-leader-handle]').forEach(h => {
    h.style.pointerEvents = isPan ? 'all' : 'none';
    h.style.cursor = isPan ? 'move' : '';
  });
}

function setColor(c) {
  const a = _spTarget();
  if (a) {
    a.Color = c; syncAnnots();
  } else {
    Color = c;
    const swatch = document.getElementById('style-trigger-swatch');
    if (swatch) swatch.style.background = colorHex(c);
  }
  // If the style popover is open, refresh its preset swatches' active state
  const presetMap = { yellow: 'cy', green: 'cg', red: 'cr', blue: 'cb', black: 'ck' };
  document.querySelectorAll('#sp-body .rcsw').forEach(s => {
    const cls = Object.values(presetMap).find(k => s.classList.contains(k));
    s.classList.toggle('active', cls === presetMap[c]);
  });
}

function setFontSize(v) {
  const n = parseInt(v) || 12;
  const a = _spTarget();
  if (a) { a.fontSize = n; syncAnnots(); } else { fontSize = n; }
}

function setOpacity(v) {
  const n = parseInt(v) || 80;
  const a = _spTarget();
  if (a) { a.opacity = n; syncAnnots(); } else { annotOpacity = n; }
}

function setTextBox(on) {
  const a = _spTarget();
  if (a) { a.box = on; syncAnnots(); } else { textBoxDefault = on; }
  _spCommit();
}

function setTextAlign(v) {
  const a = _spTarget();
  if (a) { a.textAlign = v; syncAnnots(); } else { textAlignDefault = v; }
  document.getElementById('sp-halign')?.querySelectorAll('.sp-preset-btn').forEach(b =>
    b.classList.toggle('active', b.dataset.v === v));
  _spCommit();
}

function setVAlign(v) {
  const a = _spTarget();
  if (a) { a.vAlign = v; syncAnnots(); } else { vAlignDefault = v; }
  document.getElementById('sp-valign')?.querySelectorAll('.sp-preset-btn').forEach(b =>
    b.classList.toggle('active', b.dataset.v === v));
  _spCommit();
}

/* ═══════════════════════════════════════════════
   DRAWING EVENTS
═══════════════════════════════════════════════ */
function attachEvents(ov, pageNum, _vpInitial) {
  const viewer = document.getElementById('viewer');
  // Always read current viewport from pageViewports — the captured vp goes stale on zoom change
  const getLiveVp = () => pageViewports[pageNum] || _vpInitial || { width: 800, height: 1000 };

  // Attach custom text selection handler for this page
  attachSelectEvents(ov, pageNum);

  ov.addEventListener('mousedown', e => {
    const vp = getLiveVp(); // fresh every event
    if (e.button !== 0) return;
    hideCtx();

    // Select tool handled by attachSelectEvents above
    if (tool === 'select') return;

    // ── PAN: always scrolls — .ann-move-overlay stopPropagation prevents this when dragging annotation ──
    if (tool === 'pan') {
      panDragging = true;
      panStart = { x: e.clientX, y: e.clientY };
      panScrollStart = { left: viewer.scrollLeft, top: viewer.scrollTop };
      ov.classList.add('panning');
      e.preventDefault();
      return;
    }

    if (tool === 'erase') return;

    const r = ov.getBoundingClientRect();
    // A capturing mousedown listener (see SNAP TO EXISTING ANNOTATION / DRAWING
    // GEOMETRY below) computes a snapped point for arrow/note/text/measure/line
    // and stashes it here, since e.clientX/Y themselves are read-only.
    const ox = e._snapX !== undefined ? e._snapX - r.left : e.clientX - r.left;
    const oy = e._snapY !== undefined ? e._snapY - r.top  : e.clientY - r.top;

    // ── TEXT: always click-only — show popover immediately ──
    if (tool === 'text') {
      const px = ox / vp.width * 100, py = oy / vp.height * 100;
      showTxtPop(e.clientX, e.clientY, (txt, emmaFields) => {
        pushAnnot({ id: nextId(), pageNum, type: tool, x: px, y: py,
          text: txt, Color, fontSize, box: textBoxDefault,
          textAlign: textAlignDefault, vAlign: vAlignDefault, ...emmaFields });
      });
      return;
    }

    // ── MEASURE: click-click-click state machine (intercept before drag setup) ──
    if (tool === 'measure') {
      const cx = ox, cy = oy;
      if (measureState === 'idle' || measurePageNum !== pageNum) {
        // First click — set P1
        measureState = 'firstSet';
        measureP1 = { x: cx, y: cy };
        measurePageNum = pageNum;
        measureVp = vp;
        if (measureLiveSvg) { measureLiveSvg.remove(); measureLiveSvg = null; }
        measureLiveSvg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
        measureLiveSvg.style.cssText = 'position:absolute;top:0;left:0;overflow:visible;pointer-events:none;z-index:10';
        measureLiveSvg.setAttribute('width', vp.width); measureLiveSvg.setAttribute('height', vp.height);
        const dot1 = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
        dot1.setAttribute('cx', cx); dot1.setAttribute('cy', cy); dot1.setAttribute('r', 4);
        dot1.setAttribute('fill', '#7c3aed'); dot1.setAttribute('stroke', '#fff'); dot1.setAttribute('stroke-width', 1.5);
        const ml = document.createElementNS('http://www.w3.org/2000/svg', 'line');
        ml.id = 'mline';
        ml.setAttribute('x1', cx); ml.setAttribute('y1', cy); ml.setAttribute('x2', cx); ml.setAttribute('y2', cy);
        ml.setAttribute('stroke', '#7c3aed'); ml.setAttribute('stroke-width', 1.5); ml.setAttribute('stroke-dasharray', '5,3');
        const dot2 = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
        dot2.id = 'mdot2';
        dot2.setAttribute('cx', cx); dot2.setAttribute('cy', cy); dot2.setAttribute('r', 4);
        dot2.setAttribute('fill', '#7c3aed'); dot2.setAttribute('stroke', '#fff'); dot2.setAttribute('stroke-width', 1.5);
        dot2.setAttribute('visibility', 'hidden');
        const mt = document.createElementNS('http://www.w3.org/2000/svg', 'text');
        mt.id = 'mlabel';
        mt.setAttribute('fill', '#7c3aed'); mt.setAttribute('font-size', '11');
        mt.setAttribute('font-family', 'DM Mono, monospace'); mt.setAttribute('text-anchor', 'middle');
        measureLiveSvg.appendChild(ml); measureLiveSvg.appendChild(dot1);
        measureLiveSvg.appendChild(dot2); measureLiveSvg.appendChild(mt);
        ov.appendChild(measureLiveSvg);
        toast('Click second point to set end of measurement', 2200);
        e.stopPropagation(); return;
      }
      if (measureState === 'firstSet') {
        // Second click — lock P2, prompt for third click to commit
        // Apply shift-snap if held
        let cx2 = cx, cy2 = cy;
        if (e.shiftKey && measureP1) {
          const dx = Math.abs(cx - measureP1.x), dy = Math.abs(cy - measureP1.y);
          if (dx > dy) cy2 = measureP1.y; else cx2 = measureP1.x;
        }
        measureState = 'secondSet';
        measureP2 = { x: cx2, y: cy2 };
        const ml2 = measureLiveSvg.querySelector('#mline, line');
        if (ml2) { ml2.setAttribute('x2', cx2); ml2.setAttribute('y2', cy2); ml2.setAttribute('stroke-dasharray', 'none'); }
        const d2 = measureLiveSvg.querySelector('#mdot2');
        if (d2) { d2.setAttribute('cx', cx2); d2.setAttribute('cy', cy2); d2.setAttribute('visibility', 'visible'); }
        const pxDist = Math.hypot(cx2 - measureP1.x, cy2 - measureP1.y);
        const label = measureScale
          ? `${(pxDist / measureScale.pxPerUnit / zoom).toFixed(2)} ${measureScale.unit}`
          : `${Math.round(pxDist)} px`;
        const lbl = measureLiveSvg.querySelector('#mlabel, text');
        if (lbl) {
          lbl.setAttribute('x', (measureP1.x + cx2) / 2);
          lbl.setAttribute('y', (measureP1.y + cy2) / 2 - 8);
          lbl.textContent = label;
        }
        document.getElementById('sb-measure').textContent = '⬌ ' + label;
        document.getElementById('sb-measure').classList.add('visible');
        toast('Click once more to place measurement', 2200);
        e.stopPropagation(); return;
      }
      if (measureState === 'secondSet') {
        // Third click — commit
        if (measureLiveSvg) { measureLiveSvg.remove(); measureLiveSvg = null; }
        document.getElementById('sb-measure').classList.remove('visible');
        const pxDist = Math.hypot(measureP2.x - measureP1.x, measureP2.y - measureP1.y);
        lastMeasurePx = pxDist;
        document.getElementById('scale-px').value = Math.round(pxDist);
        const label = measureScale
          ? `${(pxDist / measureScale.pxPerUnit / zoom).toFixed(2)} ${measureScale.unit}`
          : `${Math.round(pxDist)} px`;
        const x1 = measureP1.x / vp.width * 100, y1 = measureP1.y / vp.height * 100;
        const x2 = measureP2.x / vp.width * 100, y2 = measureP2.y / vp.height * 100;
        pushAnnot({ id: nextId(), pageNum, type: 'measure', x1, y1, x2, y2, Color, label,
          pxDist, zoom, unit: measureScale?.unit || 'px' });
        measureState = 'idle'; measureP1 = null; measureP2 = null; measurePageNum = null;
        if (!measureScale) toast('Tip: click ⚖ Scale to calibrate real-world units', 4000);
        e.stopPropagation(); return;
      }
      return;
    }

    // ── DRAG TOOLS ──
    drawing = true; origin = { x: ox, y: oy };

    // ── ARROW: live SVG preview ──
    if (tool === 'arrow') {
      liveSvg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
      liveSvg.style.cssText = 'position:absolute;top:0;left:0;overflow:visible;pointer-events:none;z-index:10';
      liveSvg.setAttribute('width', vp.width); liveSvg.setAttribute('height', vp.height);
      const c = colorHex(Color);
      const defs = document.createElementNS('http://www.w3.org/2000/svg', 'defs');
      const marker = document.createElementNS('http://www.w3.org/2000/svg', 'marker');
      marker.setAttribute('id', `live-arr-${pageNum}`); marker.setAttribute('viewBox', '0 0 10 10');
      marker.setAttribute('refX', '9'); marker.setAttribute('refY', '5');
      marker.setAttribute('markerWidth', '6'); marker.setAttribute('markerHeight', '6');
      marker.setAttribute('orient', 'auto-start-reverse');
      const ap = document.createElementNS('http://www.w3.org/2000/svg', 'path');
      ap.setAttribute('d', 'M 0 0 L 10 5 L 0 10 z'); ap.setAttribute('fill', c);
      marker.appendChild(ap); defs.appendChild(marker); liveSvg.appendChild(defs);
      const line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
      line.setAttribute('x1', ox); line.setAttribute('y1', oy);
      line.setAttribute('x2', ox + 1); line.setAttribute('y2', oy);
      line.setAttribute('stroke', c); line.setAttribute('stroke-width', strokeW());
      line.setAttribute('vector-effect', 'non-scaling-stroke');
      line.setAttribute('marker-end', `url(#live-arr-${pageNum})`);
      const liveArrowDash = dashArrayFor(lineStyle, strokeW());
      if (liveArrowDash) { line.setAttribute('stroke-dasharray', liveArrowDash); line.setAttribute('stroke-linecap', lineStyle === 'dotted' ? 'round' : 'butt'); }
      liveSvg.appendChild(line);
      ov.appendChild(liveSvg);
      return;
    }

    if (tool === 'pen' || tool === 'texthighlight') {
      penPoints = [{ x: ox, y: oy }];
      liveSvg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
      liveSvg.style.cssText = 'position:absolute;top:0;left:0;overflow:visible;pointer-events:none;z-index:10';
      liveSvg.setAttribute('width', vp.width);
      liveSvg.setAttribute('height', vp.height);
      const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
      path.setAttribute('d', `M${ox},${oy}`);
      path.setAttribute('fill', 'none');
      if (tool === 'texthighlight') {
        path.setAttribute('stroke', colorRgba(Color));
        path.setAttribute('stroke-width', 14);
        path.setAttribute('opacity', '0.6');
        liveSvg.style.mixBlendMode = 'multiply';
      } else {
        path.setAttribute('stroke', colorHex(Color));
        path.setAttribute('stroke-width', strokeW());
      }
      path.setAttribute('stroke-linecap', 'round');
      path.setAttribute('stroke-linejoin', 'round');
      liveSvg.appendChild(path);
      ov.appendChild(liveSvg);
      return;
    }

    liveEl = document.createElement('div');
    liveEl.style.cssText = 'position:absolute;pointer-events:none;z-index:10';
    if (tool === 'highlight') {
      liveEl.className = 'ah';
      liveEl.style.background = colorRgba(Color);
      liveEl.style.mixBlendMode = 'multiply';
    } else if (tool === 'rect') {
      liveEl.className = 'ar';
      liveEl.style.borderStyle = lineStyle === 'dashed' ? 'dashed' : lineStyle === 'dotted' ? 'dotted' : 'solid';
      liveEl.style.borderColor = colorHex(Color);
      liveEl.style.background = colorHex(Color) + '11';
    } else if (tool === 'tableextract') {
      liveEl.style.border = '2px dashed #2563eb';
      liveEl.style.background = '#2563eb11';
    } else if (tool === 'rectfill') {
      liveEl.style.background = colorHex(Color);
      liveEl.style.opacity = (annotOpacity / 100).toFixed(2);
      liveEl.style.borderRadius = '1px';
    } else if (tool === 'circle') {
      // Circle preview: SVG ellipse matching committed render
      liveEl = null;
      const cc = colorHex(Color);
      liveSvg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
      liveSvg.style.cssText = 'position:absolute;top:0;left:0;overflow:visible;pointer-events:none;z-index:10';
      liveSvg.setAttribute('width', vp.width); liveSvg.setAttribute('height', vp.height);
      const ce = document.createElementNS('http://www.w3.org/2000/svg', 'ellipse');
      ce.setAttribute('cx', ox); ce.setAttribute('cy', oy);
      ce.setAttribute('rx', '0'); ce.setAttribute('ry', '0');
      ce.setAttribute('fill', cc + '18'); ce.setAttribute('stroke', cc);
      ce.setAttribute('stroke-width', strokeW()); ce.setAttribute('vector-effect', 'non-scaling-stroke');
      const liveCircleDash = dashArrayFor(lineStyle, strokeW());
      if (liveCircleDash) { ce.setAttribute('stroke-dasharray', liveCircleDash); ce.setAttribute('stroke-linecap', lineStyle === 'dotted' ? 'round' : 'butt'); }
      liveSvg.appendChild(ce);
      ov.appendChild(liveSvg);
      return;
    } else if (tool === 'strike') {
      // Strike preview: center line through the selection, matching committed render
      const sc = colorHex(Color, 'rose');
      liveEl.style.background = `linear-gradient(transparent calc(50% - 1.5px),${sc} calc(50% - 1.5px),${sc} calc(50% + 1.5px),transparent calc(50% + 1.5px))`;
    } else if (tool === 'line') {
      // Line preview via SVG
      liveSvg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
      liveSvg.style.cssText = 'position:absolute;top:0;left:0;overflow:visible;pointer-events:none;z-index:10';
      liveSvg.setAttribute('width', vp.width); liveSvg.setAttribute('height', vp.height);
      const lLine = document.createElementNS('http://www.w3.org/2000/svg', 'line');
      lLine.setAttribute('x1', ox); lLine.setAttribute('y1', oy);
      lLine.setAttribute('x2', ox); lLine.setAttribute('y2', oy);
      lLine.setAttribute('stroke', colorHex(Color)); lLine.setAttribute('stroke-width', strokeW());
      lLine.setAttribute('stroke-linecap', 'round');
      const liveLineDash = dashArrayFor(lineStyle, strokeW());
      if (liveLineDash) lLine.setAttribute('stroke-dasharray', liveLineDash);
      liveSvg.appendChild(lLine);
      ov.appendChild(liveSvg);
      liveEl = null;
      return;
    } else if (tool === 'cloud') {
      // Cloud: real scalloped SVG preview — discard the pre-created div
      liveEl = null;
      const cc = colorHex(Color);
      liveSvg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
      liveSvg.style.cssText = 'position:absolute;top:0;left:0;overflow:visible;pointer-events:none;z-index:10';
      liveSvg.setAttribute('width', vp.width); liveSvg.setAttribute('height', vp.height);
      const cp = document.createElementNS('http://www.w3.org/2000/svg', 'path');
      cp.setAttribute('fill', cc + '18'); cp.setAttribute('stroke', cc);
      cp.setAttribute('stroke-width', '2'); cp.setAttribute('vector-effect', 'non-scaling-stroke');
      cp.setAttribute('stroke-linejoin', 'round'); cp.setAttribute('d', 'M' + ox + ' ' + oy);
      liveSvg.appendChild(cp);
      ov.appendChild(liveSvg);
      return;
    }
    if (liveEl) {
      liveEl.style.left = ox + 'px'; liveEl.style.top = oy + 'px';
      liveEl.style.width = '0'; liveEl.style.height = '0';
      ov.appendChild(liveEl);
    }
  });

  ov.addEventListener('mousemove', e => {
    // Pan is handled by the document-level mousemove — return immediately so the
    // overlay does zero work during a pan drag (vp lookup, snap ring, etc. all skipped).
    if (tool === 'pan') return;
    const vp = getLiveVp(); // only needed for drawing tools

    const r = ov.getBoundingClientRect();
    const mx = e.clientX - r.left, my = e.clientY - r.top;

    // Measure rubber-band — runs regardless of 'drawing' flag (measure uses clicks not drag)
    if (tool === 'measure' && measureLiveSvg && measureState === 'firstSet') {
      // Shift = snap to nearest orthogonal (H or V); otherwise snap to the
      // nearest annotation anchor / drawn vertex / drawn edge, if any is close.
      let snapX = mx, snapY = my;
      if (e.shiftKey && measureP1) {
        const dx = Math.abs(mx - measureP1.x), dy = Math.abs(my - measureP1.y);
        if (dx > dy) { snapY = measureP1.y; } else { snapX = measureP1.x; }
      } else {
        const snap = findSnapPoint(mx, my, pageNum, vp);
        if (snap) { snapX = snap.sx; snapY = snap.sy; updateSnapMarker(e.clientX, e.clientY, true, snap.type); }
        else { updateSnapMarker(0, 0, false); }
      }
      const ml2 = measureLiveSvg.querySelector('line');
      if (ml2) { ml2.setAttribute('x2', snapX); ml2.setAttribute('y2', snapY); }
      const pxDist = Math.hypot(snapX - measureP1.x, snapY - measureP1.y);
      const label = measureScale
        ? `${(pxDist / measureScale.pxPerUnit / zoom).toFixed(2)} ${measureScale.unit}`
        : `${Math.round(pxDist)} px`;
      const lbl = measureLiveSvg.querySelector('text');
      if (lbl) {
        lbl.setAttribute('x', (measureP1.x + snapX) / 2);
        lbl.setAttribute('y', (measureP1.y + snapY) / 2 - 8);
        lbl.textContent = label;
      }
      document.getElementById('sb-measure').textContent = '⬌ ' + label + (e.shiftKey ? ' [snap]' : '');
      document.getElementById('sb-measure').classList.add('visible');
      return;
    }

    if (!drawing) return;

    // Arrow: update live preview line (snaps to annotation anchors / drawn geometry)
    if (tool === 'arrow' && liveSvg && drawing) {
      let ex = mx, ey = my;
      const snap = findSnapPoint(mx, my, pageNum, vp);
      if (snap) { ex = snap.sx; ey = snap.sy; updateSnapMarker(e.clientX, e.clientY, true, snap.type); }
      else updateSnapMarker(0, 0, false);
      const line = liveSvg.querySelector('line');
      if (line) { line.setAttribute('x2', ex); line.setAttribute('y2', ey); }
      return;
    }
    // Line: update live preview (shift to constrain to axis; otherwise snap)
    if (tool === 'line' && liveSvg && drawing) {
      let ex = mx, ey = my;
      if (e.shiftKey) {
        const dx = Math.abs(mx - origin.x), dy = Math.abs(my - origin.y);
        if (dx > dy * 2) ey = origin.y;
        else if (dy > dx * 2) ex = origin.x;
        else { const d = Math.min(dx, dy); ex = origin.x + (mx > origin.x ? d : -d); ey = origin.y + (my > origin.y ? d : -d); }
      } else {
        const snap = findSnapPoint(mx, my, pageNum, vp);
        if (snap) { ex = snap.sx; ey = snap.sy; updateSnapMarker(e.clientX, e.clientY, true, snap.type); }
        else updateSnapMarker(0, 0, false);
      }
      const ln = liveSvg.querySelector('line');
      if (ln) { ln.setAttribute('x2', ex); ln.setAttribute('y2', ey); }
      return;
    }
    if ((tool === 'pen' || tool === 'texthighlight') && liveSvg) {
      penPoints.push({ x: mx, y: my });
      const d = penPoints.map((p, i) => (i === 0 ? 'M' : 'L') + p.x + ',' + p.y).join(' ');
      liveSvg.querySelector('path').setAttribute('d', d);
      return;
    }
    // Cloud: update the real scalloped SVG preview
    if (tool === 'cloud' && liveSvg && drawing) {
      const minX = Math.min(mx, origin.x), minY = Math.min(my, origin.y);
      const maxX = Math.max(mx, origin.x), maxY = Math.max(my, origin.y);
      if (maxX - minX > 4 && maxY - minY > 4) {
        const r = Math.min(maxX - minX, maxY - minY) * 0.08;
        const cp = liveSvg.querySelector('path');
        if (cp) cp.setAttribute('d', makeCloudPath(minX, minY, maxX, maxY, r));
      }
      return;
    }
    // Circle: update live ellipse preview
    if (tool === 'circle' && liveSvg && drawing) {
      let w = mx - origin.x, h = my - origin.y;
      if (e.shiftKey) { const s = Math.max(Math.abs(w), Math.abs(h)); w = w < 0 ? -s : s; h = h < 0 ? -s : s; }
      const cx = origin.x + w / 2, cy = origin.y + h / 2;
      const rx = Math.abs(w) / 2, ry = Math.abs(h) / 2;
      const ce = liveSvg.querySelector('ellipse');
      if (ce) { ce.setAttribute('cx', cx); ce.setAttribute('cy', cy); ce.setAttribute('rx', rx); ce.setAttribute('ry', ry); }
      return;
    }
    if (!liveEl) return;
    const lx = Math.min(mx, origin.x), ly = Math.min(my, origin.y);
    const lw = Math.abs(mx - origin.x), lh = Math.abs(my - origin.y);
    liveEl.style.left = lx + 'px'; liveEl.style.top = ly + 'px';
    liveEl.style.width = lw + 'px'; liveEl.style.height = lh + 'px';
  });

  ov.addEventListener('mouseup', e => {
    const vp = getLiveVp(); // always current
    // End pan
    if (tool === 'pan' && panDragging) {
      panDragging = false; panStart = null; panScrollStart = null;
      ov.classList.remove('panning');
      scheduleRender(); // render newly visible pages
      return;
    }
    if (!drawing) return; drawing = false;
    const r = ov.getBoundingClientRect();
    const mx = e.clientX - r.left, my = e.clientY - r.top;

    // Arrow: commit on mouseup
    if (tool === 'arrow' && liveSvg) {
      liveSvg.remove(); liveSvg = null;
      let ex = mx, ey = my;
      const snap = findSnapPoint(mx, my, pageNum, vp);
      if (snap) { ex = snap.sx; ey = snap.sy; }
      if (Math.abs(ex - origin.x) < 3 && Math.abs(ey - origin.y) < 3) return;
      const x1 = origin.x / vp.width * 100, y1 = origin.y / vp.height * 100;
      const x2 = ex / vp.width * 100, y2 = ey / vp.height * 100;
      pushAnnot({ id: nextId(), pageNum, type: 'arrow', x1, y1, x2, y2, Color, sw: strokeW(), lineStyle });
      return;
    }

    if ((tool === 'pen' || tool === 'texthighlight') && liveSvg) {
      liveSvg.remove(); liveSvg = null;
      if (penPoints.length < 3) { penPoints = []; return; }
      pushAnnot({
        id: nextId(), pageNum, type: tool,
        points: penPoints.map(p => ({ x: p.x / vp.width, y: p.y / vp.height })),
        Color, sw: tool === 'texthighlight' ? 14 : strokeW(),
        emmaExclude: tool === 'texthighlight' ? true : false
      });
      penPoints = [];
      return;
    }

    // Line commit (SVG tool — handled before liveEl cleanup)
    if (tool === 'line' && liveSvg) {
      liveSvg.remove(); liveSvg = null;
      let ex = mx, ey = my;
      if (e.shiftKey) {
        const adx = Math.abs(mx - origin.x), ady = Math.abs(my - origin.y);
        if (adx > ady * 2) ey = origin.y;
        else if (ady > adx * 2) ex = origin.x;
        else { const d = Math.min(adx, ady); ex = origin.x + (mx > origin.x ? d : -d); ey = origin.y + (my > origin.y ? d : -d); }
      } else {
        const snap = findSnapPoint(mx, my, pageNum, vp);
        if (snap) { ex = snap.sx; ey = snap.sy; }
      }
      if (Math.hypot(ex - origin.x, ey - origin.y) < 3) return;
      const lx1 = origin.x / vp.width * 100, ly1 = origin.y / vp.height * 100;
      const lx2 = ex / vp.width * 100,       ly2 = ey / vp.height * 100;
      pushAnnot({ id: nextId(), pageNum, type: 'line', x1: lx1, y1: ly1, x2: lx2, y2: ly2, Color, sw: strokeW(), lineStyle });
      return;
    }

    if (liveEl) { liveEl.remove(); liveEl = null; }

    const x  = Math.min(mx, origin.x) / vp.width  * 100;
    const y  = Math.min(my, origin.y) / vp.height * 100;
    const w  = Math.abs(mx - origin.x) / vp.width  * 100;
    const h  = Math.abs(my - origin.y) / vp.height * 100;

    if (tool === 'tableextract') {
      if (w < 1 || h < 1) return;
      openTableExtractModal(pageNum, x, y, w, h);
    } else if (tool === 'strike') {
      if (w < 0.5 || h < 0.5) return;
      pushAnnot({ id: nextId(), pageNum, type: 'strike', x, y, w, h, Color });
    } else if (tool === 'highlight' || tool === 'rect') {
      if (w < 0.3 || h < 0.3) return;
      pushAnnot(tool === 'rect'
        ? { id: nextId(), pageNum, type: tool, x, y, w, h, Color, lineStyle }
        : { id: nextId(), pageNum, type: tool, x, y, w, h, Color });
    } else if (tool === 'rectfill') {
      if (w < 0.3 || h < 0.3) return;
      pushAnnot({ id: nextId(), pageNum, type: 'rectfill', x, y, w, h, Color, opacity: annotOpacity });
    } else if (tool === 'cloud') {
      if (w < 0.5 || h < 0.5) return;
      pushAnnot({ id: nextId(), pageNum, type: 'cloud', x, y, w, h, Color });
    } else if (tool === 'circle') {
      if (liveSvg) { liveSvg.remove(); liveSvg = null; }
      let rw = mx - origin.x, rh = my - origin.y;
      if (e.shiftKey) { const s = Math.max(Math.abs(rw), Math.abs(rh)); rw = rw < 0 ? -s : s; rh = rh < 0 ? -s : s; }
      const cx = Math.min(origin.x, origin.x + rw) / vp.width * 100;
      const cy = Math.min(origin.y, origin.y + rh) / vp.height * 100;
      const cw = Math.abs(rw) / vp.width * 100;
      const ch = Math.abs(rh) / vp.height * 100;
      if (cw < 0.3 || ch < 0.3) return;
      pushAnnot({ id: nextId(), pageNum, type: 'circle', x: cx, y: cy, w: cw, h: ch, Color, sw: strokeW(), lineStyle });
    }
  });

  // Stop pan if mouse leaves overlay mid-drag
  ov.addEventListener('mouseleave', () => {
    if (tool === 'pan' && panDragging) {
      panDragging = false; panStart = null; panScrollStart = null;
      ov.classList.remove('panning');
    }
  });
}


/* ═══════════════════════════════════════════════
   ANNOTATION DATA MANAGEMENT — UNDO/REDO HISTORY
   Each pushAnnot snapshot: {annots:[...], emmaRows:{...}}
   Max 50 states to bound memory usage.
═══════════════════════════════════════════════ */
let history = [];   // array of snapshots
let historyIdx = -1;
const MAX_HISTORY = 50;

function snapshotState() {
  // Trim redo states ahead of current index
  history = history.slice(0, historyIdx + 1);
  history.push({ annots: JSON.parse(JSON.stringify(annots)), emmaRows: JSON.parse(JSON.stringify(emmaRows)) });
  if (history.length > MAX_HISTORY) history.shift();
  historyIdx = history.length - 1;
  updateUndoRedoButtons();
}

function updateUndoRedoButtons() {
  const redoBtn = document.getElementById('redo-btn');
  if (redoBtn) redoBtn.style.opacity = historyIdx < history.length - 1 ? '1' : '0.4';
}

// Legacy 'note' annotations (sticky note with fixed leader arrow + reply
// thread) are folded into 'text' (plain box with a drag-anywhere edge arrow).
// Converts in place on load so no 'note'-typed annotation survives into a
// running session — reply threads are dropped (feature removed), the fixed
// leaderX/leaderY tip is kept and bucketed onto the nearest box edge.
function migrateLegacyNoteAnnot(a) {
  if (a.type !== 'note') return a;
  const out = { ...a, type: 'text' };
  delete out.replies;
  if (out.leaderX !== undefined && out.leaderY !== undefined) {
    const dx = out.leaderX - out.x, dy = out.leaderY - out.y;
    out.leaderEdge = Math.abs(dx) > Math.abs(dy) ? (dx > 0 ? 'right' : 'left') : (dy > 0 ? 'bottom' : 'top');
  }
  if (out.textAlign === undefined) out.textAlign = 'center';
  if (out.vAlign === undefined) out.vAlign = 'center';
  if (out.box === undefined) out.box = true;
  return out;
}
// Legacy 'textbox' and 'callout' annotations (hidden, keyboard/ribbon-
// inaccessible tools whose creation flow never actually worked) are folded
// into 'text' the same way 'note' was — box styling and the leader arrow
// (callout only; its leader always ran from the box's bottom edge) both map
// directly onto text's existing box/leaderEdge fields.
function migrateLegacyTextboxCalloutAnnot(a) {
  if (a.type !== 'textbox' && a.type !== 'callout') return a;
  const out = { ...a, type: 'text', box: true };
  if (out.textAlign === undefined) out.textAlign = 'center';
  if (out.vAlign === undefined) out.vAlign = 'center';
  if (a.type === 'callout') {
    delete out.lx; delete out.ly;
    if (a.lx !== undefined && a.ly !== undefined) {
      out.leaderEdge = 'bottom';
      out.leaderX = a.lx;
      out.leaderY = a.ly;
    }
  }
  return out;
}
function migrateLegacyAnnots(list) {
  return (list || []).map(migrateLegacyNoteAnnot).map(migrateLegacyTextboxCalloutAnnot);
}

function pushAnnot(a) {
  if (!a.author) a.author = currentAuthor || 'Unknown';
  if (!a.ts) a.ts = new Date().toISOString();
  annots.push(a);
  snapshotState();
  syncAnnots(); updateAnnotPanel(); updateStatusCount(); updateEmmaRegister();
}

function deleteAnnotById(id) {
  delete emmaRows[id];
  annots = annots.filter(a => a.id !== id);
  snapshotState();
  syncAnnots(); updateAnnotPanel(); updateStatusCount(); updateEmmaRegister();
}

function undoLast() {
  if (historyIdx <= 0) { toast('Nothing to undo'); return; }
  historyIdx--;
  const snap = history[historyIdx];
  annots = JSON.parse(JSON.stringify(snap.annots));
  emmaRows = JSON.parse(JSON.stringify(snap.emmaRows));
  syncAnnots(); updateAnnotPanel(); updateStatusCount(); updateEmmaRegister();
  updateUndoRedoButtons();
  toast('Undone');
}

function redoLast() {
  if (historyIdx >= history.length - 1) { toast('Nothing to redo'); return; }
  historyIdx++;
  const snap = history[historyIdx];
  annots = JSON.parse(JSON.stringify(snap.annots));
  emmaRows = JSON.parse(JSON.stringify(snap.emmaRows));
  syncAnnots(); updateAnnotPanel(); updateStatusCount(); updateEmmaRegister();
  updateUndoRedoButtons();
  toast('Redone');
}

function clearPage() {
  if (!pdf) return;
  const before = annots.length;
  annots = annots.filter(a => a.pageNum !== curPg);
  if (before !== annots.length) {
    snapshotState();
    syncAnnots(); updateAnnotPanel(); updateStatusCount(); updateEmmaRegister();
    toast(`Cleared page ${curPg}`);
  }
}

function updateStatusCount() {
  document.getElementById('sb-count').textContent =
    `${annots.length} annotation${annots.length !== 1 ? 's' : ''}`;
}

document.addEventListener('keydown', e => {
  // Don't fire tool shortcuts when typing in an input/textarea
  const inInput = ['INPUT','TEXTAREA','SELECT'].includes(document.activeElement?.tagName);

  if ((e.ctrlKey || e.metaKey) && e.key === 'z') { e.preventDefault(); undoLast(); return; }
  if ((e.ctrlKey || e.metaKey) && (e.key === 'y' || (e.shiftKey && e.key === 'z'))) { e.preventDefault(); redoLast(); return; }
  if ((e.ctrlKey || e.metaKey) && e.key === 's') { e.preventDefault(); saveSession(); return; }

  if (e.key === 'Escape') {
    hideCtx(); hideQuickToolbar(); txtPopCancel(); closeStylePopover();
    if (measureState !== 'idle') {
      if (measureLiveSvg) { measureLiveSvg.remove(); measureLiveSvg = null; }
      measureState = 'idle'; measureP1 = null; measureP2 = null; measurePageNum = null;
      document.getElementById('sb-measure').classList.remove('visible');
      toast('Measure cancelled');
    }
    closeM('mkeys');
    return;
  }

  if (e.key === '?') { openM('mkeys'); return; }

  if ((e.key === 'Delete' || e.key === 'Backspace') && !inInput) {
    const sel = document.querySelector('.aitem.selected');
    if (sel) {
      const id = parseInt(sel.dataset.id);
      if (id) deleteAnnotById(id);
      return;
    }
    // On-canvas selection (resize/endpoint handles showing) — same target
    // an active drag would move, so Delete should remove it too.
    if (_selectedAnnotId != null) {
      const id = _selectedAnnotId;
      removeResizeHandles();
      deleteAnnotById(id);
      return;
    }
    return;
  }

  // Space = temporary pan (hold)
  if (e.key === ' ' && !inInput && !e.repeat) {
    e.preventDefault();
    if (tool !== 'pan') { window._prevTool = tool; setTool('pan'); }
    return;
  }

  // Tool letter shortcuts (not when typing)
  if (!inInput && !e.ctrlKey && !e.metaKey && !e.altKey) {
    const toolKeys = { h:'highlight', m:'texthighlight', r:'rect', p:'pen',
      a:'arrow', c:'cloud', g:'area', d:'measure', t:'text',
      e:'erase', v:'pan', z:'zoombox', l:'line', f:'rectfill', s:'select', o:'circle' };
    if (toolKeys[e.key.toLowerCase()]) { setTool(toolKeys[e.key.toLowerCase()]); return; }
    if (e.key === '[') { toggleSidebar(); return; }
  }
  // Alt+1/2/3 — switch ribbon tabs
  if (e.altKey && !inInput) {
    if (e.key === '1') { e.preventDefault(); switchRibbon('file',   document.getElementById('rtab-file'));   return; }
    if (e.key === '2') { e.preventDefault(); switchRibbon('markup', document.getElementById('rtab-markup')); return; }
    if (e.key === '3') { e.preventDefault(); switchRibbon('review', document.getElementById('rtab-review')); return; }
  }
});

document.addEventListener('keyup', e => {
  if (e.key === ' ' && window._prevTool) {
    setTool(window._prevTool); window._prevTool = null;
  }
});
document.addEventListener('mousemove', e => {
  if (!panDragging || !panStart) return;
  const viewer = document.getElementById('viewer');
  viewer.scrollLeft = panScrollStart.left - (e.clientX - panStart.x);
  viewer.scrollTop  = panScrollStart.top  - (e.clientY - panStart.y);
});
document.addEventListener('mouseup', () => {
  if (panDragging) {
    panDragging = false; panStart = null; panScrollStart = null;
    document.querySelectorAll('.aoverlay.panning').forEach(o => o.classList.remove('panning'));
    // Render any newly visible pages now that pan has stopped
    scheduleRender();
  }
});

/* ═══════════════════════════════════════════════
   SYNC ANNOTATIONS TO DOM
   SVG paths use a viewBox="0 0 100 100" so all coordinates are in
   0-100 space (matching our stored 0-1 fractions × 100).
   vector-effect="non-scaling-stroke" keeps strokes visually consistent.
═══════════════════════════════════════════════ */

// Sync annotations only on a specific overlay (used after lazy render)
/* ═══════════════════════════════════════════════
   TEXT LEADER ARROW
   A text box can optionally have one leader arrow
   running from the midpoint of any edge (top/right/
   bottom/left) out to a free point — started by
   dragging one of the "+" edge buttons (see
   showResizeHandles), repositioned by dragging its
   tip, removed by dragging the tip back onto the box.
═══════════════════════════════════════════════ */

// How close (px) the tip must be dragged back to the box to detach the arrow
const LEADER_DETACH_PX = 14;

function textLeaderFromPoint(a, boxWPct, boxHPct) {
  switch (a.leaderEdge) {
    case 'top':    return { x: a.x + boxWPct / 2, y: a.y };
    case 'bottom': return { x: a.x + boxWPct / 2, y: a.y + boxHPct };
    case 'left':   return { x: a.x, y: a.y + boxHPct / 2 };
    case 'right':  return { x: a.x + boxWPct, y: a.y + boxHPct / 2 };
    default:       return null;
  }
}

// Builds the leader-arrow SVG entirely in 0-100 percent space (viewBox +
// preserveAspectRatio:none, like the arrow/pen/measure annotations) so it
// rescales automatically with the overlay on zoom — no rebuild needed.
// A fixed-pixel coordinate system here would go stale the instant the page
// re-renders at a new zoom level, since nothing rebuilds annotation SVGs on
// zoom (only on create/select/move — see the comment in rerenderAll).
// Rebuilds just the line+arrowhead SVG (not the drag handle) — used both
// for the initial render and to keep the line following the tip live while
// the handle div is being dragged, without recreating the handle each time.
function updateTextLeaderLine(a, ov) {
  ov.querySelector('[data-leader="' + a.id + '"]')?.remove();
  if (!a.leaderEdge || a.leaderX === undefined || a.leaderY === undefined) return null;

  const vp = pageViewports[a.pageNum];
  if (!vp) return null;

  const c = colorHex(a.Color);
  const pin = ov.querySelector('[data-aid="' + a.id + '"]');

  // Prefer the stored percent size (exact, and already zoom-proof) — only
  // fall back to measuring the rendered box when it hasn't been sized yet.
  const boxWPct = a.w !== undefined ? a.w : (pin ? pin.offsetWidth  / vp.width  * 100 : 8);
  const boxHPct = a.h !== undefined ? a.h : (pin ? pin.offsetHeight / vp.height * 100 : 3);

  const from = textLeaderFromPoint(a, boxWPct, boxHPct);
  if (!from) return null;

  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svg.setAttribute('class', 'an-leader'); // svg.className is an SVGAnimatedString, not a plain setter
  svg.setAttribute('viewBox', '0 0 100 100');
  svg.setAttribute('preserveAspectRatio', 'none');
  svg.dataset.leader = a.id;

  const markerId = 'nl-arr-' + a.id;
  const defs   = document.createElementNS('http://www.w3.org/2000/svg', 'defs');
  const marker = document.createElementNS('http://www.w3.org/2000/svg', 'marker');
  marker.setAttribute('id', markerId);
  marker.setAttribute('viewBox', '0 0 8 8');
  marker.setAttribute('refX', '7'); marker.setAttribute('refY', '4');
  marker.setAttribute('markerWidth', '6'); marker.setAttribute('markerHeight', '6');
  marker.setAttribute('orient', 'auto');
  // markerUnits defaults to 'strokeWidth' — combined with the line's
  // vector-effect="non-scaling-stroke" below, this keeps the arrowhead a
  // small constant screen size (same technique buildArrowAnnotEl uses)
  // instead of scaling with the 0-100 viewBox like userSpaceOnUse would.
  const arrowPath = document.createElementNS('http://www.w3.org/2000/svg', 'path');
  arrowPath.setAttribute('d', 'M0,0 L8,4 L0,8 Z');
  arrowPath.setAttribute('fill', c);
  marker.appendChild(arrowPath); defs.appendChild(marker); svg.appendChild(defs);

  // Percent-space coordinates + non-scaling-stroke keep the line pinned to
  // the box edge and tip at any zoom, with a constant on-screen thickness
  // (same technique buildArrowAnnotEl uses for the arrow tool).
  const line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
  line.setAttribute('x1', from.x.toFixed(2)); line.setAttribute('y1', from.y.toFixed(2));
  line.setAttribute('x2', a.leaderX.toFixed(2)); line.setAttribute('y2', a.leaderY.toFixed(2));
  line.setAttribute('stroke', c);
  line.setAttribute('stroke-width', '1.5');
  line.setAttribute('stroke-linecap', 'round');
  line.setAttribute('vector-effect', 'non-scaling-stroke');
  line.setAttribute('marker-end', 'url(#' + markerId + ')');
  svg.appendChild(line);

  if (pin) ov.insertBefore(svg, pin);
  else ov.appendChild(svg);
  return svg;
}

function buildTextLeaderSvg(a, ov) {
  if (!updateTextLeaderLine(a, ov)) return;
  const c = colorHex(a.Color);

  // Draggable tip handle — a plain percent-positioned div (fixed pixel size,
  // like the resize handles) rather than an SVG shape, so it doesn't inherit
  // the viewBox's 0-100 coordinate scale and stays a small crisp dot at any zoom.
  const handle = document.createElement('div');
  handle.className = 'leader-tip-handle';
  handle.style.left = a.leaderX + '%';
  handle.style.top  = a.leaderY + '%';
  handle.style.background = c;
  handle.dataset.leaderHandle = a.id;
  handle.style.pointerEvents = tool === 'pan' ? 'all' : 'none';

  handle.addEventListener('mousedown', ev => {
    if (tool !== 'pan') return;
    ev.stopPropagation();
    ev.preventDefault();

    const ann = annots.find(x => x.id === a.id);
    if (!ann) return;

    const onMove = mv => {
      const r = ov.getBoundingClientRect();
      ann.leaderX = (mv.clientX - r.left) / r.width  * 100;
      ann.leaderY = (mv.clientY - r.top)  / r.height * 100;
      handle.style.left = ann.leaderX + '%';
      handle.style.top  = ann.leaderY + '%';
      updateTextLeaderLine(ann, ov);
    };

    const onUp = mv => {
      document.removeEventListener('mousemove', onMove);
      document.removeEventListener('mouseup',   onUp);
      // Dropped back onto the box — detach the arrow
      const curPin = ov.querySelector('[data-aid="' + ann.id + '"]');
      if (curPin) {
        const pr = curPin.getBoundingClientRect();
        const pad = LEADER_DETACH_PX;
        if (mv.clientX >= pr.left - pad && mv.clientX <= pr.right + pad &&
            mv.clientY >= pr.top  - pad && mv.clientY <= pr.bottom + pad) {
          delete ann.leaderEdge; delete ann.leaderX; delete ann.leaderY;
        }
      }
      syncAnnots();
      pushHistory();
    };

    document.addEventListener('mousemove', onMove);
    document.addEventListener('mouseup',   onUp);
  });

  ov.appendChild(handle);
}

// ── Overlay-level right-click handler — works in ALL tool modes ──
// Attached once per overlay. Uses capture phase so pointer-events:none is irrelevant.
function attachOverlayCtxMenu(ov) {
  if (ov._ctxHandlerAttached) return;
  ov._ctxHandlerAttached = true;
  ov.addEventListener('contextmenu', ev => {
    ev.preventDefault();
    // 1. Try to find [data-aid] or [data-svg-proxy-for] by walking up DOM
    let annotId = null;
    let t = ev.target;
    while (t && t !== ov) {
      if (t.dataset && t.dataset.aid)         { annotId = parseInt(t.dataset.aid);         break; }
      if (t.dataset && t.dataset.svgProxyFor) { annotId = parseInt(t.dataset.svgProxyFor); break; }
      t = t.parentNode;
    }
    // 2. Fallback: hit-test annotation data by position (catches pointer-events:none elements)
    if (!annotId) {
      const pageN = parseInt(ov.dataset.page);
      const r = ov.getBoundingClientRect();
      const xPct = (ev.clientX - r.left) / ov.offsetWidth  * 100;
      const yPct = (ev.clientY - r.top)  / ov.offsetHeight * 100;
      const hits = annots.filter(a => {
        if (a.pageNum !== pageN) return false;
        if (a.x !== undefined)
          return xPct >= a.x && xPct <= a.x + (a.w || 10) &&
                 yPct >= a.y && yPct <= a.y + (a.h || 10);
        if (a.x1 !== undefined) {
          const minX = Math.min(a.x1,a.x2)-2, maxX = Math.max(a.x1,a.x2)+2;
          const minY = Math.min(a.y1,a.y2)-2, maxY = Math.max(a.y1,a.y2)+2;
          return xPct >= minX && xPct <= maxX && yPct >= minY && yPct <= maxY;
        }
        return false;
      });
      if (hits.length) annotId = hits[hits.length - 1].id;
    }
    if (annotId) { ev.stopPropagation(); hideQuickToolbar(); openCtxMenu(annotId, ev.clientX, ev.clientY); }
    else { ev.stopPropagation(); hideCtx(); openQuickToolbar(ev.clientX, ev.clientY); }
  }, true); // capture — fires regardless of child pointer-events
}

// Right-click on empty drawing space (no annotation under the cursor) opens a
// small floating toolbar for one-click access to the most-used tools, instead
// of requiring a trip back up to the ribbon.
function openQuickToolbar(cx, cy) {
  const bar = document.getElementById('ctx-quickbar');
  bar.querySelectorAll('.qtb-item').forEach(b => b.classList.toggle('active', b.dataset.tool === tool));
  bar.style.left = '0'; bar.style.top = '0';
  bar.classList.add('open');
  const bw = bar.offsetWidth, bh = bar.offsetHeight;
  bar.style.left = Math.min(cx, window.innerWidth  - bw - 8) + 'px';
  bar.style.top  = Math.min(cy, window.innerHeight - bh - 8) + 'px';
}

function quickTool(t) {
  setTool(t);
  hideQuickToolbar();
}

function syncAnnotsOnOverlay(ov, pn) {
  // Remove all existing annotation elements, leader SVGs, and move overlays
  ov.querySelectorAll('[data-aid]').forEach(el => el.remove());
  ov.querySelectorAll('[data-leader]').forEach(el => el.remove());
  ov.querySelectorAll('.leader-tip-handle').forEach(el => el.remove());
  ov.querySelectorAll('[data-svg-proxy-for]').forEach(el => el.remove());
  ov.querySelectorAll('.ann-move-overlay').forEach(el => el.remove());

  attachOverlayCtxMenu(ov);

  annots.filter(a => a.pageNum === pn).forEach(a => {
    const el = buildAnnotEl(a);
    if (!el) return;
    el.dataset.aid = a.id;
    attachAnnotListeners(el, a, ov);
    ov.appendChild(el);
    // Render leader arrow SVG for text boxes that have one
    if (a.type === 'text') buildTextLeaderSvg(a, ov);
  });
  refreshAnnotPointerEvents();
}

function syncAnnots() {
  document.querySelectorAll('.aoverlay').forEach(ov => {
    const pn = parseInt(ov.dataset.page);
    ov.querySelectorAll('[data-aid]').forEach(el => el.remove());
    ov.querySelectorAll('[data-leader]').forEach(el => el.remove());
  ov.querySelectorAll('.leader-tip-handle').forEach(el => el.remove());
    ov.querySelectorAll('[data-svg-proxy-for]').forEach(el => el.remove());
    ov.querySelectorAll('.ann-move-overlay').forEach(el => el.remove());
    attachOverlayCtxMenu(ov);

    annots.filter(a => a.pageNum === pn).forEach(a => {
      const el = buildAnnotEl(a, ov);
      if (!el) return;
      el.dataset.aid = a.id;
      attachAnnotListeners(el, a, ov);
      ov.appendChild(el);
      if (a.type === 'text') buildTextLeaderSvg(a, ov);
    });
  });
  refreshAnnotPointerEvents();
}

function attachAnnotListeners(el, a, ov) {
  const isSvgWrap = el.classList.contains('asvg-wrap');
  const targets = isSvgWrap ? Array.from(el.querySelectorAll('path, line')) : [el];

  targets.forEach(target => {
    target.addEventListener('mouseenter', () => {
      if (tool === 'erase') el.classList.add('annot-hover-del');
    });
    target.addEventListener('mouseleave', () => el.classList.remove('annot-hover-del'));

    target.addEventListener('mousedown', ev => {
      if (tool !== 'erase') return;
      ev.stopPropagation();
      ev.preventDefault();
      deleteAnnotById(a.id);
      toast('Annotation removed');
    });
  });

  // Pan/select tool: click on text to edit directly in place
  if (a.type === 'text') {
    el.addEventListener('click', ev => {
      if (tool !== 'pan') return;
      ev.stopPropagation();
      startInlineEdit(a, el, ov);
    });
    el.addEventListener('dblclick', ev => {
      ev.stopPropagation();
      startInlineEdit(a, el, ov);
    });
  }

  // Wire move overlay — covers the full annotation for every moveable type
  if (ov && MOVE_TYPES.has(a.type)) {
    if (el.classList.contains('asvg-wrap')) {
      // SVG wraps fill the whole overlay — we inject a sibling bounding-box overlay instead
      wireSvgBoundingOverlay(a, ov);
    } else {
      wireMoveOverlay(el, a, ov);
    }
  }
}

// SVG-based annotations (pen, arrow, line, measure, area, texthighlight)
// Compute their bounding box in page-% coords and inject a transparent
// sibling overlay of the same size — identical drag behaviour to box types.
function wireSvgBoundingOverlay(ann, ov) {
  if (!MOVE_TYPES.has(ann.type)) return;

  // Compute bounding box from annotation data (all coords in 0-100% space)
  let minX, minY, maxX, maxY;

  if (ann.x1 !== undefined) {
    minX = Math.min(ann.x1, ann.x2); maxX = Math.max(ann.x1, ann.x2);
    minY = Math.min(ann.y1, ann.y2); maxY = Math.max(ann.y1, ann.y2);
  } else if (ann.x !== undefined && ann.w !== undefined) {
    // Box-type SVG (cloud, area rendered as SVG, etc.) — use x/y/w/h directly
    minX = ann.x; minY = ann.y; maxX = ann.x + ann.w; maxY = ann.y + ann.h;
  } else if (ann.points && ann.points.length) {
    const xs = ann.points.map(p => p.x * 100);
    const ys = ann.points.map(p => p.y * 100);
    minX = Math.min(...xs); maxX = Math.max(...xs);
    minY = Math.min(...ys); maxY = Math.max(...ys);
  } else {
    return; // can't determine bounding box
  }

  // Minimal padding — just enough to catch clicks on thin lines
  const pad = 0.3;
  minX -= pad; minY -= pad; maxX += pad; maxY += pad;
  const w = Math.max(maxX - minX, 1.5);
  const h = Math.max(maxY - minY, 1.5);

  const proxy = document.createElement('div');
  proxy.className = 'ann-move-overlay ann-svg-proxy';
  proxy.dataset.svgProxyFor = ann.id;
  proxy.style.cssText =
    'position:absolute;' +
    'left:' + minX + '%;top:' + minY + '%;' +
    'width:' + w + '%;height:' + h + '%;' +
    'cursor:grab;z-index:15;pointer-events:none;' +
    'border-radius:2px;';

  wireMoveOverlay(proxy, ann, ov);
  ov.appendChild(proxy);
}

/* Returns the 1-based EMMa register index for a given annotation id,
   or 0 if the annotation is excluded or not in the register. */
function getEmmaIndex(id) {
  const emmaAnnots = annots.filter(a =>
    (a.type === 'text' || a.type === 'measure') && !a.emmaExclude
  );
  const idx = emmaAnnots.findIndex(a => a.id === id);
  return idx >= 0 ? idx + 1 : 0;
}

function buildAnnotEl(a) {
  let el;
  if (a.type === 'highlight') {
    el = document.createElement('div'); el.className = 'ah';
    el.style.cssText = `position:absolute;left:${a.x}%;top:${a.y}%;width:${a.w}%;height:${a.h}%;background:${colorRgba(a.Color)};mix-blend-mode:multiply`;
  } else if (a.type === 'rect') {
    el = document.createElement('div'); el.className = 'ar';
    const borderStyle = a.lineStyle === 'dashed' ? 'dashed' : a.lineStyle === 'dotted' ? 'dotted' : 'solid';
    el.style.cssText = `position:absolute;left:${a.x}%;top:${a.y}%;width:${a.w}%;height:${a.h}%;border:2px ${borderStyle} ${colorHex(a.Color)};background:${colorHex(a.Color)}22`;
  } else if (a.type === 'circle') {
    el = buildCircleAnnotEl(a);
  } else if (a.type === 'strike') {
    el = document.createElement('div'); el.className = 'astrike';
    const sc = colorHex(a.Color, 'rose');
    el.style.cssText = `position:absolute;left:${a.x}%;top:${a.y}%;width:${a.w}%;height:${a.h}%;` +
      `background:linear-gradient(transparent calc(50% - 1.5px),${sc} calc(50% - 1.5px),${sc} calc(50% + 1.5px),transparent calc(50% + 1.5px))`;
  } else if (a.type === 'text') {
    el = document.createElement('div'); el.className = 'atxt';
    const txtC = colorHex(a.Color);
    const txtBox = a.box !== false;
    el.style.cssText = `position:absolute;left:${a.x}%;top:${a.y}%;Color:${txtC};` +
      `font-size:${a.fontSize || 13}px;opacity:${(a.opacity ?? 100) / 100};` +
      `display:flex;flex-direction:column;justify-content:${vAlignCss(a.vAlign)};` +
      (txtBox ? `border:1.5px solid ${txtC};border-radius:3px;background:rgba(255,255,255,.85)` : 'border:none;background:none') +
      (a.w !== undefined ? `;width:${a.w}%` : '') +
      (a.h !== undefined ? `;min-height:${a.h}%` : '');
    // Inner wrapper carries the horizontal alignment so it applies to the
    // wrapped text run (badge + text + tag) without disturbing the outer
    // flex column used for vertical alignment above.
    const txtInner = document.createElement('div');
    txtInner.className = 'atxt-inner';
    txtInner.style.textAlign = hAlignCss(a.textAlign);
    if (!a.emmaExclude) {
      const idx = getEmmaIndex(a.id);
      if (idx > 0) {
        const badge = document.createElement('span');
        badge.style.cssText = 'display:inline-flex;align-items:center;justify-content:center;width:14px;height:14px;background:#7c3aed;Color:#fff;border-radius:50%;font-size:8px;font-weight:700;font-family:var(--mono);margin-right:3px;vertical-align:middle;flex-shrink:0';
        badge.textContent = idx;
        txtInner.appendChild(badge);
      }
    }
    txtInner.appendChild(document.createTextNode(a.text));
    if (a.emmaExclude) {
      const tag = document.createElement('span');
      tag.style.cssText = 'display:inline-block;font-size:8px;background:rgba(0,0,0,0.08);Color:#888;border-radius:2px;padding:0 3px;margin-left:4px;vertical-align:middle;font-family:var(--mono)';
      tag.textContent = '⊘';
      txtInner.appendChild(tag);
    }
    el.appendChild(txtInner);
  } else if (a.type === 'pen' || a.type === 'texthighlight') {
    el = buildPenAnnotEl(a);
  } else if (a.type === 'arrow') {
    el = buildArrowAnnotEl(a);
  } else if (a.type === 'measure') {
    el = buildMeasureAnnotEl(a);
  } else if (a.type === 'cloud') {
    el = buildCloudAnnotEl(a);
  } else if (a.type === 'line') {
    el = buildLineAnnotEl(a);
  } else if (a.type === 'rectfill') {
    el = document.createElement('div');
    el.className = 'arectfill';
    el.style.cssText = `position:absolute;left:${a.x}%;top:${a.y}%;width:${a.w}%;height:${a.h}%;` +
      `background:${colorHex(a.Color)};opacity:${(a.opacity||80)/100};border-radius:1px`;
  } else if (a.type === 'area') {
    el = typeof buildAreaAnnotEl !== 'undefined' ? buildAreaAnnotEl(a) : null;
  } else if (a.type === 'stamp') {
    el = buildStampEl(a);
  } else if (a.type === 'image') {
    el = document.createElement('div');
    el.className = 'aimage';
    el.style.cssText = 'position:absolute;left:' + a.x + '%;top:' + a.y + '%;width:' + a.w + '%;height:' + a.h + '%';
    const img = document.createElement('img');
    img.src = a.src;
    img.draggable = false;
    el.appendChild(img);
  }

  // ── Post-build extensions (applied here, not via patch chain) ──
  if (el) {
    // Author Color stripe for merged sessions
    if (a.mergedFrom && a.author) {
      const ac = getAuthorColor ? getAuthorColor(a.author) : null;
      if (ac && el.style) { el.style.outline = '2px solid ' + ac; el.style.outlineOffset = '1px'; }
    }
  }

  return el || null;
}

/* ── PEN: use viewBox="0 0 100 100" on an SVG that fills the overlay.
       Points stored as 0-1 fractions → multiply by 100 for viewBox coords.
       This is the correct fix: SVG path 'd' attribute doesn't support '%'. ── */
function buildPenAnnotEl(a) {
  const wrap = document.createElement('div');
  wrap.className = 'asvg-wrap';
  wrap.style.cssText = 'position:absolute;inset:0;overflow:visible';

  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svg.setAttribute('viewBox', '0 0 100 100');
  svg.setAttribute('preserveAspectRatio', 'none');
  svg.style.cssText = 'position:absolute;top:0;left:0;width:100%;height:100%;overflow:visible';

  const d = a.points.map((p, i) => (i === 0 ? 'M' : 'L') + (p.x * 100).toFixed(3) + ',' + (p.y * 100).toFixed(3)).join(' ');

  // Fat invisible ghost path — wide hitbox for eraser (20px via non-scaling-stroke)
  const ghost = document.createElementNS('http://www.w3.org/2000/svg', 'path');
  ghost.setAttribute('d', d);
  ghost.setAttribute('fill', 'none');
  ghost.setAttribute('stroke', 'transparent');
  ghost.setAttribute('stroke-width', 20);
  ghost.setAttribute('vector-effect', 'non-scaling-stroke');
  ghost.setAttribute('stroke-linecap', 'round');
  ghost.setAttribute('stroke-linejoin', 'round');
  ghost.dataset.ghost = '1';

  // Visible path
  const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
  path.setAttribute('d', d);
  path.setAttribute('fill', 'none');
  if (a.type === 'texthighlight') {
    // Semi-transparent highlight stroke — use raw Color values for multiply blend
    path.setAttribute('stroke', colorHex(a.Color));
    path.setAttribute('stroke-width', a.sw || 14);
    path.setAttribute('opacity', '0.45');
    svg.style.mixBlendMode = 'multiply';
  } else {
    path.setAttribute('stroke', colorHex(a.Color));
    path.setAttribute('stroke-width', a.sw || 4);
  }
  path.setAttribute('vector-effect', 'non-scaling-stroke');
  path.setAttribute('stroke-linecap', 'round');
  path.setAttribute('stroke-linejoin', 'round');

  svg.appendChild(ghost);
  svg.appendChild(path);
  wrap.appendChild(svg);
  return wrap;
}

function buildArrowAnnotEl(a) {
  const wrap = document.createElement('div');
  wrap.className = 'asvg-wrap';
  wrap.style.cssText = 'position:absolute;inset:0;overflow:visible';

  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svg.setAttribute('viewBox', '0 0 100 100');
  svg.setAttribute('preserveAspectRatio', 'none');
  svg.style.cssText = 'position:absolute;top:0;left:0;width:100%;height:100%;overflow:visible';

  const c = colorHex(a.Color);
  const markerId = 'arr-' + a.id;

  const defs = document.createElementNS('http://www.w3.org/2000/svg', 'defs');
  const marker = document.createElementNS('http://www.w3.org/2000/svg', 'marker');
  marker.setAttribute('id', markerId);
  marker.setAttribute('viewBox', '0 0 10 10');
  marker.setAttribute('refX', '9'); marker.setAttribute('refY', '5');
  marker.setAttribute('markerWidth', '6'); marker.setAttribute('markerHeight', '6');
  marker.setAttribute('orient', 'auto-start-reverse');
  const arrowPath = document.createElementNS('http://www.w3.org/2000/svg', 'path');
  arrowPath.setAttribute('d', 'M 0 0 L 10 5 L 0 10 z');
  arrowPath.setAttribute('fill', c);
  marker.appendChild(arrowPath); defs.appendChild(marker); svg.appendChild(defs);

  const line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
  line.setAttribute('x1', a.x1); line.setAttribute('y1', a.y1);
  line.setAttribute('x2', a.x2); line.setAttribute('y2', a.y2);
  line.setAttribute('stroke', c);
  line.setAttribute('stroke-width', a.sw || 3);
  line.setAttribute('vector-effect', 'non-scaling-stroke');
  line.setAttribute('marker-end', `url(#${markerId})`);
  const arrowDash = dashArrayFor(a.lineStyle, a.sw || 3);
  if (arrowDash) { line.setAttribute('stroke-dasharray', arrowDash); line.setAttribute('stroke-linecap', a.lineStyle === 'dotted' ? 'round' : 'butt'); }

  // Fat ghost line for eraser hitbox
  const ghostLine = document.createElementNS('http://www.w3.org/2000/svg', 'line');
  ghostLine.setAttribute('x1', a.x1); ghostLine.setAttribute('y1', a.y1);
  ghostLine.setAttribute('x2', a.x2); ghostLine.setAttribute('y2', a.y2);
  ghostLine.setAttribute('stroke', 'transparent');
  ghostLine.setAttribute('stroke-width', 20);
  ghostLine.setAttribute('vector-effect', 'non-scaling-stroke');
  ghostLine.dataset.ghost = '1';

  svg.appendChild(ghostLine);
  svg.appendChild(line);
  wrap.appendChild(svg);
  return wrap;
}

function buildMeasureAnnotEl(a) {
  const wrap = document.createElement('div');
  wrap.className = 'asvg-wrap';
  wrap.style.cssText = 'position:absolute;inset:0;overflow:visible';

  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svg.setAttribute('viewBox', '0 0 100 100');
  svg.setAttribute('preserveAspectRatio', 'none');
  svg.style.cssText = 'position:absolute;top:0;left:0;width:100%;height:100%;overflow:visible';

  // Ghost for eraser hitbox
  const ghost = document.createElementNS('http://www.w3.org/2000/svg', 'line');
  ghost.setAttribute('x1', a.x1); ghost.setAttribute('y1', a.y1);
  ghost.setAttribute('x2', a.x2); ghost.setAttribute('y2', a.y2);
  ghost.setAttribute('stroke', 'transparent'); ghost.setAttribute('stroke-width', 20);
  ghost.setAttribute('vector-effect', 'non-scaling-stroke'); ghost.dataset.ghost = '1';

  // Dashed measure line
  const line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
  line.setAttribute('x1', a.x1); line.setAttribute('y1', a.y1);
  line.setAttribute('x2', a.x2); line.setAttribute('y2', a.y2);
  line.setAttribute('stroke', '#7c3aed'); line.setAttribute('stroke-width', 2);
  line.setAttribute('vector-effect', 'non-scaling-stroke');
  line.setAttribute('stroke-dasharray', '5,3');

  // End tick marks (perpendicular to line)
  const dx = a.x2 - a.x1, dy = a.y2 - a.y1;
  const len = Math.hypot(dx, dy) || 1;
  const nx = -dy / len * 1.5, ny = dx / len * 1.5; // perpendicular, 1.5 viewBox units
  const mkTick = (px, py) => {
    const t = document.createElementNS('http://www.w3.org/2000/svg', 'line');
    t.setAttribute('x1', px - nx); t.setAttribute('y1', py - ny);
    t.setAttribute('x2', px + nx); t.setAttribute('y2', py + ny);
    t.setAttribute('stroke', '#7c3aed'); t.setAttribute('stroke-width', 2);
    t.setAttribute('vector-effect', 'non-scaling-stroke');
    return t;
  };

  // Label background + text
  const midX = (a.x1 + a.x2) / 2, midY = (a.y1 + a.y2) / 2;
  const bg = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
  const labelStr = a.label || `${a.unit || 'px'}`;
  const charW = labelStr.length * 1.5 + 2;
  bg.setAttribute('x', midX - charW / 2); bg.setAttribute('y', midY - 4.5);
  bg.setAttribute('width', charW); bg.setAttribute('height', 5.5);
  bg.setAttribute('rx', '1'); bg.setAttribute('fill', 'rgba(255,255,255,0.88)');

  const txt = document.createElementNS('http://www.w3.org/2000/svg', 'text');
  txt.setAttribute('x', midX); txt.setAttribute('y', midY);
  txt.setAttribute('text-anchor', 'middle'); txt.setAttribute('dominant-baseline', 'middle');
  txt.setAttribute('fill', '#7c3aed'); txt.setAttribute('font-size', '3.2');
  txt.setAttribute('font-family', 'DM Mono, monospace'); txt.setAttribute('font-weight', '500');
  txt.textContent = labelStr;

  svg.appendChild(ghost); svg.appendChild(line);
  svg.appendChild(mkTick(a.x1, a.y1)); svg.appendChild(mkTick(a.x2, a.y2));
  svg.appendChild(bg); svg.appendChild(txt);
  wrap.appendChild(svg);
  return wrap;
}

/* ── CLOUD PATH helper — shared by builder and live preview ─────────────────
   Works in any coordinate space (%, pixels, etc.).
   x1 < x2 and y1 < y2 expected.                                           ── */
function makeCloudPath(x1, y1, x2, y2, r) {
  const segs = side => Math.max(3, Math.round(side / (r * 2.2)));
  const nT = segs(x2 - x1), nR = segs(y2 - y1);
  const nB = segs(x2 - x1), nL = segs(y2 - y1);
  let d = 'M' + x1.toFixed(2) + ' ' + y1.toFixed(2);
  for (let i = 0; i < nT; i++) { const bx = (x1 + (i+1)/nT*(x2-x1)).toFixed(2); d += ' A'+r+' '+r+' 0 0 1 '+bx+' '+y1.toFixed(2); }
  for (let i = 0; i < nR; i++) { const by = (y1 + (i+1)/nR*(y2-y1)).toFixed(2); d += ' A'+r+' '+r+' 0 0 1 '+x2.toFixed(2)+' '+by; }
  for (let i = 0; i < nB; i++) { const bx = (x2 - (i+1)/nB*(x2-x1)).toFixed(2); d += ' A'+r+' '+r+' 0 0 1 '+bx+' '+y2.toFixed(2); }
  for (let i = 0; i < nL; i++) { const by = (y2 - (i+1)/nL*(y2-y1)).toFixed(2); d += ' A'+r+' '+r+' 0 0 1 '+x1.toFixed(2)+' '+by; }
  return d + ' Z';
}

/* ── CLOUD: scalloped revision bubble ──────────────────────────────────────
   Standard engineering CAD revision cloud convention.
   x,y,w,h stored as % of page; rendered in viewBox 0 0 100 100.         ── */
function buildCloudAnnotEl(a) {
  const wrap = document.createElement('div');
  wrap.className = 'asvg-wrap';
  wrap.style.cssText = 'position:absolute;inset:0;overflow:visible;pointer-events:none';
  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svg.setAttribute('viewBox', '0 0 100 100');
  svg.setAttribute('preserveAspectRatio', 'none');
  svg.style.cssText = 'position:absolute;top:0;left:0;width:100%;height:100%;overflow:visible';
  const c = colorHex(a.Color);
  const x1 = a.x, y1 = a.y, x2 = a.x + a.w, y2 = a.y + a.h;
  const bumpR = Math.min(a.w, a.h) * 0.08;

  const ghost = document.createElementNS('http://www.w3.org/2000/svg', 'path');
  ghost.setAttribute('d', makeCloudPath(x1,y1,x2,y2,bumpR));
  ghost.setAttribute('fill', 'none'); ghost.setAttribute('stroke', 'transparent');
  ghost.setAttribute('stroke-width', '4'); ghost.setAttribute('vector-effect', 'non-scaling-stroke');

  const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
  path.setAttribute('d', makeCloudPath(x1,y1,x2,y2,bumpR));
  path.setAttribute('fill', c + '18'); path.setAttribute('stroke', c);
  path.setAttribute('stroke-width', '1.8'); path.setAttribute('vector-effect', 'non-scaling-stroke');
  path.setAttribute('stroke-linejoin', 'round');

  const triSize = Math.min(a.w, a.h) * 0.12;
  const tx = x2 - triSize*0.2, ty = y2 - triSize*0.2;
  const tri = document.createElementNS('http://www.w3.org/2000/svg', 'polygon');
  tri.setAttribute('points', tx+','+(ty-triSize)+' '+(tx-triSize)+','+ty+' '+(tx+triSize*0.2)+','+ty);
  tri.setAttribute('fill', 'none'); tri.setAttribute('stroke', c);
  tri.setAttribute('stroke-width', '1.5'); tri.setAttribute('vector-effect', 'non-scaling-stroke');

  svg.appendChild(ghost); svg.appendChild(path); svg.appendChild(tri);
  wrap.appendChild(svg);
  return wrap;
}

/* ── LINE annotation ── */
function buildLineAnnotEl(a) {
  const wrap = document.createElement('div');
  wrap.className = 'asvg-wrap';
  wrap.style.cssText = 'position:absolute;inset:0;overflow:visible;pointer-events:none';
  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svg.setAttribute('viewBox', '0 0 100 100');
  svg.setAttribute('preserveAspectRatio', 'none');
  svg.style.cssText = 'position:absolute;top:0;left:0;width:100%;height:100%;overflow:visible';
  const c = colorHex(a.Color);
  // Fat invisible ghost line for easier hit-testing
  const ghost = document.createElementNS('http://www.w3.org/2000/svg', 'line');
  ghost.setAttribute('x1', a.x1); ghost.setAttribute('y1', a.y1);
  ghost.setAttribute('x2', a.x2); ghost.setAttribute('y2', a.y2);
  ghost.setAttribute('stroke', 'transparent'); ghost.setAttribute('stroke-width', '8');
  ghost.setAttribute('stroke-linecap', 'round'); ghost.setAttribute('vector-effect', 'non-scaling-stroke');
  const line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
  line.setAttribute('x1', a.x1); line.setAttribute('y1', a.y1);
  line.setAttribute('x2', a.x2); line.setAttribute('y2', a.y2);
  line.setAttribute('stroke', c); line.setAttribute('stroke-width', a.sw || 2);
  line.setAttribute('stroke-linecap', 'round'); line.setAttribute('vector-effect', 'non-scaling-stroke');
  const lineDash = dashArrayFor(a.lineStyle, a.sw || 2);
  if (lineDash) line.setAttribute('stroke-dasharray', lineDash);
  svg.appendChild(ghost); svg.appendChild(line);
  wrap.appendChild(svg);
  return wrap;
}

/* ── CIRCLE / ELLIPSE annotation ── */
function buildCircleAnnotEl(a) {
  const c = colorHex(a.Color);
  const el = document.createElement('div');
  el.className = 'acircle';
  el.style.cssText = `position:absolute;left:${a.x}%;top:${a.y}%;width:${a.w}%;height:${a.h}%;overflow:visible`;

  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svg.setAttribute('width', '100%'); svg.setAttribute('height', '100%');
  svg.setAttribute('viewBox', '0 0 100 100');
  svg.setAttribute('preserveAspectRatio', 'none');
  svg.style.cssText = 'display:block;overflow:visible';

  // Wide ghost ellipse for easy eraser hit-testing
  const ghost = document.createElementNS('http://www.w3.org/2000/svg', 'ellipse');
  ghost.setAttribute('cx', '50'); ghost.setAttribute('cy', '50');
  ghost.setAttribute('rx', '50'); ghost.setAttribute('ry', '50');
  ghost.setAttribute('fill', 'none'); ghost.setAttribute('stroke', 'transparent');
  ghost.setAttribute('stroke-width', '10'); ghost.setAttribute('vector-effect', 'non-scaling-stroke');
  ghost.dataset.ghost = '1';

  const ellipse = document.createElementNS('http://www.w3.org/2000/svg', 'ellipse');
  ellipse.setAttribute('cx', '50'); ellipse.setAttribute('cy', '50');
  ellipse.setAttribute('rx', '50'); ellipse.setAttribute('ry', '50');
  ellipse.setAttribute('fill', c + '18');
  ellipse.setAttribute('stroke', c);
  ellipse.setAttribute('stroke-width', a.sw || 2);
  ellipse.setAttribute('vector-effect', 'non-scaling-stroke');
  const circleDash = dashArrayFor(a.lineStyle, a.sw || 2);
  if (circleDash) { ellipse.setAttribute('stroke-dasharray', circleDash); ellipse.setAttribute('stroke-linecap', a.lineStyle === 'dotted' ? 'round' : 'butt'); }

  svg.appendChild(ghost); svg.appendChild(ellipse);
  el.appendChild(svg);
  return el;
}

/* ═══════════════════════════════════════════════
   ANNOTATION PANEL (SIDEBAR)
═══════════════════════════════════════════════ */
function updateAnnotPanel() {
  const panel = document.getElementById('sp-notes');
  panel.querySelectorAll('.aitem').forEach(el => el.remove());
  const empty = document.getElementById('aempty');
  if (!annots.length) { empty.classList.remove('hidden'); updateAnnotNavBar(); return; }
  empty.classList.add('hidden');

  const statusColors = { open:'#fee2e2', progress:'#fef9c3', resolved:'#dcfce7', rejected:'#f1f5f9' };

  [...annots].reverse().forEach(a => {
    const item = document.createElement('div');
    item.className = 'aitem'; item.dataset.id = a.id;
    const status = a.status || 'open';

    // Build a useful preview for every annotation type
    let preview;
    if (a.text)                      preview = a.text;
    else if (a.label)                preview = a.label;                          // measure
    else if (a.x1 !== undefined)     preview = 'Pg ' + a.pageNum + '  (' + Math.round(a.x1) + ', ' + Math.round(a.y1) + ') → (' + Math.round(a.x2) + ', ' + Math.round(a.y2) + ')';
    else if (a.points?.length)       preview = a.points.length + ' points';      // pen/area
    else if (a.stampId)              preview = a.label || a.stampId;             // stamp
    else                             preview = typeLabels[a.type] || a.type;

    const tsStr = a.ts ? new Date(a.ts).toLocaleString(undefined, {dateStyle:'short',timeStyle:'short'}) : '';
    const canEdit   = ['text'].includes(a.type);
    // Status available on all annotation types (useful for any comment workflow)
    const hasStatus = true;

    item.innerHTML =
      '<button class="adel" title="Delete annotation (Del)">✕</button>' +
      '<div class="atype">' +
        '<span class="adot" style="background:' + colorHex(a.Color, '#999') + '"></span>' +
        (typeLabels[a.type] || a.type) +
      '</div>' +
      '<select class="aitem-status" data-annotid="' + a.id + '" style="background:' + (statusColors[status] || '#fff') + '">' +
        STATUS_CYCLE.map(s => '<option value="' + s + '"' + (s === status ? ' selected' : '') + '>' + STATUS_LABEL[s] + '</option>').join('') +
      '</select>' +
      '<div class="apreview">' + preview + '</div>' +
      '<div class="ats">' + (a.author ? '● ' + a.author + '  · ' : '') + 'Pg ' + a.pageNum + (tsStr ? '  · ' + tsStr : '') + '</div>' +
      (canEdit ? '<button class="aedit-btn" title="Edit text" onclick="event.stopPropagation();editAnnotById(' + a.id + ')">Edit</button>' : '');

    item.querySelector('.adel').onclick = ev => { ev.stopPropagation(); deleteAnnotById(a.id); };

    item.querySelector('.aitem-status').onchange = function(ev) {
      ev.stopPropagation();
      const ann = annots.find(x => x.id === a.id);
      if (!ann) return;
      ann.status = this.value;
      this.style.background = statusColors[this.value] || '#fff';
      syncAnnots(); updateAnnotPanel(); updateEmmaRegister(); pushHistory();
    };

    item.onclick = (ev) => {
      if (ev.target.closest('select,button')) return;
      document.querySelectorAll('.aitem').forEach(i => i.classList.remove('selected'));
      item.classList.add('selected');
      scrollToAnnotation(a);
    };
    panel.insertBefore(item, empty);
  });

  updateAnnotNavBar();
}

// Scroll viewer to show an annotation and flash-highlight it.
// Handles box types (positioned div) and SVG types (inset:0 wrap).
function scrollToAnnotation(a) {
  scrollToPage(a.pageNum);
  setTimeout(() => {
    const ov = document.querySelector('.aoverlay[data-page="' + a.pageNum + '"]');
    if (!ov) return;
    const ovRect = ov.getBoundingClientRect();
    const viewer = document.getElementById('viewer');

    // Compute the annotation's midpoint in page-% coords
    let midXpct, midYpct, wPct, hPct;

    if (a.x !== undefined && a.w !== undefined) {
      // Box type
      midXpct = a.x + a.w / 2;  midYpct = a.y + a.h / 2;
      wPct = a.w; hPct = a.h;
    } else if (a.x !== undefined) {
      // Point type (note, text, stamp)
      midXpct = a.x; midYpct = a.y;
      wPct = 8; hPct = 4;
    } else if (a.x1 !== undefined) {
      // Line type (arrow, line, measure)
      midXpct = (a.x1 + a.x2) / 2; midYpct = (a.y1 + a.y2) / 2;
      wPct = Math.abs(a.x2 - a.x1) + 4; hPct = Math.abs(a.y2 - a.y1) + 4;
    } else if (a.points && a.points.length) {
      // Pen / area / texthighlight
      const xs = a.points.map(p => p.x * 100);
      const ys = a.points.map(p => p.y * 100);
      const minX = Math.min(...xs), maxX = Math.max(...xs);
      const minY = Math.min(...ys), maxY = Math.max(...ys);
      midXpct = (minX + maxX) / 2; midYpct = (minY + maxY) / 2;
      wPct = maxX - minX + 4; hPct = maxY - minY + 4;
    } else {
      return;
    }

    // Convert % to px within the overlay
    const midPxX = midXpct / 100 * ov.offsetWidth;
    const midPxY = midYpct / 100 * ov.offsetHeight;

    // Scroll viewer so the annotation midpoint is centred
    const viewerRect = viewer.getBoundingClientRect();
    const targetScrollLeft = (ov.offsetLeft + midPxX) - viewerRect.width / 2;
    const targetScrollTop  = (ov.offsetTop  + midPxY) - viewerRect.height / 2;
    viewer.scrollTo({ left: targetScrollLeft, top: targetScrollTop, behavior: 'smooth' });

    // Flash a highlight box at the annotation position
    const flash = document.createElement('div');
    flash.style.cssText =
      'position:absolute;pointer-events:none;z-index:100;border-radius:3px;' +
      'border:2.5px solid #2563eb;background:rgba(37,99,235,0.08);' +
      'transition:opacity 0.6s ease;' +
      'left:' + (midXpct - wPct/2) + '%;' +
      'top:'  + (midYpct - hPct/2) + '%;' +
      'width:' + Math.max(wPct, 3) + '%;' +
      'height:'+ Math.max(hPct, 2) + '%;';
    ov.appendChild(flash);
    requestAnimationFrame(() => requestAnimationFrame(() => {
      flash.style.opacity = '1';
      setTimeout(() => {
        flash.style.opacity = '0';
        setTimeout(() => flash.remove(), 700);
      }, 900);
    }));
  }, 150);
}

function editAnnotById(id) {
  const a = annots.find(x => x.id === id);
  const editableTypes = ['text'];
  if (!a || !editableTypes.includes(a.type)) return;
  const el = document.querySelector('[data-aid="' + id + '"]');
  let sx = window.innerWidth / 2, sy = window.innerHeight / 2;
  if (el) { const r = el.getBoundingClientRect(); sx = r.left; sy = r.bottom; }
  const emmaData = {
    discipline: a.discipline, priority: a.priority,
    gridRef: a.gridRef, action: a.action,
    emmaExclude: a.emmaExclude || false,
    Color: a.Color, fontSize: a.fontSize,
    opacity: a.opacity ?? 100,
  };
  showTxtPop(sx, sy, (txt, emmaFields) => {
    a.text = txt;
    Object.assign(a, emmaFields);
    syncAnnots(); updateAnnotPanel(); updateEmmaRegister();
    toast('Annotation updated');
  }, a.text, emmaData);
}

// ── In-place editing for text annotations ──
// A textarea is overlaid directly on the annotation (matching its font,
// colour and alignment) instead of opening the separate popover box —
// click, type, click away or press Escape/Tab to finish, like editing
// text directly in a PDF viewer.
function startInlineEdit(a, el, ov) {
  if (!el || a.type !== 'text') return;
  if (el.querySelector('.ann-inline-editor')) return; // already editing

  const container = el;
  const textHost  = el.querySelector('.atxt-inner');
  if (!container) return;

  const hadPosition = !!container.style.position;
  if (!hadPosition) container.style.position = 'relative';
  if (textHost) textHost.style.visibility = 'hidden';

  const cs = getComputedStyle(container);
  const ta = document.createElement('textarea');
  ta.className = 'ann-inline-editor';
  ta.value = a.text || '';
  ta.spellcheck = false;
  ta.style.cssText =
    'position:absolute;inset:0;z-index:25;resize:none;border:none;outline:none;' +
    'box-sizing:border-box;background:rgba(255,255,255,.92);white-space:pre-wrap;overflow:auto;' +
    'font-family:inherit;font-size:' + cs.fontSize + ';color:' + cs.color + ';' +
    'text-align:' + cs.textAlign + ';line-height:' + cs.lineHeight + ';padding:' + cs.padding + ';';
  container.appendChild(ta);
  ta.focus();
  ta.select();

  let finished = false;
  const finish = commit => {
    if (finished) return;
    finished = true;
    ta.removeEventListener('blur', onBlur);
    ta.removeEventListener('keydown', onKeydown);
    const newText = ta.value;
    ta.remove();
    if (commit && newText !== (a.text || '')) {
      a.text = newText;
      syncAnnots(); updateAnnotPanel(); updateEmmaRegister(); pushHistory();
      return; // syncAnnots rebuilds the element — nothing left to restore
    }
    if (textHost) textHost.style.visibility = '';
    if (!hadPosition) container.style.position = '';
  };

  const onBlur = () => finish(true);
  const onKeydown = ev => {
    ev.stopPropagation();
    if (ev.key === 'Escape') { ev.preventDefault(); finish(false); }
  };
  ta.addEventListener('blur', onBlur);
  ta.addEventListener('keydown', onKeydown);
  ta.addEventListener('mousedown', ev => ev.stopPropagation());
  ta.addEventListener('click', ev => ev.stopPropagation());
}

/* ═══════════════════════════════════════════════
   CONTEXT MENU
═══════════════════════════════════════════════ */
function openCtxMenu(annotId, cx, cy) {
  ctxAnnotId = annotId;
  const a = annots.find(x => x.id === annotId);
  const menu = document.getElementById('ctx-menu');

  // Show/hide items based on annotation type
  const isTextable = a && ['text'].includes(a.type);
  const hasStatus  = a && ['text'].includes(a.type);
  const isImage    = a && a.type === 'image';
  document.getElementById('ctx-edit').style.display   = isTextable ? 'flex' : 'none';
  document.getElementById('ctx-resize').style.display = isImage    ? 'flex' : 'none';

  // Show status items only for text-bearing annotations
  ['ctx-status-label','ctx-status-open','ctx-status-progress',
   'ctx-status-resolved','ctx-status-rejected'].forEach(id => {
    const el = document.getElementById(id);
    if (el) el.style.display = hasStatus ? (id === 'ctx-status-label' ? 'block' : 'flex') : 'none';
  });
  // Tick current status
  if (a && a.status) {
    ['open','progress','resolved','rejected'].forEach(s => {
      const el = document.getElementById('ctx-status-' + s);
      if (el) el.style.fontWeight = a.status === s ? '700' : '';
    });
  }

  // Position — keep on screen
  menu.style.left = '0'; menu.style.top = '0';
  menu.classList.add('open');
  const mw = menu.offsetWidth, mh = menu.offsetHeight;
  menu.style.left = Math.min(cx, window.innerWidth  - mw - 8) + 'px';
  menu.style.top  = Math.min(cy, window.innerHeight - mh - 8) + 'px';
}

function ctxDelete() {
  if (ctxAnnotId != null) { deleteAnnotById(ctxAnnotId); toast('Annotation deleted'); }
  hideCtx(); ctxAnnotId = null;
}

function ctxEdit() {
  if (ctxAnnotId == null) { hideCtx(); return; }
  editAnnotById(ctxAnnotId);
  hideCtx(); ctxAnnotId = null;
}

function ctxResizeImage() {
  if (ctxAnnotId == null) { hideCtx(); return; }
  const a = annots.find(x => x.id === ctxAnnotId);
  hideCtx();
  if (!a || a.type !== 'image') return;
  // Switch to pan mode so resize handles are accessible
  if (tool !== 'pan') setTool('pan');
  // Find the annotation element and its overlay, then show resize handles
  setTimeout(() => {
    const el  = document.querySelector('[data-aid="' + a.id + '"]');
    const ov  = el?.closest('.aoverlay');
    if (el && ov) {
      showResizeHandles(el, a, ov);
      toast('Drag the handles to resize · click elsewhere to deselect', 3000);
    }
  }, 80);
  ctxAnnotId = null;
}

function ctxOpenStyle(ev) {
  if (ctxAnnotId == null) { hideCtx(); return; }
  const id = ctxAnnotId;
  hideCtx(); ctxAnnotId = null;
  openAnnotStylePopover(id, ev.clientX, ev.clientY);
}

function ctxDuplicate() {
  if (ctxAnnotId == null) { hideCtx(); return; }
  const a = annots.find(x => x.id === ctxAnnotId);
  if (!a) { hideCtx(); return; }
  const copy = JSON.parse(JSON.stringify(a));
  copy.id = nextId();
  // Offset slightly so it's visible
  if (copy.x  !== undefined) { copy.x  += 2; copy.y  += 2; }
  if (copy.x1 !== undefined) { copy.x1 += 2; copy.y1 += 2; copy.x2 += 2; copy.y2 += 2; }
  if (copy.points) copy.points = copy.points.map(p => ({ x: p.x + 0.02, y: p.y + 0.02 }));
  if (copy.leaderX !== undefined) { copy.leaderX += 2; copy.leaderY += 2; }
  pushAnnot(copy);
  toast('Annotation duplicated');
  hideCtx(); ctxAnnotId = null;
}

function ctxSetStatus(s) {
  if (ctxAnnotId == null) { hideCtx(); return; }
  const a = annots.find(x => x.id === ctxAnnotId);
  if (a) { a.status = s; syncAnnots(); updateAnnotPanel(); updateEmmaRegister(); pushHistory(); }
  toast('Status → ' + (STATUS_LABEL[s] || s));
  hideCtx(); ctxAnnotId = null;
}

document.addEventListener('click', e => {
  if (!document.getElementById('ctx-menu').contains(e.target)) hideCtx();
  if (!document.getElementById('ctx-quickbar').contains(e.target)) hideQuickToolbar();
});

/* ═══════════════════════════════════════════════
   SIDEBAR TABS
═══════════════════════════════════════════════ */
function toggleSidebar() {
  const sb = document.getElementById('sidebar');
  const btn = document.getElementById('sidebar-toggle-btn');
  const collapsed = sb.classList.toggle('collapsed');
  btn.innerHTML = collapsed ? '&#xBB;' : '&#xAB;';
  btn.title = collapsed ? 'Expand sidebar ([ )' : 'Collapse sidebar ([ )';
}

function switchTab(tab, btn) {
  document.querySelectorAll('.stab').forEach(b => b.classList.remove('active'));
  btn.classList.add('active');
  document.getElementById('sp-pages').classList.toggle('hidden',   tab !== 'pages');
  document.getElementById('sp-notes').classList.toggle('hidden',   tab !== 'notes');
  document.getElementById('sp-search').classList.toggle('hidden',  tab !== 'search');
  const emmaPanel = document.getElementById('sp-emma');
  emmaPanel.classList.toggle('visible', tab === 'emma');
  document.getElementById('sidebar').classList.toggle('emma-open', tab === 'emma');
  if (tab === 'search') setTimeout(() => document.getElementById('search-input').focus(), 50);
}

/* ═══════════════════════════════════════════════
   MERGE / SPLIT
═══════════════════════════════════════════════ */
function onMergeFiles(e) {
  mergeFiles = Array.from(e.target.files);
  document.getElementById('mfl').innerHTML =
    mergeFiles.map((f, i) => `<div class="frow">${i + 1}. ${f.name}</div>`).join('');
}

async function loadPdfLib() {
  if (window.PDFLib) return;
  await new Promise((res, rej) => {
    const s = document.createElement('script');
    s.src = 'https://cdnjs.cloudflare.com/ajax/libs/pdf-lib/1.17.1/pdf-lib.min.js';
    s.onload = res; s.onerror = rej; document.head.appendChild(s);
  });
}

async function doMerge() {
  if (mergeFiles.length < 2) { toast('Select at least 2 PDF files'); return; }
  toast('Merging…');
  try {
    await loadPdfLib();
    const { PDFDocument } = PDFLib;
    const merged = await PDFDocument.create();
    for (const f of mergeFiles) {
      const src = await PDFDocument.load(await f.arrayBuffer());
      const pages = await merged.copyPages(src, src.getPageIndices());
      pages.forEach(p => merged.addPage(p));
    }
    dl(await merged.save(), document.getElementById('mfn').value || 'merged.pdf');
    closeM('mm'); toast(`✓ Merged ${mergeFiles.length} files`);
  } catch(e) { toast('Merge failed: ' + e.message); }
}

async function doSplit() {
  if (!pdfBytes) { toast('Open a PDF first'); return; }
  const ranges = document.getElementById('sranges').value.trim();
  const prefix = document.getElementById('sprefix').value.trim() || 'drawing';
  if (!ranges) { toast('Enter page ranges'); return; }
  try {
    await loadPdfLib();
    const { PDFDocument } = PDFLib;
    const src = await PDFDocument.load(pdfBytes.slice(0));
    let count = 0;
    for (const r of ranges.split(',').map(s => s.trim()).filter(Boolean)) {
      const pages = parseR(r, nPages); if (!pages.length) continue;
      const out = await PDFDocument.create();
      const cp = await out.copyPages(src, pages.map(p => p - 1));
      cp.forEach(p => out.addPage(p));
      dl(await out.save(), `${prefix}_${r.replace(/\s/g,'')}.pdf`);
      count++;
      await new Promise(r => setTimeout(r, 250));
    }
    closeM('ms'); toast(`✓ Created ${count} file${count !== 1 ? 's' : ''}`);
  } catch(e) { toast('Split failed: ' + e.message); }
}

function parseR(r, max) {
  const pages = [];
  if (r.includes('-')) {
    const [a, b] = r.split('-').map(Number);
    for (let i = a; i <= Math.min(b, max); i++) pages.push(i);
  } else {
    const n = parseInt(r); if (n >= 1 && n <= max) pages.push(n);
  }
  return pages;
}

function dl(bytes, name) {
  const url = URL.createObjectURL(new Blob([bytes], { type: 'application/pdf' }));
  const a = document.createElement('a'); a.href = url; a.download = name; a.click();
  URL.revokeObjectURL(url);
}

/* ═══════════════════════════════════════════════
   SCALE CALIBRATION
═══════════════════════════════════════════════ */
function applyScale() {
  const px   = parseFloat(document.getElementById('scale-px').value);
  const real = parseFloat(document.getElementById('scale-real').value);
  const unit = document.getElementById('scale-unit').value;
  if (!px || !real || px <= 0 || real <= 0) { toast('Enter valid values'); return; }
  // pxPerUnit = screen pixels per unit at zoom=1
  measureScale = { pxPerUnit: (px / zoom) / real, unit };
  localStorage.setItem('engdoc_scale', JSON.stringify(measureScale));
  document.getElementById('sb-scale').textContent = `⚖ 1 ${unit} = ${(px/real).toFixed(1)} px`;
  closeM('mscale');
  toast(`Scale set: 1 ${unit} = ${(px/real).toFixed(1)} px at current zoom`);
}

/* ═══════════════════════════════════════════════
   SAVE / LOAD SESSION (.engdoc)
═══════════════════════════════════════════════ */
/* ═══════════════════════════════════════════════
   SAVE / LOAD SESSION (.engdoc)
   v2  = annotations only  (small file)
   v3  = annotations + embedded base64 PDF  (portable)
═══════════════════════════════════════════════ */
// ── File System Access API handle — stored after first save pick ──
let _fileHandle = null;
let _loadedEngdocName = null; // filename of the loaded .engdoc, for suggested save name

// Prompt: overwrite existing file or save as new?
// Returns 'overwrite' | 'saveas' | 'cancel'
function _promptSaveMode(filename) {
  return new Promise(resolve => {
    // Build a small inline modal — avoid blocking browser confirm()
    const overlay = document.createElement('div');
    overlay.style.cssText =
      'position:fixed;inset:0;background:rgba(0,0,0,.45);z-index:1000;' +
      'display:flex;align-items:center;justify-content:center;backdrop-filter:blur(2px)';

    const box = document.createElement('div');
    box.style.cssText =
      'background:#fff;border-radius:10px;padding:24px 28px;max-width:380px;width:90%;' +
      'box-shadow:0 12px 40px rgba(0,0,0,.18);font-family:var(--font)';

    box.innerHTML =
      '<div style="font-size:16px;font-weight:700;Color:var(--gray-900);margin-bottom:8px">Save session</div>' +
      '<div style="font-size:13px;Color:var(--gray-600);margin-bottom:20px;line-height:1.5">' +
        'Overwrite <strong>' + filename + '</strong> or save to a new file?' +
      '</div>' +
      '<div style="display:flex;gap:8px;justify-content:flex-end;flex-wrap:wrap">' +
        '<button id="_sp-cancel" style="padding:8px 16px;border:1px solid var(--gray-300);border-radius:6px;background:#fff;cursor:pointer;font-size:13px;font-family:var(--font)">Cancel</button>' +
        '<button id="_sp-saveas" style="padding:8px 16px;border:1px solid var(--gray-300);border-radius:6px;background:#fff;cursor:pointer;font-size:13px;font-family:var(--font)">Save As…</button>' +
        '<button id="_sp-overwrite" style="padding:8px 16px;border:none;border-radius:6px;background:var(--blue-500);Color:#fff;cursor:pointer;font-size:13px;font-weight:600;font-family:var(--font)">Overwrite</button>' +
      '</div>';

    overlay.appendChild(box);
    document.body.appendChild(overlay);

    overlay.addEventListener('click', e => { if (e.target === overlay) { overlay.remove(); resolve('cancel'); } });
    box.querySelector('#_sp-cancel').onclick    = () => { overlay.remove(); resolve('cancel'); };
    box.querySelector('#_sp-saveas').onclick    = () => { overlay.remove(); resolve('saveas'); };
    box.querySelector('#_sp-overwrite').onclick = () => { overlay.remove(); resolve('overwrite'); };
  });
}

async function _saveToHandle(data, filename) {
  const json = JSON.stringify(data);
  const blob = new Blob([json], { type: 'application/json' });

  // If we have an existing handle, ask whether to overwrite or save as new
  if (_fileHandle) {
    const mode = await _promptSaveMode(_loadedEngdocName || filename);
    if (mode === 'cancel') return false;
    if (mode === 'overwrite') {
      try {
        const writable = await _fileHandle.createWritable();
        await writable.write(blob);
        await writable.close();
        return true;
      } catch(e) {
        _fileHandle = null;
        // Handle invalid — fall through to picker
      }
    } else {
      // Save As — clear handle so picker opens below
      _fileHandle = null;
    }
  }

  // File System Access API picker (Chrome/Edge)
  if (window.showSaveFilePicker) {
    try {
      _fileHandle = await window.showSaveFilePicker({
        suggestedName: filename,
        types: [{ description: 'EngDoc Session', accept: { 'application/json': ['.engdoc'] } }],
      });
      _loadedEngdocName = _fileHandle.name;
      const writable = await _fileHandle.createWritable();
      await writable.write(blob);
      await writable.close();
      return true;
    } catch(e) {
      if (e.name === 'AbortError') return false;
      _fileHandle = null;
    }
  }

  // Legacy fallback — <a download> (Firefox, Safari)
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url; a.download = filename; a.click();
  URL.revokeObjectURL(url);
  return true;
}



function saveSession() {
  if (!pdfName && !annots.length) { toast('Nothing to save'); return; }
  const data = { v: 2, pdfName, annotIdSeq, measureScale, annots, emmaRows };
  const filename = _loadedEngdocName || (pdfName ? pdfName.replace(/\.pdf$/i,'') : 'session') + '.engdoc';
  _saveToHandle(data, filename).then(ok => {
    if (ok) toast(`✓ Session saved — ${annots.length} annotation${annots.length !== 1 ? 's' : ''}`);
  });
}

async function saveSessionWithPdf() {
  if (!pdfBytes) { toast('Open a PDF first'); return; }
  toast('Embedding PDF… (may take a moment for large files)', 3000);
  const bytes = new Uint8Array(pdfBytes);
  let binary = '';
  const chunk = 8192;
  for (let i = 0; i < bytes.length; i += chunk) {
    binary += String.fromCharCode(...bytes.subarray(i, i + chunk));
  }
  const b64 = btoa(binary);
  const data = { v: 3, pdfName, annotIdSeq, measureScale, annots, emmaRows, pdfData: b64 };
  const filename = _loadedEngdocName || (pdfName ? pdfName.replace(/\.pdf$/i,'') : 'session') + '.engdoc';
  const ok = await _saveToHandle(data, filename);
  if (ok) toast(`✓ Saved with embedded PDF — ${sizeMb} MB`);
}

function _downloadJSON(data, filename) {
  // Legacy — kept for any external callers; new code uses _saveToHandle
  const blob = new Blob([JSON.stringify(data)], { type: 'application/json' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url; a.download = filename; a.click();
  URL.revokeObjectURL(url);
}

async function loadSession(e) {
  const file = e.target.files[0]; if (!file) return;
  e.target.value = '';
  try {
    const text = await file.text();
    const data = JSON.parse(text);
    if (!data.annots) throw new Error('Invalid session file');

    // Remember the source filename so Save can suggest overwriting it
    _loadedEngdocName = file.name;
    // If the file came from showOpenFilePicker (File System Access API), store its handle
    if (e._fileHandle) {
      _fileHandle = e._fileHandle;
    } else {
      // No handle available (drag-drop / legacy input) — clear handle so
      // first Save opens the picker with the original name pre-filled
      _fileHandle = null;
    }

    // v3: embedded PDF — auto-load it first
    if (data.v === 3 && data.pdfData) {
      toast('Loading embedded PDF…', 2000);
      const binary = atob(data.pdfData);
      const bytes = new Uint8Array(binary.length);
      for (let i = 0; i < binary.length; i++) bytes[i] = binary.charCodeAt(i);
      const pdfFile = new File([bytes], data.pdfName || 'document.pdf', { type: 'application/pdf' });
      await loadPDF(pdfFile);
      // loadPDF resets _fileHandle — restore it
      _fileHandle = e._fileHandle || null;
      _loadedEngdocName = file.name;
    }

    annots = migrateLegacyAnnots(data.annots);
    emmaRows = data.emmaRows || {};
    annotIdSeq = data.annotIdSeq || annots.reduce((m, a) => Math.max(m, a.id || 0), 0);
    if (data.measureScale) {
      measureScale = data.measureScale;
      document.getElementById('sb-scale').textContent =
        `⚖ Scale: 1 ${measureScale.unit} = ${(measureScale.pxPerUnit).toFixed(1)} px`;
    }
    // Restore EMMA panel fields if saved
    if (data.emmaFields) {
      Object.entries(data.emmaFields).forEach(([id, val]) => {
        const el = document.getElementById(id);
        if (el) el.value = val;
      });
    }
    syncAnnots(); updateAnnotPanel(); updateStatusCount(); updateEmmaRegister(); updateEmmaDash();
    toast(`✓ Loaded: ${annots.length} annotation${annots.length !== 1 ? 's' : ''}${data.v === 3 ? ' (with embedded PDF)' : ''}`);
  } catch(err) {
    toast('Failed to load session: ' + err.message);
  }
}

/* ═══════════════════════════════════════════════
   EXPORT ANNOTATED PDF
   Burns all annotations onto the PDF pages using
   pdf-lib so the result is viewable in any PDF
   reader without EngDoc installed.
═══════════════════════════════════════════════ */
function saveAsPdf() {
  if (!pdfBytes) { toast('Open a PDF first'); return; }
  const blob = new Blob([pdfBytes], { type: 'application/pdf' });
  const url  = URL.createObjectURL(blob);
  const a    = document.createElement('a');
  a.href = url;
  a.download = pdfName || 'document.pdf';
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  setTimeout(() => URL.revokeObjectURL(url), 2000);
  toast(`Saved: ${pdfName}`);
}

async function exportAnnotatedPdf() {
  if (!pdfBytes) { toast('Open a PDF first'); return; }

  toast('Generating annotated PDF…', 5000);
  try {
    await loadPdfLib();
    const { PDFDocument, rgb, degrees, StandardFonts } = PDFLib;

    const srcDoc = await PDFDocument.load(pdfBytes.slice(0));
    const pages  = srcDoc.getPages();
    const pdfFont = await srcDoc.embedFont(StandardFonts.Helvetica);

    // pdf-lib Color helpers from hex
    const hexToRgb = (hex, alpha = 1) => {
      const r = parseInt(hex.slice(1,3), 16) / 255;
      const g = parseInt(hex.slice(3,5), 16) / 255;
      const b = parseInt(hex.slice(5,7), 16) / 255;
      return { r, g, b };
    };
    const C = (hex, a) => { const { r, g, b } = hexToRgb(hex); return rgb(r, g, b); };

    // stroke-dasharray equivalent for pdf-lib (point units, so no viewBox scaling needed)
    const pdfDashArray = (style, sw) => {
      const s = Math.max(1, sw || 2);
      if (style === 'dashed') return [5 * s, 3.2 * s];
      if (style === 'dotted') return [0.6 * s, 2.8 * s];
      return undefined;
    };

    // Fallback fill tints for named presets (custom hex colours use tintHex() instead)
    const FILL = { yellow: '#fef9c3', green: '#dcfce1', red: '#fee0e5', blue: '#dbeafe', black: '#e9ecef', teal: '#ccfbf1', rose: '#ffe4e6' };

    // Group annotations by page
    const byPage = {};
    annots.forEach(a => {
      if (!byPage[a.pageNum]) byPage[a.pageNum] = [];
      byPage[a.pageNum].push(a);
    });

    for (const [pgNumStr, pageAnnots] of Object.entries(byPage)) {
      const pgNum = parseInt(pgNumStr);
      const page  = pages[pgNum - 1];
      if (!page) continue;
      const { width: W, height: H } = page.getSize();

      for (const a of pageAnnots) {
        const c = colorHex(a.Color);
        const cf = isHexColor(a.Color) ? tintHex(a.Color) : (FILL[a.Color] || FILL.yellow);
        const { r, g, b } = hexToRgb(c);

        try {
          if (a.type === 'highlight') {
            // Semi-transparent yellow box
            page.drawRectangle({
              x: a.x / 100 * W,
              y: H - (a.y + a.h) / 100 * H,
              width:  a.w / 100 * W,
              height: a.h / 100 * H,
              color: rgb(r, g, b),
              opacity: 0.3,
              borderOpacity: 0,
            });
          }

          else if (a.type === 'rect') {
            page.drawRectangle({
              x: a.x / 100 * W,
              y: H - (a.y + a.h) / 100 * H,
              width:  a.w / 100 * W,
              height: a.h / 100 * H,
              borderColor: rgb(r, g, b),
              borderWidth: 1.5,
              color: rgb(r, g, b),
              opacity: 0.07,
              borderOpacity: 1,
              borderDashArray: pdfDashArray(a.lineStyle, 1.5),
            });
          }

          else if (a.type === 'circle') {
            const cx = (a.x + a.w / 2) / 100 * W;
            const cy = H - (a.y + a.h / 2) / 100 * H;
            const sw = Math.max(a.sw || 2, 1);
            page.drawEllipse({
              x: cx, y: cy,
              xScale: a.w / 100 * W / 2,
              yScale: a.h / 100 * H / 2,
              color: rgb(r, g, b),
              opacity: 0.09,
              borderColor: rgb(r, g, b),
              borderWidth: sw,
              borderDashArray: pdfDashArray(a.lineStyle, sw),
            });
          }

          else if (a.type === 'line') {
            const x1 = a.x1 / 100 * W, y1 = H - a.y1 / 100 * H;
            const x2 = a.x2 / 100 * W, y2 = H - a.y2 / 100 * H;
            const sw = Math.max(a.sw || 2, 1);
            page.drawLine({
              start: { x: x1, y: y1 },
              end:   { x: x2, y: y2 },
              color: rgb(r, g, b),
              thickness: sw,
              opacity: 0.9,
              dashArray: pdfDashArray(a.lineStyle, sw),
            });
          }

          else if (a.type === 'rectfill') {
            page.drawRectangle({
              x: a.x / 100 * W,
              y: H - (a.y + a.h) / 100 * H,
              width:  a.w / 100 * W,
              height: a.h / 100 * H,
              color: rgb(r, g, b),
              opacity: (a.opacity || 80) / 100,
              borderOpacity: 0,
            });
          }

          else if (a.type === 'stamp') {
            const sw_ = 100, sh_ = 30;
            const sx = a.x / 100 * W, sy = H - a.y / 100 * H - sh_;
            const stampColor = isHexColor(a.Color) ? a.Color : colorHex(a.Color);
            const { r: sr, g: sg, b: sb } = hexToRgb(stampColor);
            page.drawRectangle({
              x: sx, y: sy, width: sw_, height: sh_,
              color: rgb(sr, sg, sb), opacity: 0.12,
              borderColor: rgb(sr, sg, sb), borderWidth: 1.5, borderOpacity: 1,
            });
            const label = String(a.label || 'STAMP').toUpperCase();
            const tw = pdfFont.widthOfTextAtSize(label, 10);
            _drawPdfLabel(page, label, sx + (sw_ - tw) / 2, sy + sh_ / 2 - 4, rgb(sr, sg, sb), 10);
          }

          else if (a.type === 'image' && a.src) {
            const isPng = a.src.startsWith('data:image/png');
            const embedded = isPng ? await srcDoc.embedPng(a.src) : await srcDoc.embedJpg(a.src);
            page.drawImage(embedded, {
              x: a.x / 100 * W,
              y: H - (a.y + a.h) / 100 * H,
              width:  a.w / 100 * W,
              height: a.h / 100 * H,
            });
          }

          else if (a.type === 'strike') {
            // Strikethrough — horizontal line through middle
            const sx = a.x / 100 * W;
            const sy = H - (a.y + a.h / 2) / 100 * H;
            const ex = (a.x + a.w) / 100 * W;
            page.drawLine({
              start: { x: sx, y: sy },
              end:   { x: ex, y: sy },
              color: rgb(r, g, b),
              thickness: 2,
              opacity: 0.8,
            });
          }

          else if (a.type === 'arrow') {
            const x1 = a.x1 / 100 * W, y1 = H - a.y1 / 100 * H;
            const x2 = a.x2 / 100 * W, y2 = H - a.y2 / 100 * H;
            const sw = Math.max(a.sw || 2, 1);
            page.drawLine({
              start: { x: x1, y: y1 },
              end:   { x: x2, y: y2 },
              color: rgb(r, g, b),
              thickness: sw,
              opacity: 0.9,
              dashArray: pdfDashArray(a.lineStyle, sw),
            });
            // Arrowhead — small triangle at tip
            const angle = Math.atan2(y2 - y1, x2 - x1);
            const hs = sw * 4 + 4;
            const a1 = angle + Math.PI * 0.8;
            const a2 = angle - Math.PI * 0.8;
            page.drawLine({ start: { x: x2, y: y2 }, end: { x: x2 + Math.cos(a1) * hs, y: y2 + Math.sin(a1) * hs }, color: rgb(r,g,b), thickness: sw, opacity: 0.9 });
            page.drawLine({ start: { x: x2, y: y2 }, end: { x: x2 + Math.cos(a2) * hs, y: y2 + Math.sin(a2) * hs }, color: rgb(r,g,b), thickness: sw, opacity: 0.9 });
          }

          else if (a.type === 'measure') {
            const x1 = a.x1 / 100 * W, y1 = H - a.y1 / 100 * H;
            const x2 = a.x2 / 100 * W, y2 = H - a.y2 / 100 * H;
            // Measurement line (dashed look via two segments)
            page.drawLine({ start: { x: x1, y: y1 }, end: { x: x2, y: y2 }, color: rgb(0.49, 0.23, 0.93), thickness: 1, opacity: 0.8 });
            // End ticks
            const nx = -(y2 - y1), ny = x2 - x1;
            const len = Math.hypot(nx, ny) || 1;
            const tx = nx / len * 5, ty = ny / len * 5;
            page.drawLine({ start: { x: x1-tx, y: y1-ty }, end: { x: x1+tx, y: y1+ty }, color: rgb(0.49,0.23,0.93), thickness: 1 });
            page.drawLine({ start: { x: x2-tx, y: y2-ty }, end: { x: x2+tx, y: y2+ty }, color: rgb(0.49,0.23,0.93), thickness: 1 });
            // Label
            if (a.label) {
              const mx = (x1+x2)/2, my = (y1+y2)/2 + 8;
              _drawPdfLabel(page, a.label, mx, my, rgb(0.49,0.23,0.93), 8);
            }
          }

          else if (a.type === 'text') {
            const px = a.x / 100 * W;
            const py = H - a.y / 100 * H - 10;
            const text = a.text || '';
            // Colored badge background
            const { r: fr, g: fg, b: fb } = hexToRgb(cf);
            const badge_w = Math.min(text.length * 5.5 + 16, 180);
            const badge_h = 16;
            page.drawRectangle({
              x: px, y: py,
              width: badge_w, height: badge_h,
              color: rgb(fr, fg, fb),
              borderColor: rgb(r, g, b),
              borderWidth: 0.8,
              borderOpacity: 1,
              opacity: 0.92,
            });
            _drawPdfLabel(page, text.slice(0, 40) + (text.length > 40 ? '…' : ''), px + 4, py + 3, rgb(r, g, b), 7);
            // EMMa index badge
            const emmaIdx = getEmmaIndex(a.id);
            if (emmaIdx > 0 && !a.emmaExclude) {
              page.drawCircle({ x: px - 4, y: py + 8, size: 6, color: rgb(0.49, 0.23, 0.93), opacity: 0.9 });
              _drawPdfLabel(page, String(emmaIdx), px - 7, py + 4, rgb(1, 1, 1), 6);
            }
            // Leader arrow from the chosen box edge to its free point
            if (a.leaderEdge && a.leaderX !== undefined && a.leaderY !== undefined) {
              let fx = px, fy = py;
              if      (a.leaderEdge === 'top')    { fx = px + badge_w / 2; fy = py + badge_h; }
              else if (a.leaderEdge === 'bottom') { fx = px + badge_w / 2; fy = py; }
              else if (a.leaderEdge === 'left')   { fx = px; fy = py + badge_h / 2; }
              else if (a.leaderEdge === 'right')  { fx = px + badge_w; fy = py + badge_h / 2; }
              const tx = a.leaderX / 100 * W, ty = H - a.leaderY / 100 * H;
              page.drawLine({ start: { x: fx, y: fy }, end: { x: tx, y: ty }, color: rgb(r, g, b), thickness: 1.2, opacity: 0.9 });
              const ang = Math.atan2(ty - fy, tx - fx);
              const hs = 5;
              const ha1 = ang + Math.PI * 0.8, ha2 = ang - Math.PI * 0.8;
              page.drawLine({ start: { x: tx, y: ty }, end: { x: tx + Math.cos(ha1) * hs, y: ty + Math.sin(ha1) * hs }, color: rgb(r, g, b), thickness: 1.2, opacity: 0.9 });
              page.drawLine({ start: { x: tx, y: ty }, end: { x: tx + Math.cos(ha2) * hs, y: ty + Math.sin(ha2) * hs }, color: rgb(r, g, b), thickness: 1.2, opacity: 0.9 });
            }
          }

          else if (a.type === 'cloud') {
            // Cloud approximation — dashed rectangle with rounded feel
            page.drawRectangle({
              x: a.x / 100 * W,
              y: H - (a.y + a.h) / 100 * H,
              width:  a.w / 100 * W,
              height: a.h / 100 * H,
              borderColor: rgb(r, g, b),
              borderWidth: 2,
              color: rgb(r, g, b),
              opacity: 0.05,
              borderOpacity: 0.9,
            });
            // Cloud label
            _drawPdfLabel(page, '☁ Revision', a.x / 100 * W + 3, H - a.y / 100 * H - 3, rgb(r, g, b), 7);
          }

          else if (a.type === 'pen' || a.type === 'texthighlight') {
            // Draw freehand as connected line segments
            if (a.points && a.points.length >= 2) {
              const alpha = a.type === 'texthighlight' ? 0.4 : 0.85;
              const sw = Math.max(a.sw || 2, 1);
              for (let i = 0; i < a.points.length - 1; i++) {
                const p1 = a.points[i], p2 = a.points[i + 1];
                page.drawLine({
                  start: { x: p1.x * W, y: H - p1.y * H },
                  end:   { x: p2.x * W, y: H - p2.y * H },
                  color: rgb(r, g, b),
                  thickness: sw,
                  opacity: alpha,
                });
              }
            }
          }

          else if (a.type === 'area') {
            // Polygon fill + border
            if (a.points && a.points.length >= 3) {
              // pdf-lib doesn't have drawPolygon, approximate with lines
              for (let i = 0; i < a.points.length; i++) {
                const p1 = a.points[i];
                const p2 = a.points[(i + 1) % a.points.length];
                page.drawLine({
                  start: { x: p1.x * W, y: H - p1.y * H },
                  end:   { x: p2.x * W, y: H - p2.y * H },
                  color: rgb(r, g, b),
                  thickness: 1.5,
                  opacity: 0.8,
                });
              }
              // Area label at centroid
              if (a.label) {
                const cx = a.points.reduce((s, p) => s + p.x, 0) / a.points.length * W;
                const cy = H - a.points.reduce((s, p) => s + p.y, 0) / a.points.length * H;
                _drawPdfLabel(page, a.label, cx - 20, cy, rgb(r, g, b), 8);
              }
            }
          }
        } catch(annotErr) { /* skip individual annotation errors silently */ }
      }
    }

    const pdfBytesOut = await srcDoc.save();
    const fname = (pdfName || 'drawing').replace(/\.pdf$/i, '') + '_annotated.pdf';
    dl(pdfBytesOut, fname);
    toast(`✓ Exported annotated PDF — ${annots.length} annotation${annots.length !== 1 ? 's' : ''} rendered`);
  } catch(err) {
    toast('Export failed: ' + err.message);
    console.error('[EngDoc] exportAnnotatedPdf:', err);
  }
}

// Helper: draw small text on a pdf-lib page (pdf-lib requires embedded font for non-latin;
// we use the built-in Helvetica which covers ASCII)
function _drawPdfLabel(page, text, x, y, color, size = 8) {
  try {
    page.drawText(String(text).replace(/[^\x20-\x7E]/g, '?'), {
      x, y,
      size,
      color,
      opacity: 0.95,
    });
  } catch(e) { /* skip if font issue */ }
}

/* ═══════════════════════════════════════════════
   SHEETJS LOADER
═══════════════════════════════════════════════ */
async function loadSheetJs() {
  if (window.XLSX) return;
  await new Promise((res, rej) => {
    const s = document.createElement('script');
    s.src = 'https://cdnjs.cloudflare.com/ajax/libs/xlsx/0.18.5/xlsx.full.min.js';
    s.onload = res; s.onerror = rej;
    document.head.appendChild(s);
  });
}

/* ═══════════════════════════════════════════════
   TABLE EXTRACT
   User drags a box (tool 'tableextract') around a
   table on the drawing. We first try to build a grid
   from the page's embedded text (pdfTextContent, already
   extracted at load — see extractPdfText). If the box
   has no embedded text (scanned/image page) we offer an
   OCR pass (Tesseract.js, lazy-loaded) over just that
   cropped region. Either path clusters word positions
   into rows/columns by gap-detection, then shows an
   editable preview before exporting to .xlsx.
═══════════════════════════════════════════════ */
let teGrid = [];        // current editable grid: string[][]
let tePageNum = null;
let teBox = null;       // {x,y,w,h} in 0-100 % of page, as drawn

async function loadTesseract() {
  if (window.Tesseract) return;
  await new Promise((res, rej) => {
    const s = document.createElement('script');
    s.src = 'https://cdn.jsdelivr.net/npm/tesseract.js@5.0.4/dist/tesseract.min.js';
    s.onload = res; s.onerror = rej;
    document.head.appendChild(s);
  });
}

// Cluster a flat list of numbers into groups separated by unusually large gaps.
// Returns the cluster means, ascending. Used for column positions, where real
// columns genuinely do have a small-gap-within/large-gap-between pattern.
function teClusterValues(values, minGap) {
  const sorted = [...values].sort((a, b) => a - b);
  if (!sorted.length) return [];
  const diffs = [];
  for (let i = 1; i < sorted.length; i++) diffs.push(sorted[i] - sorted[i - 1]);
  // Low percentile, not the median: in a table with several single-token
  // numeric columns and one wordy column, most gaps ARE column gaps, so the
  // median gap is itself a column gap — using it as the "noise" estimate
  // would merge real columns together. The smallest gaps reliably represent
  // noise/word-spacing, wherever it occurs.
  let typicalGap = minGap;
  if (diffs.length) {
    const sd = [...diffs].sort((a, b) => a - b);
    typicalGap = sd[Math.floor(sd.length * 0.25)];
  }
  const gapThresh = Math.max(typicalGap * 2.2, minGap);
  const clusters = [[sorted[0]]];
  for (let i = 1; i < sorted.length; i++) {
    if (sorted[i] - sorted[i - 1] > gapThresh) clusters.push([sorted[i]]);
    else clusters[clusters.length - 1].push(sorted[i]);
  }
  return clusters.map(c => c.reduce((s, v) => s + v, 0) / c.length);
}

// Row positions in a real table are usually near-uniform pitch — there's no
// small/large gap dichotomy to exploit like there is for columns, so a gap
// clustering approach collapses evenly-spaced rows into one giant group.
// Instead, merge items into the same row using an absolute tolerance based
// on font height (text on the same line sits within a fraction of a line
// height of its neighbours; a genuinely different line is offset by roughly
// a full line height).
function teClusterRows(items) {
  const heights = items.map(it => it.h).filter(h => h > 0).sort((a, b) => a - b);
  const typicalH = heights.length ? heights[Math.floor(heights.length / 2)] : 0.012;
  const rowEps = Math.max(typicalH, 0.003);
  const sortedY = [...items.map(it => it.y)].sort((a, b) => a - b);
  const groups = [[sortedY[0]]];
  for (let i = 1; i < sortedY.length; i++) {
    const lastGroup = groups[groups.length - 1];
    if (sortedY[i] - lastGroup[lastGroup.length - 1] <= rowEps) lastGroup.push(sortedY[i]);
    else groups.push([sortedY[i]]);
  }
  return groups.map(g => g.reduce((s, v) => s + v, 0) / g.length);
}

function teNearestIndex(reps, val) {
  let best = 0, bestD = Infinity;
  reps.forEach((r, i) => { const d = Math.abs(val - r); if (d < bestD) { bestD = d; best = i; } });
  return best;
}

// items: [{str, x, y, w, h}] with x,y,w,h normalised 0..1 relative to the
// selection box (w = item width, h = font height — used to tell "space
// between words in one cell" apart from "gap between columns"; without it,
// a multi-word cell like "Steel beam UB" gets shredded into separate columns
// by word). Two-stage: (1) group into rows, merge adjacent words in each row
// into runs wherever the gap between them looks like normal word-spacing;
// (2) cluster the resulting run start-positions (far fewer, cleaner) into
// columns.
function teBuildGrid(items) {
  if (!items.length) return [];
  const rowReps = teClusterRows(items);
  const rows = rowReps.map(() => []);
  items.forEach(it => rows[teNearestIndex(rowReps, it.y)].push(it));
  rows.forEach(row => row.sort((a, b) => a.x - b.x));

  // Merge threshold grounded in font height, not percentile-of-gaps: a real
  // table's own column gaps can legitimately be as small as (or smaller
  // than) typical word-spacing, so deriving the threshold from this
  // selection's own gap statistics is unreliable — it risks merging real,
  // tightly-packed columns together, which is far harder for the user to
  // undo afterwards than the reverse (a multi-word cell landing in two
  // columns, which is a one-click merge in the editable preview).
  const heights = items.map(it => it.h).filter(h => h > 0).sort((a, b) => a - b);
  const typicalH = heights.length ? heights[Math.floor(heights.length / 2)] : 0.012;
  const mergeThresh = typicalH * 0.25;

  const runsPerRow = rows.map(row => {
    const runs = [];
    row.forEach(it => {
      const last = runs[runs.length - 1];
      if (last && it.x - last.endX <= mergeThresh) {
        last.str += ' ' + it.str;
        last.endX = it.x + (it.w || 0);
      } else {
        runs.push({ str: it.str, x: it.x, endX: it.x + (it.w || 0) });
      }
    });
    return runs;
  });

  const colReps = teClusterValues(runsPerRow.flatMap(runs => runs.map(r => r.x)), 0.015);
  const grid = runsPerRow.map(runs => {
    const cells = new Array(colReps.length).fill('');
    runs.forEach(r => {
      const c = teNearestIndex(colReps, r.x);
      cells[c] = cells[c] ? cells[c] + ' ' + r.str : r.str;
    });
    return cells;
  });
  return teMergeSparseAdjacentColumns(grid);
}

// A header label is sometimes positioned just far enough from its own
// column's data (e.g. differently justified, or simply a longer label than
// any value below it) that it lands one column cluster away from its data —
// producing a spurious extra column that's essentially empty except for a
// header row or two, sitting right next to the real (densely populated)
// column. Detect that pattern directly: if two adjacent columns never both
// have content in the same row, AND one of them is populated in only a
// small fraction of rows (i.e. it's basically "just the header"), they're
// almost certainly the same logical column — merge them.
function teMergeSparseAdjacentColumns(grid) {
  if (!grid.length || !grid[0].length) return grid;
  const nCols = grid[0].length, nRows = grid.length;
  const counts = new Array(nCols).fill(0);
  for (let r = 0; r < nRows; r++) for (let c = 0; c < nCols; c++) if (grid[r][c]) counts[c]++;
  const keep = new Array(nCols).fill(true);
  for (let c = 0; c < nCols - 1; c++) {
    if (!keep[c]) continue;
    const sparse = Math.min(counts[c], counts[c + 1]);
    if (sparse === 0 || sparse / nRows > 0.15) continue;
    let conflict = false;
    for (let r = 0; r < nRows; r++) { if (grid[r][c] && grid[r][c + 1]) { conflict = true; break; } }
    if (conflict) continue;
    for (let r = 0; r < nRows; r++) { if (grid[r][c + 1]) grid[r][c] = grid[r][c] ? grid[r][c] + ' ' + grid[r][c + 1] : grid[r][c + 1]; }
    keep[c + 1] = false;
    counts[c] = Math.max(counts[c], counts[c + 1]);
  }
  return grid.map(row => row.filter((_, c) => keep[c]));
}

async function openTableExtractModal(pageNum, x, y, w, h) {
  tePageNum = pageNum;
  teBox = { x, y, w, h };
  const status = document.getElementById('te-status');
  const ocrPrompt = document.getElementById('te-ocr-prompt');
  ocrPrompt.style.display = 'none';
  status.textContent = 'Reading text from the selected area…';
  openM('mtableextract');

  const boxX = x / 100, boxY = y / 100, boxW = w / 100, boxH = h / 100;
  const pageItems = pdfTextContent[pageNum] || [];
  const items = pageItems
    .filter(it => it.x >= boxX && it.x <= boxX + boxW && it.y >= boxY && it.y <= boxY + boxH)
    .map(it => ({ str: it.str, x: (it.x - boxX) / boxW, y: (it.y - boxY) / boxH, w: (it.width || 0) / boxW, h: (it.fontSize || 0) / boxH }));

  if (items.length >= 4) {
    teGrid = teBuildGrid(items);
    status.textContent = `Detected ${teGrid.length} row(s) × ${teGrid[0]?.length || 0} column(s) from embedded text. Edit cells below if needed.`;
    teRenderGrid();
  } else {
    teGrid = [];
    teRenderGrid();
    status.textContent = 'No embedded text found in this area.';
    ocrPrompt.style.display = 'block';
  }
}

async function runTableOcr() {
  const status = document.getElementById('te-status');
  const btn = document.getElementById('te-run-ocr-btn');
  btn.disabled = true; btn.textContent = 'Running OCR…';
  status.textContent = 'Loading OCR engine…';
  try {
    await loadTesseract();

    const OCR_SCALE = 3;
    const page = await pdf.getPage(tePageNum);
    const vp = page.getViewport({ scale: OCR_SCALE });
    const fullCanvas = document.createElement('canvas');
    fullCanvas.width = vp.width; fullCanvas.height = vp.height;
    await page.render({ canvasContext: fullCanvas.getContext('2d'), viewport: vp }).promise;

    const cropX = (teBox.x / 100) * vp.width;
    const cropY = (teBox.y / 100) * vp.height;
    const cropW = (teBox.w / 100) * vp.width;
    const cropH = (teBox.h / 100) * vp.height;
    const cropCanvas = document.createElement('canvas');
    cropCanvas.width = cropW; cropCanvas.height = cropH;
    cropCanvas.getContext('2d').drawImage(fullCanvas, cropX, cropY, cropW, cropH, 0, 0, cropW, cropH);

    status.textContent = 'Recognising text…';
    const { data } = await Tesseract.recognize(cropCanvas, 'eng');
    const items = (data.words || [])
      .filter(w => w.text && w.text.trim())
      .map(w => ({
        str: w.text.trim(),
        x: w.bbox.x0 / cropW,
        y: ((w.bbox.y0 + w.bbox.y1) / 2) / cropH,
        w: (w.bbox.x1 - w.bbox.x0) / cropW,
        h: (w.bbox.y1 - w.bbox.y0) / cropH,
      }));

    if (!items.length) {
      status.textContent = 'OCR found no text in this area.';
      btn.disabled = false; btn.textContent = 'Run OCR';
      return;
    }
    teGrid = teBuildGrid(items);
    document.getElementById('te-ocr-prompt').style.display = 'none';
    status.textContent = `OCR detected ${teGrid.length} row(s) × ${teGrid[0]?.length || 0} column(s). Edit cells below if needed.`;
    teRenderGrid();
  } catch (err) {
    status.textContent = 'OCR failed: ' + err.message;
    btn.disabled = false; btn.textContent = 'Run OCR';
    console.error('[EngDoc] runTableOcr:', err);
  }
}

function teRenderGrid() {
  const wrap = document.getElementById('te-grid-wrap');
  if (!teGrid.length) {
    wrap.innerHTML = '<div style="padding:16px;Color:var(--gray-500);font-size:12.5px">No table data yet — use "+ Row" / "+ Column" to start one manually, or run OCR above.</div>';
    return;
  }
  let html = '<table style="border-collapse:collapse;width:100%">';
  teGrid.forEach((row, r) => {
    html += '<tr>';
    row.forEach((cell, c) => {
      html += `<td contenteditable="true" data-r="${r}" data-c="${c}" oninput="teCellEdit(this)"
                 style="border:1px solid var(--gray-200);padding:5px 8px;font-size:12px;min-width:70px">${
                   String(cell).replace(/&/g,'&amp;').replace(/</g,'&lt;')
                 }</td>`;
    });
    html += '</tr>';
  });
  html += '</table>';
  wrap.innerHTML = html;
}

function teCellEdit(el) {
  const r = parseInt(el.dataset.r), c = parseInt(el.dataset.c);
  if (teGrid[r]) teGrid[r][c] = el.textContent;
}

function teAddRow() {
  const cols = teGrid[0]?.length || 1;
  teGrid.push(new Array(cols).fill(''));
  teRenderGrid();
}
function teAddCol() {
  if (!teGrid.length) teGrid.push(['']);
  else teGrid.forEach(row => row.push(''));
  teRenderGrid();
}
function teDelRow() {
  if (teGrid.length) teGrid.pop();
  teRenderGrid();
}
function teDelCol() {
  if (teGrid[0] && teGrid[0].length > 1) teGrid.forEach(row => row.pop());
  teRenderGrid();
}

async function exportTableToExcel() {
  if (!teGrid.length) { toast('Nothing to export'); return; }
  try {
    await loadSheetJs();
    const wb = XLSX.utils.book_new();
    const ws = XLSX.utils.aoa_to_sheet(teGrid);
    XLSX.utils.book_append_sheet(wb, ws, 'Table');
    const buf = XLSX.write(wb, { bookType: 'xlsx', type: 'array' });
    const blob = new Blob([buf], { type: 'application/octet-stream' });
    const url = URL.createObjectURL(blob);
    const base = (pdfName || 'document').replace(/\.pdf$/i, '');
    const a = document.createElement('a');
    a.href = url; a.download = `${base}_table_p${tePageNum}.xlsx`;
    a.click(); URL.revokeObjectURL(url);
    closeM('mtableextract');
    toast('Table exported to Excel');
  } catch (err) {
    toast('Export failed: ' + err.message);
    console.error('[EngDoc] exportTableToExcel:', err);
  }
}

/* ═══════════════════════════════════════════════
   EMMA LIVE REGISTER
   emmaRows mirrors annots but holds the extra
   Checking Review fields (cat, type, reply, etc.)
   Keyed by annot.id so they stay in sync.
═══════════════════════════════════════════════ */
let emmaRows = {};      // { annotId: { cat, commentType, accepted, reply, closedOut, notes, docNo, rev } }
let emmaEditId = null;  // annotId being edited in the modal
let emmaTemplateBuf = null; // ArrayBuffer of loaded .xlsm template

function emmaRowForAnnot(a) {
  if (!emmaRows[a.id]) emmaRows[a.id] = { cat:'', commentType:'', accepted:'', reply:'', closedOut:'No', notes:'',
    docNo: document.getElementById('emma-doc-no').value || '',
    rev:   document.getElementById('emma-rev-no').value || '' };
  return emmaRows[a.id];
}

function updateEmmaRegister() {
  const register = document.getElementById('emma-register');
  const empty    = document.getElementById('emma-empty');
  // Only note/text/measure annotations that aren't excluded go into EMMA
  const emmaAnnots = annots.filter(a =>
    (a.type === 'text' || a.type === 'measure') && !a.emmaExclude
  );

  // Remove existing rows (not the empty message)
  register.querySelectorAll('.emma-row').forEach(el => el.remove());

  document.getElementById('emma-count-label').textContent = `${emmaAnnots.length} comment${emmaAnnots.length !== 1 ? 's' : ''}`;

  if (!emmaAnnots.length) { empty.style.display = 'block'; return; }
  empty.style.display = 'none';

  emmaAnnots.forEach((a, i) => {
    const row = emmaRowForAnnot(a);
    const div = document.createElement('div');
    div.className = 'emma-row'; div.dataset.id = a.id;

    const catClass = `emma-cat-${row.cat || ''}`;
    const stClass  = row.closedOut === 'Yes' ? 'emma-closed-st' : 'emma-open-st';
    const stLabel  = row.closedOut === 'Yes' ? 'Closed' : 'Open';

    div.innerHTML = `
      <div class="emma-row-num">${i + 1}</div>
      <div>
        <div class="emma-row-comment">${a.text || (a.type === 'measure' ? a.label || '—' : '—')}</div>
        <div class="emma-row-doc">Pg ${a.pageNum} · ${a.author || '—'}</div>
        ${row.reply ? `<div class="emma-row-reply"><span style="Color:var(--blue-500);font-weight:600">↩ </span>${row.reply}</div>` : ''}
      </div>
      <div><span class="emma-cat-badge ${catClass}">${row.cat || '—'}</span></div>
      <div style="font-size:9px;Color:var(--gray-500);padding-top:3px">${row.commentType || '—'}</div>
      <div><span class="emma-status ${stClass}">${stLabel}</span></div>`;

    div.addEventListener('click', () => openEmmaRowEdit(a.id));
    register.insertBefore(div, empty);
  });
}

function openEmmaRowEdit(annotId) {
  emmaEditId = annotId;
  const a   = annots.find(x => x.id === annotId); if (!a) return;
  const row = emmaRowForAnnot(a);

  document.getElementById('er-comment').value  = a.text || (a.type === 'measure' ? a.label || '' : '');
  document.getElementById('er-docno').value    = row.docNo || document.getElementById('emma-doc-no').value || '';
  document.getElementById('er-rev').value      = row.rev   || document.getElementById('emma-rev-no').value  || '';
  document.getElementById('er-cat').value      = row.cat      || '';
  document.getElementById('er-type').value     = row.commentType || '';
  document.getElementById('er-accepted').value = row.accepted   || '';
  document.getElementById('er-closed').value   = row.closedOut  || 'No';
  document.getElementById('er-reply').value    = row.reply  || '';
  document.getElementById('er-notes').value    = row.notes  || '';
  openM('memma-row');
}

function saveEmmaRow() {
  if (emmaEditId == null) { closeM('memma-row'); return; }
  const a = annots.find(x => x.id === emmaEditId); if (!a) { closeM('memma-row'); return; }

  // Update comment text
  const newText = document.getElementById('er-comment').value.trim();
  if (newText && a.type === 'text') { a.text = newText; syncAnnots(); updateAnnotPanel(); }

  // Save EMMA fields
  emmaRows[emmaEditId] = {
    docNo:       document.getElementById('er-docno').value.trim(),
    rev:         document.getElementById('er-rev').value.trim(),
    cat:         document.getElementById('er-cat').value,
    commentType: document.getElementById('er-type').value,
    accepted:    document.getElementById('er-accepted').value,
    closedOut:   document.getElementById('er-closed').value,
    reply:       document.getElementById('er-reply').value.trim(),
    notes:       document.getElementById('er-notes').value.trim(),
  };

  closeM('memma-row');
  updateEmmaRegister();
  toast('EMMA row updated');
}

/* ── Load existing .xlsm template to pre-fill project info ── */
async function loadEmmaTemplate(e) {
  const file = e.target.files[0]; if (!file) return;
  emmaTemplateBuf = await file.arrayBuffer();
  // Try to read project info using SheetJS
  try {
    await loadSheetJs();
    const wb = XLSX.read(emmaTemplateBuf, { type: 'array' });
    const ws = wb.Sheets['Document Check Sheet'];
    if (ws) {
      const g = (cell) => ws[cell] ? (ws[cell].v ?? '') : '';
      // D5 = Specific Design, C4 = Project Title, D6 = Discipline, K5 = Rev, K6 = CheckSheetNo
      const specDesign = g('D5');
      const projTitle  = g('C4') || g('D4') || '';
      const discipline = g('D6');
      const rev        = g('K5');
      const chkNo      = g('K6');

      if (specDesign) document.getElementById('emma-specific').value   = specDesign;
      if (projTitle)  document.getElementById('emma-proj-title').value = projTitle;
      if (discipline) document.getElementById('emma-discipline').value = discipline;
      if (rev)        document.getElementById('emma-rev-no').value     = typeof rev === 'string' ? rev : String(rev);
      if (chkNo)      document.getElementById('emma-chk-no').value     = chkNo;
    }
    const ws2 = wb.Sheets['Checking Review'];
    if (ws2) {
      const g = (cell) => ws2[cell] ? (ws2[cell].v ?? '') : '';
      const projNo = g('D3');
      const projNm = g('D4');
      if (projNo && projNo !== 0) document.getElementById('emma-proj-no').value    = String(projNo);
      if (projNm && projNm !== 0) document.getElementById('emma-proj-title').value = String(projNm);
    }
    toast('✓ Template loaded and saved — will be remembered next time');
  } catch(err) {
    toast('Could not read template metadata: ' + err.message);
  }
  // Persist to IDB so it survives page reload
  await idbSaveTemplate(emmaTemplateBuf, file.name);
  updateTemplateUI(file.name);
  e.target.value = '';
}

/* ── Export into real .xlsm template ── */
async function exportEmma() {
  const emmaAnnots = annots.filter(a =>
    (a.type === 'text' || a.type === 'measure') && !a.emmaExclude
  );
  if (!emmaAnnots.length) { toast('No EMMA comments to export'); return; }
  if (!emmaTemplateBuf)   { toast('⚠ No template loaded — load your Checksheet.xlsm via the EMMA panel first', 6000); return; }

  closeM('memma');
  toast('Building EMMA Checksheet…');

  try {
    await loadJSZip();

    const docTitle   = document.getElementById('emma-proj-title').value.trim();
    const projNo     = document.getElementById('emma-proj-no').value.trim();
    const discipline = document.getElementById('emma-discipline').value;
    const docNo      = document.getElementById('emma-doc-no').value.trim();
    const rev        = document.getElementById('emma-rev-no').value.trim();
    const specific   = document.getElementById('emma-specific').value.trim();
    const chkNo      = document.getElementById('emma-chk-no').value.trim();

    const zip = await JSZip.loadAsync(emmaTemplateBuf);

    // ── Helper: find worksheet file for a named sheet ──
    async function getSheetPath(sheetName) {
      const wbXml   = await zip.file('xl/workbook.xml').async('string');
      const relsXml = await zip.file('xl/_rels/workbook.xml.rels').async('string');
      const esc = s => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
      const m1 = wbXml.match(new RegExp('<sheet[^>]+name="' + esc(sheetName) + '"[^>]+r:id="([^"]+)"'));
      const m2 = wbXml.match(new RegExp('<sheet[^>]+r:id="([^"]+)"[^>]+name="' + esc(sheetName) + '"'));
      const rid = (m1 || m2)?.[1]; if (!rid) return null;
      const rm = relsXml.match(new RegExp('Id="' + rid + '"[^>]+Target="([^"]+)"'));
      if (!rm) return null;
      const t = rm[1].replace(/^\/?xl\//, '');
      return 'xl/' + t;
    }

    // ── Shared strings: read existing, add new, write back ──
    // This is the ONLY correct way to write text into styled cells —
    // the cell keeps its s= style attribute and we just change the shared string index.
    let ssXml = await zip.file('xl/sharedStrings.xml').async('string');

    // Parse existing strings into an array
    const ssEntries = [];
    const siRe = /<si>([\s\S]*?)<\/si>/g;
    let siM;
    while ((siM = siRe.exec(ssXml)) !== null) {
      // Extract text — may be <t> or multiple <r><t> runs
      const tVals = [...siM[1].matchAll(/<t[^>]*>([^<]*)<\/t>/g)].map(x => x[1]);
      ssEntries.push(tVals.join(''));
    }

    // Look up or add a string, return its index
    function ssIndex(str) {
      const s = String(str);
      const existing = ssEntries.indexOf(s);
      if (existing !== -1) return existing;
      // Append new entry
      ssEntries.push(s);
      const xmlEsc = s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
      const needsSpace = s !== s.trim();
      const tAttr = needsSpace ? ' xml:space="preserve"' : '';
      // Insert before </sst>
      ssXml = ssXml.replace(/<\/sst>/, '<si><t' + tAttr + '>' + xmlEsc + '</t></si></sst>');
      return ssEntries.length - 1;
    }

    // Update the count attribute on <sst>
    function finaliseSharedStrings() {
      const count = ssEntries.length;
      ssXml = ssXml.replace(/(<sst[^>]+count=")[^"]*(")/,  '$1' + count + '$2');
      ssXml = ssXml.replace(/(<sst[^>]+uniqueCount=")[^"]*(")/,  '$1' + count + '$2');
      zip.file('xl/sharedStrings.xml', ssXml);
    }

    // ── Core cell writer ──
    // Finds <c r="REF" ...> and updates ONLY the <v> content and t= attribute.
    // The s= style attribute and all other attributes are left completely untouched.
    function writeSharedStr(xml, cellRef, strIndex) {
      // Match existing cell — may be self-closing or have content
      const cellRe = new RegExp(
        '(<c\\s+r="' + cellRef + '"(?:\\s+[^>]*)?)(?:\\s*/>|>((?:[\\s\\S]*?))<\\/c>)',
        'i'
      );
      const replacement = (match, openTag, _inner) => {
        // Remove existing t= attribute, add t="s"
        let tag = openTag.replace(/\s+t="[^"]*"/, '');
        return tag + ' t="s"><v>' + strIndex + '</v></c>';
      };
      if (cellRe.test(xml)) return xml.replace(cellRe, replacement);

      // Cell doesn't exist — insert into its row
      const rowNum = cellRef.match(/\d+$/)[0];
      const rowRe  = new RegExp('(<row\\b[^>]*\\br="' + rowNum + '"[^>]*>)([\\s\\S]*?)(</row>)');
      return xml.replace(rowRe, (_, open, body, close) =>
        open + body + '<c r="' + cellRef + '" t="s"><v>' + strIndex + '</v></c>' + close
      );
    }

    // Write a number into a cell (no t= attribute needed for numbers)
    function writeNum(xml, cellRef, num) {
      const cellRe = new RegExp(
        '(<c\\s+r="' + cellRef + '"(?:\\s+[^>]*)?)(?:\\s*/>|>(?:[\\s\\S]*?)<\\/c>)',
        'i'
      );
      const replacement = (_, openTag) => {
        let tag = openTag.replace(/\s+t="[^"]*"/, '');
        return tag + '><v>' + num + '</v></c>';
      };
      if (cellRe.test(xml)) return xml.replace(cellRe, replacement);
      const rowNum = cellRef.match(/\d+$/)[0];
      const rowRe  = new RegExp('(<row\\b[^>]*\\br="' + rowNum + '"[^>]*>)([\\s\\S]*?)(</row>)');
      return xml.replace(rowRe, (_, open, body, close) =>
        open + body + '<c r="' + cellRef + '"><v>' + num + '</v></c>' + close
      );
    }

    // ── Patch Document Check Sheet ──
    // D3-D7 in Checking Review are FORMULAS that pull from here — write here only.
    const dcsPath = await getSheetPath('Document Check Sheet');
    if (dcsPath) {
      let dcsXml = await zip.file(dcsPath).async('string');
      if (docTitle)   dcsXml = writeSharedStr(dcsXml, 'D4',  ssIndex(docTitle));
      if (projNo)     dcsXml = writeNum(dcsXml,       'I4',  projNo);
      if (specific)   dcsXml = writeSharedStr(dcsXml, 'D5',  ssIndex(specific));
      if (rev)        dcsXml = writeSharedStr(dcsXml, 'K5',  ssIndex(rev));
      if (discipline) dcsXml = writeSharedStr(dcsXml, 'D6',  ssIndex(discipline));
      if (chkNo)      dcsXml = writeSharedStr(dcsXml, 'K6',  ssIndex(chkNo));
      // Date in G5 — store as a number (Excel serial date)
      const today = new Date();
      const serial = Math.floor((today - new Date(1899, 11, 30)) / 86400000);
      dcsXml = writeNum(dcsXml, 'G5', serial);
      zip.file(dcsPath, dcsXml);
    }

    // ── Patch Checking Review data rows ──
    // Rows start at 11. Only write C (Doc No), E (Date), F (Designer), G (Checker),
    // H (Cat), I (Comment), J (Type), K (Accepted), L (Reply), M (Closed Out), N (Notes).
    // Column B is auto-numbered by the template formula, D is formula from DCS.
    const crPath = await getSheetPath('Checking Review');
    if (!crPath) { toast('Checking Review sheet not found in template', 5000); return; }
    let crXml = await zip.file(crPath).async('string');

    const todayStr = new Date().toLocaleDateString('en-GB');
    emmaAnnots.forEach((a, idx) => {
      const r   = 11 + idx;
      const row = emmaRowForAnnot(a);
      const comment = a.text || (a.type === 'measure' ? a.label || '' : '');
      const dateStr = a.timestamp ? new Date(a.timestamp).toLocaleDateString('en-GB') : todayStr;

      crXml = writeSharedStr(crXml, 'C' + r, ssIndex(row.docNo || docNo || ''));
      crXml = writeSharedStr(crXml, 'E' + r, ssIndex(dateStr));
      crXml = writeSharedStr(crXml, 'F' + r, ssIndex(a.author || currentAuthor || ''));
      crXml = writeSharedStr(crXml, 'G' + r, ssIndex(currentAuthor || ''));
      crXml = writeSharedStr(crXml, 'H' + r, ssIndex(row.cat          || ''));
      crXml = writeSharedStr(crXml, 'I' + r, ssIndex(comment));
      crXml = writeSharedStr(crXml, 'J' + r, ssIndex(row.commentType  || ''));
      crXml = writeSharedStr(crXml, 'K' + r, ssIndex(row.accepted     || ''));
      crXml = writeSharedStr(crXml, 'L' + r, ssIndex(row.reply        || ''));
      crXml = writeSharedStr(crXml, 'M' + r, ssIndex(row.closedOut    || 'No'));
      crXml = writeSharedStr(crXml, 'N' + r, ssIndex(row.notes        || ''));
    });
    zip.file(crPath, crXml);

    // Write updated shared strings back
    finaliseSharedStrings();

    // Re-zip and download
    const outBytes = await zip.generateAsync({
      type: 'uint8array',
      compression: 'DEFLATE',
      compressionOptions: { level: 6 },
      mimeType: 'application/vnd.ms-excel.sheet.macroEnabled.12'
    });

    const fname = (chkNo || (docNo ? docNo.replace(/[^\w-]/g,'_') : 'EMMA')) + '_Checksheet.xlsm';
    dl(outBytes, fname);
    toast('✓ EMMA Checksheet exported — ' + emmaAnnots.length + ' comment' + (emmaAnnots.length !== 1 ? 's' : ''));

  } catch(err) {
    console.error('[EngDoc] exportEmma:', err);
    toast('Export failed: ' + err.message);
  }
}

async function loadJSZip() {
  if (window.JSZip) return;
  await new Promise((res, rej) => {
    const s = document.createElement('script');
    s.src = 'https://cdnjs.cloudflare.com/ajax/libs/jszip/3.10.1/jszip.min.js';
    s.onload = res; s.onerror = rej;
    document.head.appendChild(s);
  });
}

function openEmmaExport() {
  const emmaAnnots = annots.filter(a =>
    (a.type === 'text' || a.type === 'measure') && !a.emmaExclude
  );
  if (!emmaAnnots.length) {
    toast('No EMMA comments to export — add Notes or Text annotations (with EMMA checked) first'); return;
  }
  const projTitle  = document.getElementById('emma-proj-title').value.trim() || '(not set)';
  const docNo      = document.getElementById('emma-doc-no').value.trim()     || '(not set)';
  const rev        = document.getElementById('emma-rev-no').value.trim()     || '(not set)';
  const chkNo      = document.getElementById('emma-chk-no').value.trim()     || '(not set)';
  const openCount  = emmaAnnots.filter(a => (emmaRows[a.id]?.closedOut || 'No') !== 'Yes').length;
  const closedCount = emmaAnnots.length - openCount;
  document.getElementById('emma-export-summary').innerHTML =
    `Project: ${projTitle}<br>Doc No: ${docNo} · Rev: ${rev}<br>Check Sheet: ${chkNo}<br>` +
    `Comments: ${emmaAnnots.length} total (${openCount} open, ${closedCount} closed)`;

  // Template status
  const statusEl = document.getElementById('emma-template-status');
  if (emmaTemplateBuf) {
    statusEl.style.cssText = 'background:#dcfce7;Color:#166534;border:1px solid #bbf7d0;margin-top:10px;padding:8px 10px;border-radius:4px;font-size:12px;font-weight:500';
    statusEl.textContent = '✓ Template loaded — all formatting, Colors and macros will be preserved';
  } else {
    statusEl.style.cssText = 'background:#fee2e2;Color:#b91c1c;border:1px solid #fca5a5;margin-top:10px;padding:8px 10px;border-radius:4px;font-size:12px;font-weight:500';
    statusEl.textContent = '⚠ No template loaded — load your Checksheet.xlsm via the EMMA panel → Load Template before exporting. Without it the formatting will be lost.';
  }
  openM('memma');
}

// Keep old function name as alias in case called anywhere
const exportXlsx = openEmmaExport;

// ═══════════════════════════════════════════════
//  DARK MODE
// ═══════════════════════════════════════════════
function toggleDark() {
  const isDark = document.body.classList.toggle('dark');
  localStorage.setItem('engdoc_dark', isDark ? '1' : '0');
  document.getElementById('dark-icon-moon').style.display = isDark ? 'none' : '';
  document.getElementById('dark-icon-sun').style.display  = isDark ? '' : 'none';
}
// Restore dark mode on load
if (localStorage.getItem('engdoc_dark') === '1') toggleDark();

// ═══════════════════════════════════════════════
//  INDEXEDDB AUTO-SAVE
// ═══════════════════════════════════════════════
let idb = null;
function openIDB() {
  return new Promise((res, rej) => {
    const req = indexedDB.open('engdoc', 2); // v2 adds templates store
    req.onupgradeneeded = e => {
      const db = e.target.result;
      if (!db.objectStoreNames.contains('sessions'))  db.createObjectStore('sessions',  { keyPath: 'id' });
      if (!db.objectStoreNames.contains('templates')) db.createObjectStore('templates', { keyPath: 'id' });
    };
    req.onsuccess = e => { idb = e.target.result; res(idb); };
    req.onerror = () => rej(req.error);
  });
}

async function idbSaveTemplate(buf, filename) {
  if (!idb) return;
  try {
    const tx = idb.transaction('templates', 'readwrite');
    tx.objectStore('templates').put({ id: 'emma-template', buf, filename, savedAt: new Date().toISOString() });
  } catch(e) { /* silent */ }
}

async function idbLoadTemplate() {
  if (!idb) return null;
  return new Promise(res => {
    try {
      const tx = idb.transaction('templates', 'readonly');
      const req = tx.objectStore('templates').get('emma-template');
      req.onsuccess = () => res(req.result || null);
      req.onerror = () => res(null);
    } catch(e) { res(null); }
  });
}

async function idbClearTemplate() {
  if (!idb) return;
  try {
    const tx = idb.transaction('templates', 'readwrite');
    tx.objectStore('templates').delete('emma-template');
  } catch(e) { /* silent */ }
}

async function idbSave() {
  if (!idb || !pdfName) return;
  try {
    const data = {
      id: 'autosave',
      pdfName, annots, emmaRows, annotIdSeq,
      emmaFields: captureEmmaFields(),
      savedAt: new Date().toISOString(),
      annotCount: annots.length,
      pdfBytes: pdfBytes || undefined,
    };
    const tx = idb.transaction('sessions', 'readwrite');
    tx.objectStore('sessions').put(data);
    const dot = document.getElementById('autosave-dot');
    if (dot) { dot.classList.add('pulse'); setTimeout(() => dot.classList.remove('pulse'), 1500); }
    const sbAs = document.getElementById('sb-autosave');
    if (sbAs) sbAs.textContent = '\u2713 ' + new Date().toLocaleTimeString([], {hour:'2-digit',minute:'2-digit'});
  } catch(e) { /* quota exceeded or idb error — silent */ }
}

async function idbRestore() {
  if (!idb) return null;
  return new Promise(res => {
    try {
      const tx  = idb.transaction('sessions', 'readonly');
      const req = tx.objectStore('sessions').get('autosave');
      req.onsuccess = () => res(req.result || null);
      req.onerror   = () => res(null);
    } catch(e) { res(null); }
  });
}

async function idbClearAutosave() {
  if (!idb) return;
  try {
    const tx = idb.transaction('sessions', 'readwrite');
    tx.objectStore('sessions').delete('autosave');
  } catch(e) { /* silent */ }
}

function captureEmmaFields() {
  const ids = ['emma-proj-title','emma-proj-no','emma-doc-no','emma-rev-no',
    'emma-specific','emma-chk-no','emma-discipline','emma-checker','emma-date'];
  const out = {};
  ids.forEach(id => { const el = document.getElementById(id); if (el) out[id] = el.value; });
  return out;
}

function updateTemplateUI(filename) {
  const btn = document.querySelector('.emma-import-btn');
  if (!btn) return;
  // The static <input id="emma-template-file"> is always in the DOM — don't inject a duplicate
  if (filename) {
    const short = filename.replace(/\.xlsm$/i,'').replace(/\.xlsx$/i,'').slice(0, 24);
    btn.innerHTML =
      '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" width="12" height="12"><path d="M9 11l3 3L22 4"/></svg> ' +
      short +
      ' <span onclick="clearEmmaTemplate(event)" style="margin-left:6px;Color:#b91c1c;font-weight:700;cursor:pointer" title="Remove saved template">&times;</span>';
    btn.style.Color = '#166534';
    btn.style.borderColor = '#bbf7d0';
    btn.style.background = '#f0fdf4';
  } else {
    btn.innerHTML =
      '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" width="12" height="12"><path d="M21 15v4a2 2 0 01-2 2H5a2 2 0 01-2-2v-4"/><polyline points="17 8 12 3 7 8"/><line x1="12" y1="3" x2="12" y2="15"/></svg> ' +
      'Load Template';
    btn.style.Color = '';
    btn.style.borderColor = '';
    btn.style.background = '';
  }
}

async function clearEmmaTemplate(e) {
  e.stopPropagation();
  emmaTemplateBuf = null;
  await idbClearTemplate();
  updateTemplateUI(null);
  toast('EMMA template removed — load a new one via the EMMA panel');
}

// Auto-save every 30s and on every annotation push
let autoSaveTimer = null;
function scheduleAutoSave() {
  clearTimeout(autoSaveTimer);
  autoSaveTimer = setTimeout(() => idbSave(), 30000);
  clearTimeout(window._idbDebounce);
  window._idbDebounce = setTimeout(() => idbSave(), 2000);
}

// Initialise IDB — restore template + session on startup
openIDB().then(async () => {
  // Restore template silently first
  const tmpl = await idbLoadTemplate();
  if (tmpl && tmpl.buf) {
    emmaTemplateBuf = tmpl.buf;
    updateTemplateUI(tmpl.filename || 'Checksheet.xlsm');
    toast('✓ EMMA template ready: ' + (tmpl.filename || 'Checksheet.xlsm'), 3000);
  }
  // Check for unsaved autosave session
  const saved = await idbRestore();
  if (saved && saved.pdfName && !pdfName) {
    const ageMins = saved.savedAt
      ? Math.round((Date.now() - new Date(saved.savedAt)) / 60000)
      : null;
    const ageStr = ageMins === null ? 'unknown time'
      : ageMins < 1  ? 'less than a minute ago'
      : ageMins < 60 ? ageMins + ' minute' + (ageMins !== 1 ? 's' : '') + ' ago'
      : Math.round(ageMins / 60) + ' hour' + (Math.round(ageMins / 60) !== 1 ? 's' : '') + ' ago';

    document.getElementById('restore-title').textContent =
      'Unsaved session found: "' + saved.pdfName + '"';
    document.getElementById('restore-detail').innerHTML =
      'EngDoc has an auto-saved session from <strong>' + ageStr + '</strong> with ' +
      '<strong>' + (saved.annotCount || (saved.annots && saved.annots.length) || 0) + ' annotation' +
      ((saved.annotCount || (saved.annots && saved.annots.length) || 0) !== 1 ? 's' : '') + '</strong>.<br><br>' +
      (saved.pdfBytes
        ? 'The drawing and all annotations will be restored.'
        : 'Annotations will be restored. You will need to re-open the PDF drawing.') +
      '<br><br>Click <strong>Discard</strong> to start fresh, or <strong>Restore Session</strong> to continue where you left off.';

    // Store for use by doRestore / dismissRestore
    window._pendingRestore = saved;
    openM('mrestore');
  }
}).catch(() => {});


// ═══════════════════════════════════════════════
//  AREA / POLYGON MEASUREMENT TOOL
// ═══════════════════════════════════════════════
let areaPoints = [];  // [{x, y}] in overlay px
let areaLiveSvg = null;
let areaPageNum = null;
let areaVp = null;

function startAreaTool(ov, pageNum, vp, ox, oy) {
  if (areaPageNum !== pageNum) {
    // Cancel any in-progress area on a different page
    cancelArea();
  }
  areaPageNum = pageNum; areaVp = vp;
  areaPoints.push({ x: ox, y: oy });

  if (!areaLiveSvg) {
    areaLiveSvg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    areaLiveSvg.style.cssText = 'position:absolute;top:0;left:0;overflow:visible;pointer-events:none;z-index:10';
    areaLiveSvg.setAttribute('width', vp.width); areaLiveSvg.setAttribute('height', vp.height);
    ov.appendChild(areaLiveSvg);
  }
  updateAreaPreview(ox, oy);
  if (areaPoints.length === 1) toast('Click to add points — double-click to close & measure', 2500);
}

function updateAreaPreview(mx, my) {
  if (!areaLiveSvg || areaPoints.length === 0) return;
  areaLiveSvg.innerHTML = '';
  const c = colorHex(Color, '#7c3aed');
  const pts = [...areaPoints, { x: mx, y: my }];

  // Closed polygon fill
  if (pts.length >= 3) {
    const poly = document.createElementNS('http://www.w3.org/2000/svg', 'polygon');
    poly.setAttribute('points', pts.map(p => `${p.x},${p.y}`).join(' '));
    poly.setAttribute('fill', c + '22'); poly.setAttribute('stroke', c);
    poly.setAttribute('stroke-width', '1.5'); poly.setAttribute('stroke-dasharray', '5,3');
    areaLiveSvg.appendChild(poly);
  }
  // Point dots
  areaPoints.forEach((p, i) => {
    const dot = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
    dot.setAttribute('cx', p.x); dot.setAttribute('cy', p.y); dot.setAttribute('r', i === 0 ? 5 : 3);
    dot.setAttribute('fill', i === 0 ? c : '#fff'); dot.setAttribute('stroke', c); dot.setAttribute('stroke-width', '1.5');
    areaLiveSvg.appendChild(dot);
  });
  // Live line to cursor
  if (areaPoints.length > 0) {
    const line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
    const last = areaPoints[areaPoints.length - 1];
    line.setAttribute('x1', last.x); line.setAttribute('y1', last.y);
    line.setAttribute('x2', mx); line.setAttribute('y2', my);
    line.setAttribute('stroke', c); line.setAttribute('stroke-width', '1.5');
    line.setAttribute('stroke-dasharray', '4,3'); areaLiveSvg.appendChild(line);
  }
  // Area label
  if (pts.length >= 3) {
    const area = computePolygonArea(areaPoints);
    const areaLabel = measureScale
      ? `${(area / (measureScale.pxPerUnit * measureScale.pxPerUnit)).toFixed(2)} ${measureScale.unit}²`
      : `${Math.round(area)} px²`;
    const cx = areaPoints.reduce((s, p) => s + p.x, 0) / areaPoints.length;
    const cy = areaPoints.reduce((s, p) => s + p.y, 0) / areaPoints.length;
    const txt = document.createElementNS('http://www.w3.org/2000/svg', 'text');
    txt.setAttribute('x', cx); txt.setAttribute('y', cy);
    txt.setAttribute('fill', c); txt.setAttribute('font-size', '11');
    txt.setAttribute('font-family', 'DM Mono, monospace'); txt.setAttribute('text-anchor', 'middle');
    txt.textContent = areaLabel; areaLiveSvg.appendChild(txt);
    document.getElementById('sb-measure').textContent = '⬛ ' + areaLabel;
    document.getElementById('sb-measure').classList.add('visible');
  }
}

function computePolygonArea(pts) {
  // Shoelace formula
  let area = 0;
  for (let i = 0; i < pts.length; i++) {
    const j = (i + 1) % pts.length;
    area += pts[i].x * pts[j].y;
    area -= pts[j].x * pts[i].y;
  }
  return Math.abs(area) / 2;
}

function commitArea() {
  if (!areaPoints || areaPoints.length < 3) { cancelArea(); return; }
  if (areaLiveSvg) { areaLiveSvg.remove(); areaLiveSvg = null; }
  document.getElementById('sb-measure').classList.remove('visible');
  const vp = areaVp;
  const area = computePolygonArea(areaPoints);
  const areaLabel = measureScale
    ? `${(area / (measureScale.pxPerUnit * measureScale.pxPerUnit)).toFixed(2)} ${measureScale.unit}²`
    : `${Math.round(area)} px²`;
  const pts = areaPoints.map(p => ({ x: p.x / vp.width, y: p.y / vp.height }));
  pushAnnot({ id: nextId(), pageNum: areaPageNum, type: 'area',
    points: pts, Color, label: areaLabel, areaPx: area });
  areaPoints = []; areaPageNum = null; areaVp = null;
}

function cancelArea() {
  if (areaLiveSvg) { areaLiveSvg.remove(); areaLiveSvg = null; }
  areaPoints = []; areaPageNum = null; areaVp = null;
  document.getElementById('sb-measure').classList.remove('visible');
}

// Wire area tool into attachEvents — intercept mousedown/mousemove for area
// (done by checking tool === 'area' in the overlay event handlers already attached;
//  we extend the existing attachEvents via a separate overlay listener here)
function attachAreaEvents(ov, pageNum, vp) {
  let lastClick = 0;
  ov.addEventListener('click', e => {
    if (tool !== 'area') return;
    e.stopPropagation();
    const r = ov.getBoundingClientRect();
    // 'click' fires as its own event object (after the mousedown that set
    // e._snapX/_snapY on a different event), so re-run the snap lookup here
    // rather than relying on the generic mousedown-stash mechanism.
    const rawX = e.clientX - r.left, rawY = e.clientY - r.top;
    const snap = findSnapPoint(rawX, rawY, pageNum, vp);
    const ox = snap ? snap.sx : rawX, oy = snap ? snap.sy : rawY;
    const now = Date.now();
    if (now - lastClick < 350) {
      // Double-click — commit
      commitArea(); lastClick = 0; return;
    }
    lastClick = now;
    startAreaTool(ov, pageNum, vp, ox, oy);
  });
  ov.addEventListener('mousemove', e => {
    if (tool !== 'area' || areaPoints.length === 0) return;
    const r = ov.getBoundingClientRect();
    updateAreaPreview(e.clientX - r.left, e.clientY - r.top);
  });
}

// ═══════════════════════════════════════════════
//  AREA ANNOTATION RENDERER
// ═══════════════════════════════════════════════
function buildAreaAnnotEl(a) {
  const wrap = document.createElement('div');
  wrap.className = 'asvg-wrap';
  wrap.style.cssText = 'position:absolute;inset:0;pointer-events:none';
  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svg.style.cssText = 'position:absolute;top:0;left:0;width:100%;height:100%;overflow:visible';
  svg.setAttribute('viewBox', '0 0 100 100');
  svg.setAttribute('preserveAspectRatio', 'none');
  const c = colorHex(a.Color, '#7c3aed');
  const pts = a.points.map(p => `${p.x * 100},${p.y * 100}`).join(' ');

  // Ghost stroke for eraser
  const ghost = document.createElementNS('http://www.w3.org/2000/svg', 'polygon');
  ghost.setAttribute('points', pts); ghost.setAttribute('fill', 'none');
  ghost.setAttribute('stroke', 'transparent'); ghost.setAttribute('stroke-width', '4');
  ghost.setAttribute('vector-effect', 'non-scaling-stroke');

  // Visible polygon
  const poly = document.createElementNS('http://www.w3.org/2000/svg', 'polygon');
  poly.setAttribute('points', pts);
  poly.setAttribute('fill', c + '22'); poly.setAttribute('stroke', c);
  poly.setAttribute('stroke-width', '2'); poly.setAttribute('vector-effect', 'non-scaling-stroke');

  // Label at centroid
  const cx = a.points.reduce((s, p) => s + p.x, 0) / a.points.length * 100;
  const cy = a.points.reduce((s, p) => s + p.y, 0) / a.points.length * 100;
  const txt = document.createElementNS('http://www.w3.org/2000/svg', 'text');
  txt.setAttribute('x', cx); txt.setAttribute('y', cy);
  txt.setAttribute('fill', c); txt.setAttribute('font-size', '2.5');
  txt.setAttribute('font-family', 'DM Mono, monospace'); txt.setAttribute('text-anchor', 'middle');
  txt.setAttribute('vector-effect', 'non-scaling-stroke'); txt.textContent = a.label;

  svg.appendChild(ghost); svg.appendChild(poly); svg.appendChild(txt);
  wrap.appendChild(svg);
  return wrap;
}

// ═══════════════════════════════════════════════
//  SPACEBAR TEMPORARY PAN
// ═══════════════════════════════════════════════
let spaceToolPrev = null;
document.addEventListener('keydown', e => {
  if (e.code === 'Space' && !e.repeat && !e.target.closest('input,textarea,select')) {
    if (tool !== 'pan') { spaceToolPrev = tool; setTool('pan'); }
  }
});
document.addEventListener('keyup', e => {
  if (e.code === 'Space' && spaceToolPrev !== null) {
    setTool(spaceToolPrev); spaceToolPrev = null;
  }
});

// ═══════════════════════════════════════════════
//  NR DRAWING STANDARDS CHECKER
//  Analyses extracted text content for common NR/TRU
//  drawing issues: missing scale bar, CDM triangle,
//  title block completeness, drawing number format,
//  north point, revision history, and more.
// ═══════════════════════════════════════════════

/* Each check returns { id, group, title, desc, status, ref, page }
   status: 'pass' | 'warn' | 'fail' | 'info'
*/
let checkFindings = [];

async function runStandardsCheck() {
  if (!pdf) { toast('Open a PDF first'); return; }
  const myGen = docGen; // bail if the user switches tabs before this finishes
  openM('mcheck');
  switchCheckTab('standards');
  document.getElementById('check-running').style.display = 'block';
  document.getElementById('check-results').innerHTML = '';
  document.getElementById('check-summary').textContent = '';
  document.getElementById('check-add-btn').style.display = 'none';

  // Make sure text is extracted for at least page 1
  const bar = document.getElementById('check-progress');
  const updateBar = (pct) => { if (bar) bar.style.width = pct + '%'; };

  updateBar(10);
  // Extract pages 1 and last (title sheet + last sheet usually have key info)
  const pagesToCheck = [1];
  if (nPages > 1) pagesToCheck.push(nPages);
  if (nPages > 2) pagesToCheck.push(Math.ceil(nPages / 2)); // mid-sheet sample

  for (const pg of pagesToCheck) {
    if (!pdfTextContent[pg]) {
      try {
        const page = await pdf.getPage(pg);
        if (myGen !== docGen) return;
        const tc = await page.getTextContent();
        if (myGen !== docGen) return;
        const vp = page.getViewport({ scale: 1 });
        pdfTextContent[pg] = tc.items.filter(i => i.str?.trim()).map(i => {
          const [,,,scaleY,tx,ty] = i.transform;
          return { str: i.str.trim(), x: tx/vp.width, y: 1-(ty/vp.height),
            fontSize: Math.abs(scaleY)/vp.height, width: i.width/vp.width };
        });
      } catch(e) {}
    }
  }
  if (myGen !== docGen) return;
  updateBar(40);

  // Run all checks
  checkFindings = [];
  const page1 = pdfTextContent[1] || [];
  const allText = Object.values(pdfTextContent).flat();
  const allStr = allText.map(t => t.str).join(' ');
  const page1Str = page1.map(t => t.str).join(' ');

  checkFindings.push(...checkTitleBlock(page1, page1Str));
  updateBar(55);
  checkFindings.push(...checkDrawingNumber(page1Str));
  updateBar(65);
  checkFindings.push(...checkScaleBar(page1, page1Str));
  updateBar(73);
  checkFindings.push(...checkCDM(allStr, page1Str));
  updateBar(80);
  checkFindings.push(...checkRevisionPanel(page1, page1Str));
  updateBar(87);
  checkFindings.push(...checkNorthPoint(page1Str, allStr));
  updateBar(92);
  checkFindings.push(...checkProjectionAngle(page1Str));
  updateBar(96);
  checkFindings.push(...checkUnits(page1Str, allStr));
  updateBar(100);

  renderCheckResults(checkFindings);
  document.getElementById('check-running').style.display = 'none';

  const fails = checkFindings.filter(f => f.status === 'fail').length;
  const warns = checkFindings.filter(f => f.status === 'warn').length;
  const passes = checkFindings.filter(f => f.status === 'pass').length;
  document.getElementById('check-summary').textContent =
    `${fails} issue${fails !== 1?'s':''} · ${warns} warning${warns!==1?'s':''} · ${passes} passed`;
  const hasFails = fails > 0 || warns > 0;
  document.getElementById('check-add-btn').style.display = hasFails ? '' : 'none';
}

/* ── INDIVIDUAL CHECK FUNCTIONS ─────────────────────────── */

function checkTitleBlock(items, str) {
  const findings = [];
  const req = [
    { key: 'drawing number', pats: /drawing\s*number|drg\s*no|dwg\s*no/i, label: 'Drawing Number' },
    { key: 'revision',       pats: /^revision$|^rev\.?$/i,                 label: 'Revision' },
    { key: 'drawn by',       pats: /^drawn$|^drawn\s*by$/i,                label: 'Drawn by' },
    { key: 'checked',        pats: /^checked$|^checked\s*by$/i,            label: 'Checked by' },
    { key: 'date',           pats: /^date$/i,                              label: 'Date' },
    { key: 'title',          pats: /drawing\s*title|^title$/i,             label: 'Drawing Title' },
    { key: 'scale',          pats: /^scale$|^scales?$/i,                   label: 'Scale' },
    { key: 'project',        pats: /^project$|contract\s*no/i,            label: 'Project / Contract No.' },
    { key: 'sheet',          pats: /sheet\s*\d|sheet.*of|^\d+\s*of\s*\d+$/i, label: 'Sheet Number' },
  ];

  const missingLabels = [];
  req.forEach(({ pats, label }) => {
    const found = items.some(it => pats.test(it.str.trim()));
    if (!found) missingLabels.push(label);
  });

  if (missingLabels.length === 0) {
    findings.push({ id:'tb-complete', group:'Title Block', title:'Title block appears complete',
      desc:'All required title block fields detected.', status:'pass', ref:'NR/L2/INI/02116' });
  } else {
    findings.push({ id:'tb-missing', group:'Title Block',
      title:'Missing title block fields',
      desc:`The following fields were not detected in the title block: ${missingLabels.join(', ')}.`,
      status: missingLabels.length > 3 ? 'fail' : 'warn',
      ref:'NR/L2/INI/02116 §4.2' });
  }

  // Check authorised field
  const hasAuth = /authoris|approved/i.test(str);
  if (!hasAuth) {
    findings.push({ id:'tb-auth', group:'Title Block', title:'No Authorised / Approved field found',
      desc:'NR title blocks must include an Authorised or Approved signatory field.',
      status:'warn', ref:'NR/L2/INI/02116 §4.3' });
  }

  return findings;
}

function checkDrawingNumber(str) {
  const findings = [];
  // NR drawing number convention: typically contains hyphens and alphanumeric blocks
  // e.g. 151667-TSA-W3-TRU-DRG-R-SE-021255 or NR/PROJ/DISC/NNNNN
  const nrFormatStrict = /\d{5,}-[A-Z]{2,}-[A-Z0-9]+-[A-Z]{2,}-[A-Z]{3,}/;
  const nrFormatLoose  = /[A-Z0-9]{2,}-[A-Z0-9]{2,}-[A-Z0-9]{2,}/;

  if (nrFormatStrict.test(str)) {
    findings.push({ id:'drg-num', group:'Drawing Number', title:'Drawing number format looks correct',
      desc:'Drawing number follows expected hyphen-separated NR/TRU format.', status:'pass', ref:'NR/GN/CIV/005' });
  } else if (nrFormatLoose.test(str)) {
    findings.push({ id:'drg-num', group:'Drawing Number', title:'Drawing number format — verify',
      desc:'A document reference was found but it may not follow the full NR/TRU number convention (NNNNN-ORG-PROJ-DISC-DRG-TYPE-NNNNN).',
      status:'warn', ref:'NR/GN/CIV/005 §3' });
  } else {
    findings.push({ id:'drg-num', group:'Drawing Number', title:'Drawing number not detected',
      desc:'No recognisable drawing number format found. Check title block.',
      status:'fail', ref:'NR/GN/CIV/005' });
  }

  // Revision check — should be P01, P02, AFC, A, B… not blank
  const revMatch = str.match(/\b(P0\d|P1\d|AFC|Rev\s*[A-Z]|\bA\b|\bB\b|\bC\b|R\d+)\b/);
  if (revMatch) {
    findings.push({ id:'revision', group:'Drawing Number', title:'Revision status found',
      desc:`Revision identifier detected: ${revMatch[0]}`, status:'pass', ref:'NR/L2/INI/02116 §5' });
  } else {
    findings.push({ id:'revision', group:'Drawing Number', title:'Revision status not found or unclear',
      desc:'Could not detect a clear revision identifier (e.g. P01, P02, AFC, A, B). Verify the title block revision field.',
      status:'warn', ref:'NR/L2/INI/02116 §5' });
  }

  return findings;
}

function checkScaleBar(items, str) {
  const findings = [];

  // 1. Check stated scale in title block
  const scaleRatio = str.match(/1\s*[:\/]\s*(\d+)/);
  if (scaleRatio) {
    findings.push({ id:'scale-stated', group:'Scale', title:`Scale stated: 1:${scaleRatio[1]}`,
      desc:'Drawing scale ratio detected in title block.', status:'pass', ref:'BS 8888:2017 §13.2' });
  } else if (/NTS|not\s*to\s*scale|n\.t\.s/i.test(str)) {
    findings.push({ id:'scale-stated', group:'Scale', title:'Drawing marked as Not To Scale (NTS)',
      desc:'Drawing is explicitly marked NTS. Ensure this is intentional — NTS drawings must not be used for set-out or dimension checking.',
      status:'info', ref:'BS 8888:2017 §13.2' });
  } else {
    findings.push({ id:'scale-stated', group:'Scale', title:'No scale stated in title block',
      desc:'A scale ratio (e.g. 1:500) or NTS designation must be stated in the title block on all engineering drawings.',
      status:'fail', ref:'BS 8888:2017 §13.2 / NR/L2/INI/02116' });
  }

  // 2. Check for scale bar / graphic scale in drawing body
  // Look for patterns like "0___50m", "scale bar", "0  25  50", or a horizontal measurement bar
  const hasScaleBar = /scale\s*bar|graphic\s*scale|\b0\s+\d+\s+\d+\s*m\b|\bscale\s*1:/i.test(str)
    || items.some(it => /^\d+\s*m$|^\d+\s*mm$|^\d+\s*km$/i.test(it.str.trim()));

  if (hasScaleBar) {
    findings.push({ id:'scale-bar', group:'Scale', title:'Scale bar / graphic scale detected',
      desc:'A graphic scale or scale bar appears to be present on the drawing.',
      status:'pass', ref:'NR/GN/CIV/005' });
  } else {
    findings.push({ id:'scale-bar', group:'Scale', title:'Scale bar not detected',
      desc:'Engineering drawings should include a graphic scale bar in addition to the title block ratio. This allows dimensions to be checked even if the drawing is reproduced at a different size.',
      status:'warn', ref:'NR/GN/CIV/005 §4.1 / BS 8888:2017 §13.3' });
  }

  return findings;
}

function checkCDM(allStr, page1Str) {
  const findings = [];

  // CDM hazard / health & safety triangle
  // Look for: CDM, hazard, H&S, health and safety, residual risk, construction phase plan
  const hasCDM = /\bCDM\b|health\s*[&and]+\s*safety|hazard|residual\s*risk|construction\s*phase\s*plan|CPP\b|H&S\b/i.test(allStr);
  if (hasCDM) {
    findings.push({ id:'cdm-present', group:'CDM & Safety', title:'CDM / H&S content detected',
      desc:'Health & Safety or CDM-related text found on the drawing.',
      status:'pass', ref:'CDM Regs 2015 / NR/L3/INF/02007' });
  } else {
    findings.push({ id:'cdm-missing', group:'CDM & Safety', title:'No CDM / H&S hazard indication found',
      desc:'NR drawings must include a CDM hazard triangle or equivalent health & safety information where construction hazards are present. Check whether this drawing requires CDM annotation (e.g. confined spaces, overhead lines, buried services, contaminated land).',
      status:'warn', ref:'CDM Regs 2015 / NR/L3/INF/02007 §6' });
  }

  // OLE / electrification warning
  const hasOLE = /\bOLE\b|overhead\s*line|electrification|25kV|25\s*kV|catenary|contact\s*wire/i.test(allStr);
  if (hasOLE) {
    const hasOLEWarning = /safe\s*working|isolation|line\s*clear|permit|exclusion\s*zone|approach\s*distance/i.test(allStr);
    if (hasOLEWarning) {
      findings.push({ id:'ole-warn', group:'CDM & Safety', title:'OLE / electrification warning present',
        desc:'Overhead line equipment references and safety working notes detected.',
        status:'pass', ref:'NR/L2/OLE/00056' });
    } else {
      findings.push({ id:'ole-warn', group:'CDM & Safety', title:'OLE detected — safe working distance warning may be missing',
        desc:'Overhead line equipment (OLE) is referenced but no safe working distance or isolation notice was detected. All drawings showing OLE must include appropriate electrical safety warnings.',
        status:'fail', ref:'NR/L2/OLE/00056 §4.2' });
    }
  }

  // Buried services / utilities
  const hasBuried = /buried\s*service|underground\s*cable|utility|utilities|below\s*ground\s*service|existing\s*service/i.test(allStr);
  if (hasBuried) {
    findings.push({ id:'buried', group:'CDM & Safety', title:'Buried services referenced',
      desc:'Buried or underground services are mentioned. Confirm that a "buried services" CDM hazard note is included and that service drawings have been consulted (e.g. via LSBUD/Dial Before You Dig).',
      status:'info', ref:'CDM Regs 2015 Reg.4' });
  }

  return findings;
}

function checkRevisionPanel(items, str) {
  const findings = [];

  // Revision history / revision table
  const hasRevTable = /rev(?:ision)?\s*(?:history|table|record|log)|issue\s*(?:history|table|record)/i.test(str)
    || (str.match(/\bP0[0-9]\b/g) || []).length >= 2; // at least 2 P0x entries suggests rev table

  if (hasRevTable) {
    findings.push({ id:'rev-table', group:'Revision History', title:'Revision history panel detected',
      desc:'A revision history or issue record appears to be present.',
      status:'pass', ref:'NR/L2/INI/02116 §5.4' });
  } else {
    findings.push({ id:'rev-table', group:'Revision History', title:'Revision history not detected',
      desc:'All NR drawings must carry a revision history / issue record panel listing previous revisions, issue dates, and descriptions of changes.',
      status:'warn', ref:'NR/L2/INI/02116 §5.4' });
  }

  // Issue description / reason for issue
  const hasIssueDesc = /reason\s*for\s*issue|description\s*of\s*(?:revision|change|issue)|issued\s*for|for\s*(?:information|construction|approval|checking|tender)/i.test(str);
  if (!hasIssueDesc) {
    findings.push({ id:'rev-reason', group:'Revision History', title:'Issue purpose not stated',
      desc:'The purpose of issue (e.g. "Issued for Checking", "Issued for Construction") was not detected. This should appear in the revision panel or title block.',
      status:'warn', ref:'NR/L2/INI/02116 §5.5' });
  } else {
    findings.push({ id:'rev-reason', group:'Revision History', title:'Issue purpose stated',
      desc:'A reason for issue / issued for statement was detected.', status:'pass', ref:'NR/L2/INI/02116 §5.5' });
  }

  return findings;
}

function checkNorthPoint(page1Str, allStr) {
  const findings = [];

  // North point / orientation arrow — only relevant for plan view drawings
  const isPlanView = /plan|layout|general\s*arrangement|site\s*plan|location\s*plan|key\s*plan/i.test(page1Str);
  if (!isPlanView) {
    findings.push({ id:'north', group:'Orientation', title:'Not identified as plan view',
      desc:'Drawing does not appear to be a plan-view drawing — north point check skipped.',
      status:'info', ref:'BS 8888:2017 §13.6' });
    return findings;
  }

  const hasNorth = /north|true\s*north|grid\s*north|magnetic\s*north|\bN\b.*arrow|\bnorth\s*point\b/i.test(allStr);
  if (hasNorth) {
    findings.push({ id:'north', group:'Orientation', title:'North point / orientation indicator detected',
      desc:'A north point or orientation reference appears to be present on the plan.',
      status:'pass', ref:'BS 8888:2017 §13.6' });
  } else {
    findings.push({ id:'north', group:'Orientation', title:'North point not detected on plan view',
      desc:'Plan view drawings must include a north point or orientation indicator. Without it surveyors and site teams cannot establish orientation.',
      status:'fail', ref:'BS 8888:2017 §13.6 / NR/GN/CIV/005' });
  }

  // Grid reference / OS coordinates
  const hasGrid = /grid\s*ref|NGR\b|OS\s*ref|easting|northing|BNG\b|national\s*grid/i.test(allStr);
  if (isPlanView && !hasGrid) {
    findings.push({ id:'grid', group:'Orientation', title:'No OS grid reference detected',
      desc:'Site plan drawings should include Ordnance Survey grid references or BNG coordinates to tie the drawing to the national grid. Required for GIS / asset register integration.',
      status:'warn', ref:'NR/L2/INI/02116 §6.3' });
  } else if (hasGrid) {
    findings.push({ id:'grid', group:'Orientation', title:'Grid reference / OS coordinates present',
      desc:'OS or national grid references detected.', status:'pass', ref:'NR/L2/INI/02116 §6.3' });
  }

  return findings;
}

function checkProjectionAngle(str) {
  const findings = [];

  // Third angle projection symbol should be on engineering drawings
  const hasProjection = /third\s*angle|first\s*angle|3rd\s*angle|1st\s*angle|projection/i.test(str);
  if (hasProjection) {
    findings.push({ id:'proj', group:'Drawing Standards', title:'Projection angle stated',
      desc:'Drawing projection type (first/third angle) is indicated.', status:'pass', ref:'BS 8888:2017 §14' });
  } else {
    findings.push({ id:'proj', group:'Drawing Standards', title:'Projection angle not stated',
      desc:'Engineering drawings with multi-view projections should indicate whether first or third angle projection is used. BS 8888 requires this where multiple views are shown.',
      status:'info', ref:'BS 8888:2017 §14.3' });
  }

  // Units statement
  const hasUnitsStmt = /unless\s*otherwise|all\s*dimensions?\s*(are\s*in|in)\s*(mm|m\b|metres?)/i.test(str)
    || /dimensions?\s*in\s*(mm|metres?|m\b)/i.test(str);
  if (hasUnitsStmt) {
    findings.push({ id:'units-stmt', group:'Drawing Standards', title:'Units statement present',
      desc:'A general units statement (e.g. "All dimensions in mm unless otherwise stated") was detected.',
      status:'pass', ref:'BS 8888:2017 §10' });
  } else {
    findings.push({ id:'units-stmt', group:'Drawing Standards', title:'Units statement not found',
      desc:'A general units statement should appear on the drawing (e.g. "All dimensions in mm unless otherwise noted"). Without it, dimensions may be misinterpreted.',
      status:'warn', ref:'BS 8888:2017 §10.2' });
  }

  // Copyright / confidentiality notice
  const hasCopyright = /copyright|confidential|proprietary|all\s*rights\s*reserved|do\s*not\s*scale|©/i.test(str);
  if (!hasCopyright) {
    findings.push({ id:'copyright', group:'Drawing Standards', title:'Copyright / do-not-scale notice missing',
      desc:'"Do not scale from this drawing" and/or a copyright notice is not detected. These should appear on all issued NR drawings.',
      status:'warn', ref:'NR/L2/INI/02116 §4.6' });
  } else {
    findings.push({ id:'copyright', group:'Drawing Standards', title:'Copyright / do-not-scale notice present',
      desc:'Copyright or do-not-scale notice detected.', status:'pass', ref:'NR/L2/INI/02116 §4.6' });
  }

  return findings;
}

function checkUnits(page1Str, allStr) {
  const findings = [];

  // Mixed units warning — both mm and m used (potential confusion)
  const hasMM = /\b\d+\s*mm\b/i.test(allStr);
  const hasM  = /\b\d+(\.\d+)?\s*m\b/i.test(allStr);
  if (hasMM && hasM) {
    findings.push({ id:'mixed-units', group:'Units & Dimensions', title:'Mixed units (mm and m) detected',
      desc:'Both millimetres and metres appear in dimension annotations. Verify this is intentional and that dimensions are clearly labelled with their unit to avoid misinterpretation.',
      status:'warn', ref:'BS 8888:2017 §10 / NR/GN/CIV/005' });
  } else if (hasMM || hasM) {
    findings.push({ id:'mixed-units', group:'Units & Dimensions', title:'Consistent units detected',
      desc:`Drawing appears to use ${hasMM ? 'millimetres (mm)' : 'metres (m)'} consistently.`,
      status:'pass', ref:'BS 8888:2017 §10' });
  }

  // Check for dimension annotations that might have no units
  const bareNumbers = (allStr.match(/\b\d{3,5}\b(?!\s*(?:mm|m\b|km|cm|ft|in|kN|kPa|MPa|%))/g) || []).length;
  if (bareNumbers > 10) {
    findings.push({ id:'bare-dims', group:'Units & Dimensions', title:'Possible un-annotated dimensions',
      desc:`${bareNumbers} numeric values without clear unit suffixes detected. Verify all dimensions carry an explicit unit or are covered by the general units statement.`,
      status:'info', ref:'BS 8888:2017 §10.2' });
  }

  return findings;
}

/* ── RENDER CHECK RESULTS ────────────────────────────────── */
function renderCheckResults(findings) {
  const container = document.getElementById('check-results');
  container.innerHTML = '';

  // Group by group name
  const groups = {};
  findings.forEach(f => {
    if (!groups[f.group]) groups[f.group] = [];
    groups[f.group].push(f);
  });

  const statusIcon = { pass:'✓', warn:'!', fail:'✕', info:'i' };
  const worstStatus = (items) => {
    if (items.some(i => i.status === 'fail')) return 'fail';
    if (items.some(i => i.status === 'warn')) return 'warn';
    if (items.some(i => i.status === 'info')) return 'info';
    return 'pass';
  };

  Object.entries(groups).forEach(([groupName, items]) => {
    const ws = worstStatus(items);
    const failCount = items.filter(i => i.status === 'fail').length;
    const warnCount = items.filter(i => i.status === 'warn').length;

    const group = document.createElement('div');
    group.className = 'check-group';

    // Group header
    const head = document.createElement('div');
    head.className = 'check-group-head';
    head.innerHTML = `
      <span class="check-badge ${ws}">${failCount || warnCount || items.filter(i=>i.status==='pass').length}</span>
      <span class="check-group-title">${groupName}</span>
      <span style="font-size:10px;Color:var(--gray-400)">${items.length} check${items.length!==1?'s':''}</span>
    `;

    const itemsDiv = document.createElement('div');
    itemsDiv.className = 'check-items';

    items.forEach(f => {
      const item = document.createElement('div');
      item.className = 'check-item';
      item.innerHTML = `
        <div class="check-icon ${f.status}">${statusIcon[f.status]}</div>
        <div class="check-item-body">
          <div class="check-item-title">${f.title}</div>
          <div class="check-item-desc">${f.desc}</div>
          ${f.ref ? `<div class="check-item-ref">${f.ref}</div>` : ''}
        </div>
        ${(f.status === 'fail' || f.status === 'warn') ?
          `<button class="check-add-one" onclick="addFindingAsComment('${f.id}')">+ Add to EMMA</button>` : ''}
      `;
      itemsDiv.appendChild(item);
    });

    head.onclick = () => itemsDiv.classList.toggle('collapsed');
    group.appendChild(head);
    group.appendChild(itemsDiv);
    container.appendChild(group);
  });
}

/* ── ADD FINDINGS AS EMMA COMMENTS ───────────────────────── */
function addFindingAsComment(findingId) {
  const f = checkFindings.find(x => x.id === findingId);
  if (!f) return;
  _addFindingAnnot(f);
  toast(`Added "${f.title}" to EMMA register`);
}

function addAllCheckFindings() {
  const actionable = checkFindings.filter(f => f.status === 'fail' || f.status === 'warn');
  actionable.forEach(f => _addFindingAnnot(f));
  toast(`Added ${actionable.length} findings to EMMA register`);
  closeM('mcheck');
}

function _addFindingAnnot(f) {
  // Place at a consistent position on page 1 based on finding id hash
  const hash = [...f.id].reduce((h, c) => (h * 31 + c.charCodeAt(0)) & 0xffff, 0);
  const x = 2 + (hash % 6) * 3;
  const y = 2 + (hash % 12) * 3;
  const catMap = { fail: '1', warn: '3', info: '' };
  const a = {
    id: nextId(), pageNum: 1, type: 'text',
    x, y, text: `[Standards Check] ${f.title}: ${f.desc.slice(0, 120)}`,
    Color: f.status === 'fail' ? 'red' : f.status === 'warn' ? 'yellow' : 'green',
    author: currentAuthor || 'Standards Checker',
    timestamp: new Date().toISOString(),
    emmaExclude: false,
    textAlign: 'center', vAlign: 'center', box: true,
  };
  pushAnnot(a);
  // Pre-set EMMa row with category and reference
  emmaRows[a.id] = {
    cat: catMap[f.status] || '',
    commentType: 'Not to standard',
    accepted: '', reply: '', closedOut: 'No',
    notes: f.ref || ''
  };
  syncAnnots(); updateAnnotPanel(); updateEmmaRegister();
}

// ═══════════════════════════════════════════════
//  POINTER EVENTS (touch/stylus support)
//  Patch the viewer overlay to accept pointer events in addition to mouse
// ═══════════════════════════════════════════════
function addPointerSupport(ov) {
  // Forward pointer events to mouse event handlers via synthetic events
  ['pointerdown','pointermove','pointerup'].forEach(evtName => {
    ov.addEventListener(evtName, e => {
      if (e.pointerType === 'mouse') return; // already handled natively
      e.preventDefault();
      const mouseEvt = new MouseEvent(
        evtName === 'pointerdown' ? 'mousedown' :
        evtName === 'pointermove' ? 'mousemove' : 'mouseup',
        { bubbles: true, cancelable: true, clientX: e.clientX, clientY: e.clientY, button: 0, buttons: 1 }
      );
      e.target.dispatchEvent(mouseEvt);
    }, { passive: false });
  });
  ov.style.touchAction = 'none'; // prevent scroll while drawing
}

// ═══════════════════════════════════════════════
//  EMMA STATUS DASHBOARD
// ═══════════════════════════════════════════════
function updateEmmaDash() {
  const emmaAnnots = annots.filter(a =>
    (a.type === 'text' || a.type === 'measure') && !a.emmaExclude
  );
  const total = emmaAnnots.length;
  const closed = emmaAnnots.filter(a => emmaRows[a.id]?.closedOut === 'Yes').length;
  const open = total - closed;
  const pct = total > 0 ? Math.round(closed / total * 100) : 0;

  const el = id => document.getElementById(id);
  if (el('ds-total')) el('ds-total').textContent = total;
  if (el('ds-open'))  el('ds-open').textContent  = open;
  if (el('ds-closed'))el('ds-closed').textContent = closed;
  if (el('ds-pct'))   el('ds-pct').textContent   = total > 0 ? pct + '%' : '—';
  if (el('ds-bar'))   el('ds-bar').style.width   = pct + '%';

  // CAT breakdown badges
  const catsEl = el('ds-cats');
  if (catsEl) {
    const catCounts = { '1': 0, '2': 0, '3': 0, 'BP': 0 };
    emmaAnnots.forEach(a => {
      const cat = emmaRows[a.id]?.cat;
      if (cat && catCounts[cat] !== undefined) catCounts[cat]++;
    });
    const catStyles = {
      '1': 'background:#fee2e2;Color:#b91c1c',
      '2': 'background:#fef9c3;Color:#854d0e',
      '3': 'background:#ffedd5;Color:#c2410c',
      'BP': 'background:#dbeafe;Color:#1d4ed8'
    };
    catsEl.innerHTML = Object.entries(catCounts)
      .filter(([,v]) => v > 0)
      .map(([k, v]) => `<span class="dash-cat" style="${catStyles[k]}">${k}: ${v}</span>`)
      .join('');
  }
}

// ═══════════════════════════════════════════════
//  PATCH pushAnnot TO TRIGGER DASHBOARD + AUTOSAVE
// ═══════════════════════════════════════════════
const _origPushAnnot = pushAnnot;
// Wrap pushAnnot to also update dashboard and trigger autosave
// (pushAnnot is already defined above; we extend its behaviour here)
const pushAnnotOrig = pushAnnot;
window._pushAnnotHooked = true;

// Override at module level — extend the existing function
(function() {
  const orig = window.pushAnnot || pushAnnot;
  // Can't reassign const; patch via the call chain instead
  // Dashboard update fires from syncAnnots which is called by pushAnnot
})();

// ═══════════════════════════════════════════════
//  PATCH syncAnnots TO UPDATE DASHBOARD
// ═══════════════════════════════════════════════
// ═══════════════════════════════════════════════
//  WIRE AREA EVENTS + POINTER SUPPORT INTO PAGE RENDER
// ═══════════════════════════════════════════════
// Extend renderPageContent to attach area+pointer support after overlay is created
const _origRenderPageContent = renderPageContent;
renderPageContent = async function(pageNum) {
  await _origRenderPageContent(pageNum);
  // Find the overlay and attach area events + pointer support
  const ov = document.querySelector(`.aoverlay[data-page="${pageNum}"]`);
  if (ov && !ov._areaAttached) {
    ov._areaAttached = true;
    const pvp = pageViewports[pageNum];
    if (pvp) {
      attachAreaEvents(ov, pageNum, { width: pvp.width, height: pvp.height });
      addPointerSupport(ov);
    }
  }
  updateEmmaDash();
};

// ═══════════════════════════════════════════════
//  PATCH typeLabels + setTool + buildAnnotEl for area
// ═══════════════════════════════════════════════
typeLabels['area'] = 'Area Measurement';

// area cancelArea now handled in _ribbonSetTool patch below

// area type handled in core buildAnnotEl via buildAreaAnnotEl

// ═══════════════════════════════════════════════
//  PATCH pushAnnot to trigger autosave + dashboard
// ═══════════════════════════════════════════════
// Single pushAnnot post-hook — dashboard, autosave, measurement table
const _origPushAnnotFinal = pushAnnot;
pushAnnot = function(a) {
  _origPushAnnotFinal(a);
  updateEmmaDash();
  scheduleAutoSave();
  if (a.type === 'measure' || a.type === 'area') updateMeasurementTable();
};

// deleteAnnotById post-hook
const _deleteAnnotBase = deleteAnnotById;
deleteAnnotById = function(id) {
  _deleteAnnotBase(id);
  updateEmmaDash();
  scheduleAutoSave();
};

// saveEmmaRow post-hook
const _saveEmmaRowBase = saveEmmaRow;
saveEmmaRow = function() {
  _saveEmmaRowBase();
  updateEmmaDash();
  scheduleAutoSave();
};

// ═══════════════════════════════════════════════
//  INIT
// ═══════════════════════════════════════════════
initAuthor();
// Restore saved scale
try {
  const saved = localStorage.getItem('engdoc_scale');
  if (saved) {
    measureScale = JSON.parse(saved);
    document.getElementById('sb-scale').textContent = `⚖ Scale: 1:set`;
  }
} catch(e) {}
// Ctrl+S save
document.addEventListener('keydown', e => {
  if ((e.ctrlKey || e.metaKey) && e.key === 's') { e.preventDefault(); saveSessionWithPdf(); }
});

// ═══════════════════════════════════════════════
//  AUTHOR Color-CODING (multi-user sessions)
// ═══════════════════════════════════════════════
const AUTHOR_PALETTE = ['#2563eb','#16a34a','#dc2626','#d97706','#7c3aed','#0891b2','#be185d','#65a30d'];
const authorColors = {}; // name → hex Color
let authorColorIdx = 0;

function getAuthorColor(name) {
  if (!name) return '#6b7280';
  if (!authorColors[name]) {
    authorColors[name] = AUTHOR_PALETTE[authorColorIdx % AUTHOR_PALETTE.length];
    authorColorIdx++;
  }
  return authorColors[name];
}

// ═══════════════════════════════════════════════
//  MERGE SESSION (multi-user)
// ═══════════════════════════════════════════════
async function mergeSession(e) {
  const file = e.target.files[0]; if (!file) return;
  e.target.value = '';
  try {
    const text = await file.text();
    const data = JSON.parse(text);
    if (!data.annots) { toast('Invalid .engdoc file'); return; }

    let added = 0, skipped = 0;
    const existingIds = new Set(annots.map(a => a.id));

    data.annots.forEach(a => {
      // Skip if exact same id already exists (own session)
      if (existingIds.has(a.id)) { skipped++; return; }
      // Assign a new local id to avoid conflicts
      const newId = nextId();
      const merged = migrateLegacyTextboxCalloutAnnot(migrateLegacyNoteAnnot({ ...a, id: newId, mergedFrom: a.author || 'Unknown' }));
      annots.push(merged);
      // Carry EMMA row data if present
      if (data.emmaRows && data.emmaRows[a.id]) {
        emmaRows[newId] = { ...data.emmaRows[a.id] };
      }
      added++;
    });

    // Record all new authors for Color palette
    data.annots.forEach(a => { if (a.author) getAuthorColor(a.author); });

    syncAnnots(); updateAnnotPanel(); updateStatusCount(); updateEmmaRegister(); updateEmmaDash();
    toast(`✓ Merged ${added} annotation${added !== 1 ? 's' : ''} from "${data.pdfName || file.name}"${skipped ? ` (${skipped} duplicates skipped)` : ''}`);
  } catch(err) {
    toast('Merge failed: ' + err.message);
  }
}

// Author Color stripe for merged annotations handled in core buildAnnotEl

// ═══════════════════════════════════════════════
//  REVISION COMPARISON
// ═══════════════════════════════════════════════
let comparePdfBytes = null;
let comparisonActive = false;

function onCompareFileSelect(e) {
  const file = e.target.files[0]; if (!file) return;
  file.arrayBuffer().then(buf => {
    comparePdfBytes = buf;
    document.getElementById('compare-filename').textContent = file.name;
  });
}

async function runComparison() {
  if (!pdf) { toast('Open a base PDF first'); return; }
  if (!comparePdfBytes) { toast('Select a comparison PDF'); return; }

  const pageNum = parseInt(document.getElementById('compare-page').value) || 1;
  const thresh  = parseInt(document.getElementById('compare-thresh').value) || 30;

  toast('Comparing revisions…', 4000);
  closeM('mcompare');

  try {
    // Load comparison PDF
    const compPdf = await pdfjsLib.getDocument({ data: comparePdfBytes.slice(0) }).promise;
    const compPage = await compPdf.getPage(Math.min(pageNum, compPdf.numPages));
    const basePage = await pdf.getPage(Math.min(pageNum, nPages));

    // Render both pages to offscreen canvases at a fixed scale for comparison
    const COMP_SCALE = 1.0;
    const baseVp = basePage.getViewport({ scale: COMP_SCALE });
    const compVp = compPage.getViewport({ scale: COMP_SCALE });

    const baseCanvas = document.createElement('canvas');
    baseCanvas.width = baseVp.width; baseCanvas.height = baseVp.height;
    await basePage.render({ canvasContext: baseCanvas.getContext('2d'), viewport: baseVp }).promise;

    const compCanvas = document.createElement('canvas');
    compCanvas.width = compVp.width; compCanvas.height = compVp.height;
    await compPage.render({ canvasContext: compCanvas.getContext('2d'), viewport: compVp }).promise;

    // Pixel diff
    const w = Math.min(baseVp.width, compVp.width);
    const h = Math.min(baseVp.height, compVp.height);
    const baseData = baseCanvas.getContext('2d').getImageData(0, 0, w, h).data;
    const compData = compCanvas.getContext('2d').getImageData(0, 0, w, h).data;

    // Build diff canvas
    const diffCanvas = document.createElement('canvas');
    diffCanvas.width = w; diffCanvas.height = h;
    const diffCtx = diffCanvas.getContext('2d');
    const diffImage = diffCtx.createImageData(w, h);
    const diffPx = diffImage.data;

    let changedPixels = 0;
    for (let i = 0; i < w * h * 4; i += 4) {
      const dr = Math.abs(baseData[i]   - compData[i]);
      const dg = Math.abs(baseData[i+1] - compData[i+1]);
      const db = Math.abs(baseData[i+2] - compData[i+2]);
      const diff = (dr + dg + db) / 3;
      if (diff > thresh) {
        diffPx[i]   = 220;  // R
        diffPx[i+1] = 38;   // G
        diffPx[i+2] = 38;   // B
        diffPx[i+3] = Math.min(255, Math.round(diff * 2)); // alpha proportional to diff
        changedPixels++;
      }
    }
    diffCtx.putImageData(diffImage, 0, 0);

    // Place diff overlay on the page wrapper
    const wrap = document.getElementById(`pw-${pageNum}`);
    if (!wrap) { toast('Page not rendered yet — scroll to it first'); return; }

    clearComparison();

    const overlay = document.createElement('canvas');
    overlay.id = 'compare-overlay';
    overlay.width = w; overlay.height = h;
    overlay.style.cssText = `position:absolute;top:0;left:0;width:100%;height:100%;pointer-events:none;z-index:15;border-radius:2px;opacity:0.7`;
    overlay.getContext('2d').drawImage(diffCanvas, 0, 0);
    wrap.appendChild(overlay);
    comparisonActive = true;

    const pct = ((changedPixels / (w * h)) * 100).toFixed(1);
    toast(`✓ Comparison complete — ${pct}% of page changed (red = differences)`, 5000);
  } catch(err) {
    toast('Comparison failed: ' + err.message);
  }
}

function clearComparison() {
  document.querySelectorAll('#compare-overlay').forEach(el => el.remove());
  comparisonActive = false;
}

// ═══════════════════════════════════════════════
//  DRAWING SET REGISTER
// ═══════════════════════════════════════════════
let drawingSet = []; // [{name, bytes, pages, status, annotCount}]

async function addToDrawingSet(e) {
  const files = Array.from(e.target.files); if (!files.length) return;
  e.target.value = '';
  for (const file of files) {
    // Avoid duplicates
    if (drawingSet.find(d => d.name === file.name)) continue;
    const bytes = await file.arrayBuffer();
    let pages = '?';
    try {
      const tmpPdf = await pdfjsLib.getDocument({ data: bytes.slice(0) }).promise;
      pages = tmpPdf.numPages;
    } catch(e) {}
    drawingSet.push({
      name: file.name,
      bytes,
      pages,
      status: 'outstanding',
      annotCount: 0
    });
  }
  renderDrawingSet();
  toast(`Added ${files.length} drawing${files.length !== 1 ? 's' : ''} to set`);
}

function clearDrawingSet() {
  drawingSet = [];
  renderDrawingSet();
}

function renderDrawingSet() {
  const list = document.getElementById('set-list');
  const empty = document.getElementById('set-empty');
  const count = document.getElementById('set-count');
  list.querySelectorAll('.set-item').forEach(el => el.remove());
  count.textContent = `${drawingSet.length} drawing${drawingSet.length !== 1 ? 's' : ''}`;

  if (!drawingSet.length) { empty.style.display = 'block'; return; }
  empty.style.display = 'none';

  const statusLabels = { outstanding:'Outstanding', inprogress:'In Progress', complete:'Complete' };
  const statusClasses = { outstanding:'set-status-outstanding', inprogress:'set-status-inprogress', complete:'set-status-complete' };

  drawingSet.forEach((d, i) => {
    const item = document.createElement('div');
    item.className = 'set-item' + (pdfName === d.name ? ' active' : '');
    item.innerHTML = `
      <div class="set-item-name" title="${d.name}">${d.name.replace('.pdf','')}</div>
      <span class="set-item-pages">${d.pages}p</span>
      <select class="set-item-status ${statusClasses[d.status]}" data-idx="${i}"
        onclick="event.stopPropagation()" onchange="setDrawingStatus(${i}, this.value)"
        style="font-size:10px;font-family:var(--mono);border:none;border-radius:10px;padding:2px 6px;cursor:pointer">
        ${Object.entries(statusLabels).map(([v,l]) =>
          `<option value="${v}" ${d.status===v?'selected':''}>${l}</option>`).join('')}
      </select>
      <button onclick="loadDrawingFromSet(${i})" style="padding:3px 8px;font-size:11px;background:none;border:1px solid var(--gray-300);border-radius:3px;cursor:pointer;Color:var(--gray-600)" title="Open this drawing">Open</button>`;
    list.insertBefore(item, empty);
  });
}

function setDrawingStatus(idx, status) {
  if (drawingSet[idx]) {
    drawingSet[idx].status = status;
    renderDrawingSet();
  }
}

async function loadDrawingFromSet(idx) {
  const d = drawingSet[idx]; if (!d) return;
  const file = new File([d.bytes], d.name, { type: 'application/pdf' });
  closeM('mset');
  await loadPDF(file);
  // Mark in-progress automatically
  if (d.status === 'outstanding') { d.status = 'inprogress'; renderDrawingSet(); }
}

// ═══════════════════════════════════════════════
//  DISCIPLINE COMMENT TEMPLATES
// ═══════════════════════════════════════════════
const TEMPLATES = {
  general: [
    'Detail requires clarification — please revise and reissue.',
    'Dimension/specification inconsistency — verify against design intent.',
    'Cross-reference missing — add reference to relevant document.',
    'General arrangement does not match detail drawing — coordinate.',
    'Title block incomplete — ensure all mandatory fields are populated.',
    'Drawing not to NR standard format — revise before issue.',
    'Notes are ambiguous — clarify intent with specific requirement.',
    'No revision cloud shown for changes — add in accordance with procedure.',
  ],
  civils: [
    'Reinforcement layout not compliant with BS 8666 — revise bar schedule.',
    'Foundation bearing pressure not stated — confirm against ground investigation report.',
    'No construction joint positions shown — add to drawing.',
    'Waterproofing detail not shown at basement/retaining wall junction.',
    'Structural element dimensions insufficient — add clear overall and setting-out dims.',
    'Movement joint spacing exceeds recommended maximum — review.',
    'Fencing/barrier shown does not meet NR lineside specification.',
    'Drainage falls not indicated — add gradient notation.',
    'Cover to reinforcement not stated — confirm adequacy for exposure class.',
    'No reference to geotechnical/ground investigation report — add note.',
  ],
  track: [
    'Track geometry not shown — add cant, gradient, and curvature data.',
    'Buffer stop specification not detailed — confirm type and energy absorption.',
    'Crossing angle/geometry not stated — confirm against permanent way standard.',
    'No sleeper spacing indicated — confirm to RT/CE/S/049.',
    'Rail section not specified — confirm type and weight per metre.',
    'Clearance envelope not shown — confirm compliance with NR/L2/TRK/3200.',
    'Switch and crossing details incomplete — reference TDS/D/SW/number.',
    'Level crossing surface specification missing — confirm type to NR/L3/TRK/2049.',
  ],
  signalling: [
    'Signal sighting distance not shown — check against Rule Book requirements.',
    'Cable route not indicated — confirm to functional design spec.',
    'Equipment room layout conflicts with proposed civil arrangement.',
    'Location case position not dimensioned from track centreline.',
    'Bonding and earthing arrangement not shown — add to drawing.',
    'No reference to EMC/interference assessment — confirm compliance.',
    'Signal aspect sequence not detailed — add to functional specification.',
    'Power supply arrangement for location cases not shown.',
  ],
  ole: [
    'OLE stagger/height not dimensioned at this location.',
    'Safe working distance from OLE not indicated — add exclusion zone note.',
    'Isolation section boundary not shown — confirm with OLE designer.',
    'Mast/support positions conflict with civil arrangement — coordinate.',
    'Uplift force at registration arm not calculated — check against wire tension.',
    'Earth continuity conductor not shown — add to drawing.',
    'Sectioning arrangement at neutral section not detailed.',
    'Wire height at structure gauge check point not confirmed.',
  ],
  drainage: [
    'Invert levels not shown — add to all drainage runs.',
    'Pipe gradient insufficient for self-cleansing velocity — review to Sewers for Adoption.',
    'Manhole/inspection chamber specification not stated.',
    'No outfall details shown — add discharge point and consent reference.',
    'Catchment area calculation not referenced — attach or cross-reference.',
    'Attenuation volume not confirmed against drainage strategy.',
    'Pipe bedding class not specified — confirm to BS EN 1610.',
    'Connection to existing sewer not shown in context.',
  ],
  cdm: [
    'CDM hazard triangle not shown — add for this construction activity.',
    'Residual risk not documented on drawing — add H&S note.',
    'Confined space present — add permit to enter note and reference CPP.',
    'Overhead live OLE within working area — add exclusion zone and isolation procedure reference.',
    'Buried services present — note requirement to consult LSBUD / Dial Before You Dig.',
    'Contaminated land indicated — add reference to Phase II ESA and remediation strategy.',
    'Temporary works requirement not identified — flag for Temporary Works Engineer.',
    'Working at height — add reference to work at height risk assessment.',
  ],
};

function showTemplates() {
  const picker = document.getElementById('template-picker');
  picker.style.display = picker.style.display === 'none' ? 'block' : 'none';
  if (picker.style.display === 'block') renderTemplates();
}

function renderTemplates() {
  const disc = document.getElementById('tpl-disc').value;
  const list = document.getElementById('tpl-list');
  const items = TEMPLATES[disc] || TEMPLATES.general;
  list.innerHTML = items.map(t =>
    `<div class="tpl-item" onclick="insertTemplate(${JSON.stringify(t)})">${t}</div>`
  ).join('');
}

function insertTemplate(text) {
  const input = document.getElementById('txt-pop-input');
  if (input) {
    input.value = text;
    input.focus();
    input.select();
  }
  document.getElementById('template-picker').style.display = 'none';
}

// ═══════════════════════════════════════════════
//  SNAP TO EXISTING ANNOTATION / DRAWING GEOMETRY
//  CAD-style object snap (OSNAP). When placing arrow/note/text/measure/line/
//  area points, snap cursor to the *nearest* active candidate among:
//   - annot        another annotation's anchor point
//   - endpoint     a vertex actually drawn in the PDF (line/rect corners)
//   - midpoint     the midpoint of a drawn line
//   - center       the center of a drawn circle/arc
//   - intersection where two drawn lines cross
//   - edge         the nearest point on a drawn line (perpendicular projection)
//  Toggled per-type + radius via the Snap panel (#snap-panel); persisted to
//  localStorage. See beginVectorGeomRecording()/_pageVectorGeom for how the
//  drawing geometry itself is extracted.
// ═══════════════════════════════════════════════
let snapSettings = { annot: true, endpoint: true, midpoint: true, center: true, intersection: true, edge: true, radius: 12 };
(function loadSnapSettings() {
  try {
    const saved = JSON.parse(localStorage.getItem('engdoc_snap_settings') || 'null');
    if (saved) snapSettings = { ...snapSettings, ...saved };
  } catch (e) { /* ignore corrupt saved settings */ }
})();
function saveSnapSettings() {
  localStorage.setItem('engdoc_snap_settings', JSON.stringify(snapSettings));
}

function getAnnotAnchors(pageNum, vp) {
  // Returns [{screenX, screenY, annotId}] for all annotations on this page
  return annots
    .filter(a => a.pageNum === pageNum)
    .flatMap(a => {
      const ax = []; // anchor points in overlay px
      if (a.x !== undefined && a.y !== undefined) {
        ax.push({ sx: a.x / 100 * vp.width, sy: a.y / 100 * vp.height, id: a.id });
      }
      if (a.x2 !== undefined) {
        ax.push({ sx: a.x2 / 100 * vp.width, sy: a.y2 / 100 * vp.height, id: a.id });
      }
      if (a.x1 !== undefined) {
        ax.push({ sx: a.x1 / 100 * vp.width, sy: a.y1 / 100 * vp.height, id: a.id });
      }
      return ax;
    });
}

function findSnapPoint(mx, my, pageNum, vp) {
  let best = null, bestDist = snapSettings.radius, bestType = null;
  const consider = (p, type) => {
    if (!p) return;
    const d = Math.hypot(mx - p.x, my - p.y);
    if (d < bestDist) { bestDist = d; best = { sx: p.x, sy: p.y }; bestType = type; }
  };

  if (snapSettings.annot) {
    getAnnotAnchors(pageNum, vp).forEach(a => consider({ x: a.sx, y: a.sy }, 'annot'));
  }

  const geom = _pageVectorGeom[pageNum];
  if (geom) {
    // Order doesn't set priority — each consider() only overrides on a
    // strictly closer hit, so the overall nearest active type always wins,
    // same as CAD's "closest osnap" behaviour.
    if (snapSettings.endpoint)     consider(findNearestInLayer(geom, 'points', 'pt', mx, my, bestDist), 'endpoint');
    if (snapSettings.midpoint)     consider(findNearestInLayer(geom, 'midpoints', 'mid', mx, my, bestDist), 'midpoint');
    if (snapSettings.center)       consider(findNearestInLayer(geom, 'centers', 'ctr', mx, my, bestDist), 'center');
    if (snapSettings.intersection) consider(findNearestVectorIntersection(geom, mx, my, bestDist), 'intersection');
    if (snapSettings.edge)         consider(findNearestVectorEdgePoint(geom, mx, my, bestDist), 'edge');
  }

  return best ? { ...best, type: bestType } : null; // null if nothing within snap radius
}

// Marker shapes mirror common CAD osnap conventions so the type is readable
// at a glance, not just by color: square=endpoint, triangle=midpoint,
// circle=center, X=intersection, diamond=edge/nearest, dot=annotation anchor.
function updateSnapMarker(screenX, screenY, visible, type) {
  const marker = document.getElementById('snap-marker');
  if (!marker) return;
  if (!visible) { marker.style.display = 'none'; return; }
  marker.style.display = 'block';
  marker.style.left = screenX + 'px';
  marker.style.top = screenY + 'px';
  marker.querySelectorAll('[data-snaptype]').forEach(el => {
    el.style.display = el.dataset.snaptype === type ? '' : 'none';
  });
}

// Patch attachEvents to add snap behaviour on arrow/note mousemove and mousedown
const _origAttachEvents = attachEvents;
attachEvents = function(ov, pageNum, vp) {
  _origAttachEvents(ov, pageNum, vp);

  // Snap marker: skip entirely during pan (zero work during drag)
  ov.addEventListener('mousemove', e => {
    if (tool === 'pan') return;
    if (!['arrow', 'text', 'measure', 'line', 'area'].includes(tool)) {
      updateSnapMarker(0, 0, false); return;
    }
    const r = ov.getBoundingClientRect();
    const mx = e.clientX - r.left, my = e.clientY - r.top;
    const snap = findSnapPoint(mx, my, pageNum, vp);
    if (snap) {
      updateSnapMarker(e.clientX, e.clientY, true, snap.type);
    } else {
      updateSnapMarker(0, 0, false);
    }
  });

  ov.addEventListener('mouseleave', () => updateSnapMarker(0, 0, false));
};

// Patch mousedown in attachEvents to snap coordinates
// We intercept by hooking the overlay's existing mousedown before it fires
// via a capturing listener added here
document.addEventListener('mousedown', e => {
  if (!['arrow', 'text', 'measure', 'line'].includes(tool)) return;
  const ov = e.target.closest('.aoverlay');
  if (!ov) return;
  const pageNum = parseInt(ov.dataset.page);
  const vp = pageViewports[pageNum];
  if (!vp) return;
  const r = ov.getBoundingClientRect();
  const mx = e.clientX - r.left, my = e.clientY - r.top;
  const snap = findSnapPoint(mx, my, pageNum, vp);
  if (snap) {
    // Tool mousedown handlers read e.clientX/e.clientY (or ox/oy derived from
    // them) — clientX/Y itself is read-only, so we signal the snapped coord
    // via these extra properties and each handler applies them explicitly.
    e._snapX = snap.sx + r.left;
    e._snapY = snap.sy + r.top;
    updateSnapMarker(0, 0, false);
  }
}, true); // capturing — fires before the overlay's mousedown

// ── Snap settings panel (OSNAP-style toggle popover) ──
function toggleSnapPanel(e) {
  e.stopPropagation();
  const panel = document.getElementById('snap-panel');
  if (!panel) return;
  if (panel.style.display === 'block') { panel.style.display = 'none'; return; }
  Object.keys(snapSettings).forEach(k => {
    const el = document.getElementById('snap-opt-' + k);
    if (!el) return;
    if (el.type === 'checkbox') el.checked = !!snapSettings[k];
    else el.value = snapSettings[k];
  });
  const radiusLabel = document.getElementById('snap-radius-val');
  if (radiusLabel) radiusLabel.textContent = snapSettings.radius + 'px';
  const btn = document.getElementById('sb-snap');
  const r = btn.getBoundingClientRect();
  panel.style.left = Math.round(r.left) + 'px';
  panel.style.bottom = (window.innerHeight - r.top + 6) + 'px';
  panel.style.display = 'block';
}
function updateSnapSettings() {
  ['annot', 'endpoint', 'midpoint', 'center', 'intersection', 'edge'].forEach(k => {
    const el = document.getElementById('snap-opt-' + k);
    if (el) snapSettings[k] = el.checked;
  });
  const radiusEl = document.getElementById('snap-opt-radius');
  if (radiusEl) {
    snapSettings.radius = parseInt(radiusEl.value, 10);
    const radiusLabel = document.getElementById('snap-radius-val');
    if (radiusLabel) radiusLabel.textContent = snapSettings.radius + 'px';
  }
  saveSnapSettings();
}
document.addEventListener('mousedown', e => {
  const panel = document.getElementById('snap-panel');
  if (!panel || panel.style.display !== 'block') return;
  if (e.target.closest('#snap-panel') || e.target.closest('#sb-snap')) return;
  panel.style.display = 'none';
});

// ═══════════════════════════════════════════════
//  ZOOM-AWARE MEASUREMENT LABEL RECALCULATION
//  After zoom changes, update all measure annotation
//  labels based on stored pxDist and current zoom
// ═══════════════════════════════════════════════


function recalcMeasureLabels() {
  // Update data labels and patch SVG text nodes directly — do NOT call syncAnnots()
  // (syncAnnots rebuilds all annotation DOM which destroys zoom performance)
  annots.forEach(a => {
    if (a.type !== 'measure' && a.type !== 'area') return;
    let label = null;
    if (a.type === 'measure' && a.pxDist) {
      label = measureScale
        ? (a.pxDist / measureScale.pxPerUnit / zoom).toFixed(2) + ' ' + measureScale.unit
        : Math.round(a.pxDist) + ' px';
      a.label = label;
    }
    if (a.type === 'area' && a.areaPx) {
      label = measureScale
        ? (a.areaPx / (measureScale.pxPerUnit * measureScale.pxPerUnit)).toFixed(2) + ' ' + measureScale.unit + '\u00b2'
        : Math.round(a.areaPx) + ' px\u00b2';
      a.label = label;
    }
    // Patch the existing SVG text node in-place — far cheaper than a DOM rebuild
    if (label) {
      const el = document.querySelector('[data-aid="' + a.id + '"]');
      if (el) {
        const txt = el.querySelector('text');
        if (txt) txt.textContent = label;
      }
    }
  });
}

// ═══════════════════════════════════════════════
//  WEB WORKER TEXT EXTRACTION
//  Moves PDF.js getTextContent off the main thread
//  using an inline Worker blob so there's no
//  separate .js file required
// ═══════════════════════════════════════════════
const WORKER_SRC = `
// Applies a pdf.js viewport transform matrix [a,b,c,d,e,f] to a point.
// Needed instead of a plain width/height divide because the viewport
// transform already bakes in the page's rotation (page.rotate 90/180/270,
// common on landscape engineering sheets stored as rotated portrait) —
// dividing raw PDF-space tx/ty by the rotated viewport's width/height
// silently scrambles x/y for every item on a rotated page.
function applyTransform(x, y, m) {
  return [m[0]*x + m[2]*y + m[4], m[1]*x + m[3]*y + m[5]];
}
self.onmessage = async function(e) {
  const { pageData, pageNum, width, height, vpTransform } = e.data;
  // We receive pre-extracted text items from the main thread
  // (pdf.js can't run in a worker without its own worker setup)
  // Instead we do the coordinate normalisation here
  const items = pageData.map(item => {
    const [a,b,c,d,tx,ty] = item.transform;
    const start = applyTransform(tx, ty, vpTransform);
    // item.width is already an absolute page-space displacement — (a,b) is
    // only the *direction* of travel (already scaled to ~fontSize), so it
    // must be normalised to a unit vector before stepping by width, or the
    // end point overshoots by roughly another factor of fontSize.
    const mag = Math.hypot(a, b) || 1;
    const end = applyTransform(tx + (a/mag)*item.width, ty + (b/mag)*item.width, vpTransform);
    return {
      str: item.str.trim(),
      x: start[0] / width,
      y: start[1] / height,
      fontSize: Math.hypot(c, d) / height,
      width: Math.hypot(end[0]-start[0], end[1]-start[1]) / width,
    };
  }).filter(it => it.str.length > 0);
  self.postMessage({ pageNum, items });
};
`;

let textWorker = null;
function getTextWorker() {
  if (!textWorker) {
    const blob = new Blob([WORKER_SRC], { type: 'application/javascript' });
    textWorker = new Worker(URL.createObjectURL(blob));
  }
  return textWorker;
}

// Override extractPdfText to use the worker for coordinate normalisation
async function extractPdfText() {
  const myGen = docGen; // if the user switches tabs mid-extraction, stale results below must not land
  const worker = getTextWorker();
  const promises = [];

  for (let i = 1; i <= nPages; i++) {
    promises.push((async (pg) => {
      try {
        const page = await pdf.getPage(pg);
        if (myGen !== docGen) return;
        const tc   = await page.getTextContent();
        if (myGen !== docGen) return;
        const vp   = page.getViewport({ scale: 1 });

        return new Promise(res => {
          const handler = e => {
            if (e.data.pageNum === pg) {
              worker.removeEventListener('message', handler);
              if (myGen === docGen) pdfTextContent[pg] = e.data.items;
              res();
            }
          };
          worker.addEventListener('message', handler);
          worker.postMessage({
            pageNum: pg,
            pageData: tc.items.filter(it => it.str?.trim()),
            width: vp.width,
            height: vp.height,
            vpTransform: vp.transform
          });
        });
      } catch(e) { /* skip page */ }
    })(i));
  }
  // Process in batches of 4 to avoid overwhelming the worker
  for (let i = 0; i < promises.length; i += 4) {
    if (myGen !== docGen) return;
    await Promise.all(promises.slice(i, i + 4));
  }
}

// ═══════════════════════════════════════════════
//  RIBBON CONTROLLER
// ═══════════════════════════════════════════════

const TOOL_HINTS = {
  pan:          'Click and drag to scroll · drag any annotation to move it · Space to temporarily pan',
  select:       'Drag to select text · Ctrl+C to copy · Ctrl+A to select all text on this page · Esc or V to return to Pan',
  erase:        'Click any annotation to delete it · works on all annotation types',
  highlight:    'Drag to highlight a region · Color set in Style group',
  texthighlight:'Swipe across text like a physical highlighter pen',
  rect:         'Drag to draw a rectangle markup box',
  circle:       'Drag to draw a circle or ellipse · hold Shift to constrain to perfect circle',
  rectfill:     'Drag to draw a solid filled rectangle — blocks out content or marks areas',
  strike:       'Drag to add a strikethrough over text or a region',
  cloud:        'Drag to draw a revision cloud bubble — standard NR markup convention',
  line:         'Drag to draw a straight line · Shift = constrain to horizontal / vertical / 45°',
  text:         'Click to place a text label · click label to edit · drag a + on its edge to add a leader arrow',
  pen:          'Click and drag to draw freehand · release to commit',
  arrow:        'Drag to draw an arrow with arrowhead · snap to annotations nearby',
  measure:      'Click 1 → set start · Click 2 → set end · Click 3 → commit · Shift = orthogonal snap',
  area:         'Click to add polygon points · double-click to close and calculate area',
  zoombox:      'Drag a rectangle to zoom into that region · Esc or V to return to pan · Ctrl+Wheel to zoom anywhere',
};

const TOOL_TABS = {
  pan:'markup', select:'markup', erase:'markup', zoombox:'markup',
  highlight:'markup', texthighlight:'markup', rect:'markup', rectfill:'markup', circle:'markup',
  strike:'markup', line:'markup', text:'markup',
  pen:'markup', arrow:'markup', cloud:'markup',
  measure:'markup', area:'markup',
};

function switchRibbon(tab, btn) {
  document.querySelectorAll('.rtab').forEach(b => b.classList.remove('active'));
  document.querySelectorAll('.rpanel').forEach(p => p.classList.remove('active'));
  if (btn) btn.classList.add('active');
  const panel = document.getElementById(`rpanel-${tab}`);
  if (panel) panel.classList.add('active');
  // If no btn passed, also activate the tab button
  if (!btn) {
    const tabBtn = document.getElementById(`rtab-${tab}`);
    if (tabBtn) tabBtn.classList.add('active');
  }
}

let _strokeW = 4;
function strokeW() { return _strokeW; }
function setStrokeW(val) {
  const a = _spTarget();
  if (a) { a.sw = val; syncAnnots(); return; }
  _strokeW = val;
  // Keep hidden select in sync
  const sel = document.getElementById('stroke-w');
  if (sel) sel.value = val;
}

// Patch setTool to update ribbon active states and hint strip
const _ribbonSetTool = setTool;
setTool = function(t) {
  // Clear text selection when leaving select tool
  if (tool === 'select' && t !== 'select') clearTextSelection();

  _ribbonSetTool(t);

  // Update ribbon button active states — clear all, set new
  document.querySelectorAll('.rbtn').forEach(b => {
    b.classList.remove('active', 'eraser-active');
  });
  const btn = document.getElementById('t-' + t);
  if (btn) btn.classList.add('active');

  // Restore eraser passive style when not erasing
  const erBtn = document.getElementById('t-erase');
  if (erBtn && t !== 'erase') erBtn.classList.add('eraser-active');

  // Update status bar tool hint
  const sbHint = document.getElementById('sb-hint');
  if (sbHint) sbHint.textContent = TOOL_HINTS[t] || '';

  // Auto-switch ribbon tab to match tool
  const targetTab = TOOL_TABS[t];
  if (targetTab) {
    const tabBtn = document.getElementById('rtab-' + targetTab);
    if (tabBtn) switchRibbon(targetTab, tabBtn);
  }

  // Cancel area tool if switching away
  if (t !== 'area' && areaPoints.length > 0) cancelArea();

  // Refresh move handles (debounced — cheap)
  setTimeout(refreshAnnotMoveHandles, 50);

  // Sync mobile zoom label
  const mobLabel = document.getElementById('mob-zoom-label');
  if (mobLabel) mobLabel.textContent = Math.round(zoom * 100) + '%';
};

// Number key Color shortcuts (1=yellow, 2=green, 3=red, 4=blue, 5=black)
document.addEventListener('keydown', e => {
  if (e.target.closest('input,textarea,select')) return;
  if (e.key === '1') setColor('yellow');
  if (e.key === '2') setColor('green');
  if (e.key === '3') setColor('red');
  if (e.key === '4') setColor('blue');
  if (e.key === '5') setColor('black');
});

// ═══════════════════════════════════════════════
//  STYLE POPOVER — one consolidated panel for colour,
//  line width/style, and font size (mirrors #ctx-menu's
//  position:fixed + open-class pattern).
// ═══════════════════════════════════════════════
function toggleStylePopover(e) {
  e.stopPropagation();
  const pop = document.getElementById('style-popover');
  if (pop.classList.contains('open')) { closeStylePopover(); return; }
  _spTargetAnnotId = null; // ribbon trigger always edits the default style for the next annotation
  renderStylePopover();
  const r = e.currentTarget.getBoundingClientRect();
  pop.style.left = '0px'; pop.style.top = '0px';
  pop.classList.add('open');
  const pw = pop.offsetWidth, ph = pop.offsetHeight;
  let left = r.left, top = r.bottom + 6;
  if (left + pw > window.innerWidth - 8) left = window.innerWidth - pw - 8;
  if (left < 8) left = 8;
  if (top + ph > window.innerHeight - 8) top = r.top - ph - 6;
  pop.style.left = left + 'px';
  pop.style.top  = top + 'px';
}

// Right-click → Style… opens the same popover, but scoped to one existing
// annotation: every control mutates that annotation directly (with a single
// history entry on release) instead of the global "next annotation" style.
function openAnnotStylePopover(annotId, cx, cy) {
  _spTargetAnnotId = annotId;
  const pop = document.getElementById('style-popover');
  renderStylePopover();
  pop.style.left = '0px'; pop.style.top = '0px';
  pop.classList.add('open');
  const pw = pop.offsetWidth, ph = pop.offsetHeight;
  pop.style.left = Math.max(8, Math.min(cx, window.innerWidth  - pw - 8)) + 'px';
  pop.style.top  = Math.max(8, Math.min(cy, window.innerHeight - ph - 8)) + 'px';
}
function closeStylePopover() {
  document.getElementById('style-popover').classList.remove('open');
  _spTargetAnnotId = null;
}
function _spTarget() {
  return _spTargetAnnotId != null ? annots.find(x => x.id === _spTargetAnnotId) : null;
}
function _spCommit() {
  if (_spTargetAnnotId != null) pushHistory();
}
document.addEventListener('mousedown', e => {
  const pop = document.getElementById('style-popover');
  if (pop.classList.contains('open') && !pop.contains(e.target) && !e.target.closest('.custom-trigger')) {
    closeStylePopover();
  }
});

const SP_STROKE_TYPES  = ['rect','circle','line','arrow','cloud','pen','measure','area'];
const SP_FONT_TYPES    = ['text'];
const SP_OPACITY_TYPES = ['highlight','rectfill','text'];
const SP_BOX_TYPES     = ['text'];
const SP_ALIGN_TYPES   = ['text'];

function renderStylePopover() {
  const body = document.getElementById('sp-body');
  const presets = [8,10,12,14,16,20,24];
  const strokePresets = [{v:2,lbl:'Fine'},{v:4,lbl:'Med'},{v:8,lbl:'Thick'},{v:14,lbl:'Bold'}];

  const target   = _spTarget();
  const curColor = target ? target.Color             : Color;
  const curStroke= target ? (target.sw ?? _strokeW)  : _strokeW;
  const curLine  = target ? (target.lineStyle || 'solid') : lineStyle;
  const curFont  = target ? (target.fontSize || 12)  : fontSize;
  const curOpac  = target ? (target.opacity || 80)   : annotOpacity;
  const curBox   = target ? (target.box !== false)   : textBoxDefault;
  const curHAlign = target ? (target.textAlign || 'center') : textAlignDefault;
  const curVAlign = target ? (target.vAlign || 'center')    : vAlignDefault;

  const showStroke  = !target || SP_STROKE_TYPES.includes(target.type);
  const showFont    = !target || SP_FONT_TYPES.includes(target.type);
  const showOpacity = !target || SP_OPACITY_TYPES.includes(target.type);
  const showBox     = !target || SP_BOX_TYPES.includes(target.type);
  const showAlign   = !target || SP_ALIGN_TYPES.includes(target.type);

  body.innerHTML =
    (target ? '<div class="sp-label" style="opacity:.6;margin-bottom:6px">Editing ' +
      (typeLabels[target.type] || target.type) + '</div>' : '') +
    '<div class="sp-label">Colour</div>' +
    '<div class="sp-row" style="margin-bottom:8px">' +
      '<div class="rcsw cy' + (curColor==='yellow'?' active':'') + '" onclick="setColor(\'yellow\');_spCommit()" title="Yellow (1)"></div>' +
      '<div class="rcsw cg' + (curColor==='green'?' active':'') + '" onclick="setColor(\'green\');_spCommit()" title="Green (2)"></div>' +
      '<div class="rcsw cr' + (curColor==='red'?' active':'') + '" onclick="setColor(\'red\');_spCommit()" title="Red (3)"></div>' +
      '<div class="rcsw cb' + (curColor==='blue'?' active':'') + '" onclick="setColor(\'blue\');_spCommit()" title="Blue (4)"></div>' +
      '<div class="rcsw ck' + (curColor==='black'?' active':'') + '" onclick="setColor(\'black\');_spCommit()" title="Black (5)"></div>' +
    '</div>' +
    '<canvas id="sp-sv" width="176" height="90"></canvas>' +
    '<input type="range" id="sp-hue" min="0" max="360" value="45">' +
    '<div class="sp-row"><div id="sp-preview"></div><input id="sp-hex" type="text" maxlength="7" value="#fbbf24"></div>' +
    '<div id="sp-recents"></div>' +

    (showStroke ?
    '<div class="sp-label" style="margin-top:4px">Line width</div>' +
    '<div class="sp-presets">' + strokePresets.map(p =>
      '<button class="sp-preset-btn' + (curStroke === p.v ? ' active' : '') + '" onclick="applyStrokePreset(' + p.v + ')">' + p.lbl + '</button>'
    ).join('') + '</div>' +
    '<div class="sp-row"><input type="range" id="sp-stroke" min="1" max="24" value="' + curStroke + '">' +
    '<span id="sp-stroke-val" style="font-family:var(--mono);font-size:11px;width:34px;text-align:right">' + curStroke + 'px</span></div>' +
    '<div id="sp-stroke-preview"></div>' +

    '<div class="sp-label" style="margin-top:10px">Line style</div>' +
    '<div class="sp-presets">' +
      '<button class="sp-preset-btn' + (curLine==='solid'?' active':'') + '" onclick="applyLineStyle(\'solid\')">Solid</button>' +
      '<button class="sp-preset-btn' + (curLine==='dashed'?' active':'') + '" onclick="applyLineStyle(\'dashed\')">Dashed</button>' +
      '<button class="sp-preset-btn' + (curLine==='dotted'?' active':'') + '" onclick="applyLineStyle(\'dotted\')">Dotted</button>' +
    '</div>' : '') +

    (showFont ?
    '<div class="sp-label" style="margin-top:10px">Font size</div>' +
    '<div class="sp-presets">' + presets.map(v =>
      '<button class="sp-preset-btn' + (v === curFont ? ' active' : '') + '" onclick="applyFontPreset(' + v + ')">' + v + 'pt</button>'
    ).join('') + '</div>' +
    '<div class="sp-row"><input type="number" id="sp-font-input" min="6" max="96" value="' + curFont + '">' +
    '<span style="font-size:10px;color:var(--gray-500)">pt</span></div>' : '') +

    (showAlign ?
    '<div class="sp-label" style="margin-top:10px">Horizontal align</div>' +
    '<div class="sp-presets" id="sp-halign">' +
      '<button class="sp-preset-btn' + (curHAlign==='left'?' active':'')   + '" data-v="left"   onclick="setTextAlign(\'left\')">Left</button>' +
      '<button class="sp-preset-btn' + (curHAlign==='center'?' active':'') + '" data-v="center" onclick="setTextAlign(\'center\')">Center</button>' +
      '<button class="sp-preset-btn' + (curHAlign==='right'?' active':'')  + '" data-v="right"  onclick="setTextAlign(\'right\')">Right</button>' +
    '</div>' +
    '<div class="sp-label" style="margin-top:8px">Vertical align</div>' +
    '<div class="sp-presets" id="sp-valign">' +
      '<button class="sp-preset-btn' + (curVAlign==='top'?' active':'')    + '" data-v="top"    onclick="setVAlign(\'top\')">Top</button>' +
      '<button class="sp-preset-btn' + (curVAlign==='center'?' active':'') + '" data-v="center" onclick="setVAlign(\'center\')">Middle</button>' +
      '<button class="sp-preset-btn' + (curVAlign==='bottom'?' active':'') + '" data-v="bottom"  onclick="setVAlign(\'bottom\')">Bottom</button>' +
    '</div>' : '') +

    (showBox ?
    '<div class="sp-label" style="margin-top:10px">Text box</div>' +
    '<label class="sp-row" style="align-items:center;gap:6px;cursor:pointer">' +
      '<input type="checkbox" id="sp-textbox"' + (curBox ? ' checked' : '') + '>' +
      '<span style="font-size:11px">Show border around text</span>' +
    '</label>' : '') +

    (showOpacity ?
    '<div class="sp-label" style="margin-top:10px">Opacity</div>' +
    '<input type="range" id="sp-opacity" min="20" max="100" value="' + curOpac + '" step="10">' : '');

  initColorPopover();
  if (showStroke) initStrokePopover();
  if (showOpacity) {
    const op = document.getElementById('sp-opacity');
    op.oninput  = e => setOpacity(e.target.value);
    op.onchange = () => _spCommit();
  }
  if (showFont) {
    const fi = document.getElementById('sp-font-input');
    fi.addEventListener('keydown', e => { if (e.key === 'Enter') applyCustomFont(); });
    fi.addEventListener('blur', applyCustomFont);
  }
  if (showBox) {
    const cb = document.getElementById('sp-textbox');
    cb.addEventListener('change', () => setTextBox(cb.checked));
  }
}

// ── Colour section: HSV square + hue slider + hex input + recents ──
let _spHue = 45;
function initColorPopover() {
  const canvas = document.getElementById('sp-sv');
  const ctx = canvas.getContext('2d');
  function draw() {
    const w = canvas.width, h = canvas.height;
    ctx.fillStyle = `hsl(${_spHue},100%,50%)`;
    ctx.fillRect(0, 0, w, h);
    const gw = ctx.createLinearGradient(0, 0, w, 0);
    gw.addColorStop(0, '#fff'); gw.addColorStop(1, 'rgba(255,255,255,0)');
    ctx.fillStyle = gw; ctx.fillRect(0, 0, w, h);
    const gb = ctx.createLinearGradient(0, 0, 0, h);
    gb.addColorStop(0, 'rgba(0,0,0,0)'); gb.addColorStop(1, '#000');
    ctx.fillStyle = gb; ctx.fillRect(0, 0, w, h);
  }
  draw();
  const hue = document.getElementById('sp-hue');
  hue.value = _spHue;
  hue.oninput = () => { _spHue = +hue.value; draw(); };
  function pick(e) {
    const r = canvas.getBoundingClientRect();
    const x = Math.max(0, Math.min(canvas.width - 1, Math.round((e.clientX - r.left) * (canvas.width / r.width))));
    const y = Math.max(0, Math.min(canvas.height - 1, Math.round((e.clientY - r.top) * (canvas.height / r.height))));
    const d = ctx.getImageData(x, y, 1, 1).data;
    const hex = '#' + [d[0], d[1], d[2]].map(v => v.toString(16).padStart(2, '0')).join('');
    setSpHex(hex);
    setColor(hex);
  }
  let dragging = false;
  canvas.onmousedown = e => { dragging = true; pick(e); };
  window.addEventListener('mousemove', e => { if (dragging) pick(e); });
  window.addEventListener('mouseup', () => {
    if (dragging) { addRecentColor(document.getElementById('sp-hex').value); _spCommit(); }
    dragging = false;
  });
  document.getElementById('sp-hex').addEventListener('input', e => {
    setSpHex(e.target.value, false);
    if (isHexColor(e.target.value)) setColor(e.target.value);
  });
  document.getElementById('sp-hex').addEventListener('change', e => {
    if (isHexColor(e.target.value)) { addRecentColor(e.target.value); _spCommit(); }
  });
  renderRecentColors();
  const startColor = _spTarget()?.Color ?? Color;
  setSpHex(isHexColor(startColor) ? startColor : '#fbbf24');
}
function setSpHex(hex, updateInput = true) {
  if (!isHexColor(hex) && !updateInput) return;
  const preview = document.getElementById('sp-preview');
  if (preview) preview.style.background = hex;
  if (updateInput) {
    const input = document.getElementById('sp-hex');
    if (input) input.value = hex;
  }
}
function getRecentColors() {
  try { return JSON.parse(localStorage.getItem('engdoc_recent_colors') || '[]'); }
  catch (e) { return []; }
}
function addRecentColor(hex) {
  if (!isHexColor(hex)) return;
  const list = [hex, ...getRecentColors().filter(c => c !== hex)].slice(0, 8);
  localStorage.setItem('engdoc_recent_colors', JSON.stringify(list));
  renderRecentColors();
}
function renderRecentColors() {
  const wrap = document.getElementById('sp-recents');
  if (!wrap) return;
  wrap.innerHTML = getRecentColors().map(hex =>
    `<div class="sp-recent-sw" style="background:${hex}" onclick="setSpHex('${hex}');setColor('${hex}');_spCommit()" title="${hex}"></div>`
  ).join('');
}

// ── Line width / style section ──
function initStrokePopover() {
  const slider = document.getElementById('sp-stroke');
  const preview = document.getElementById('sp-stroke-preview');
  const val = document.getElementById('sp-stroke-val');
  const update = (v) => { preview.style.height = v + 'px'; val.textContent = v + 'px'; };
  update(slider.value);
  slider.oninput = () => {
    update(slider.value);
    setStrokeW(parseInt(slider.value));
    document.querySelectorAll('#sp-body .sp-presets')[0]?.querySelectorAll('.sp-preset-btn').forEach(b => b.classList.remove('active'));
  };
  slider.onchange = () => _spCommit();
}
function applyStrokePreset(v) {
  setStrokeW(v);
  const slider = document.getElementById('sp-stroke');
  if (slider) { slider.value = v; slider.dispatchEvent(new Event('input')); }
  document.querySelectorAll('#sp-body .sp-presets')[0]?.querySelectorAll('.sp-preset-btn').forEach(b =>
    b.classList.toggle('active', b.textContent === {2:'Fine',4:'Med',8:'Thick',14:'Bold'}[v]));
  _spCommit();
}
function applyLineStyle(style) {
  const a = _spTarget();
  if (a) { a.lineStyle = style; syncAnnots(); } else { lineStyle = style; }
  document.querySelectorAll('#sp-body .sp-presets')[1]?.querySelectorAll('.sp-preset-btn').forEach(b =>
    b.classList.toggle('active', b.textContent.toLowerCase() === style));
  _spCommit();
}

// ── Font size section ──
function applyFontPreset(v) {
  setFontSize(v);
  document.querySelectorAll('#sp-body .sp-presets')[2]?.querySelectorAll('.sp-preset-btn').forEach(b =>
    b.classList.toggle('active', b.textContent === v + 'pt'));
  const fi = document.getElementById('sp-font-input');
  if (fi) fi.value = v;
  _spCommit();
}
function applyCustomFont() {
  const fi = document.getElementById('sp-font-input');
  if (!fi) return;
  const v = parseInt(fi.value);
  if (!v || v < 6 || v > 96) return;
  setFontSize(v);
  _spCommit();
}

// Single applyZoom post-hook — updates ribbon, labels, and measure annotations
const _origApplyZoomBase = applyZoom;
applyZoom = async function(val) {
  await _origApplyZoomBase(val);
  const pct = Math.round(zoom * 100) + '%';
  const sbZoom  = document.getElementById('sb-zoom');
  if (sbZoom)  sbZoom.innerHTML = '<div class="sbdot b"></div>' + pct;
  const sel = document.getElementById('zsel');
  if (sel && !isNaN(parseFloat(val))) sel.value = String(parseFloat(val));
  // Update measure labels in-place (no DOM rebuild)
  recalcMeasureLabels();
};

// ═══════════════════════════════════════════════
//  MARQUEE ZOOM
// ═══════════════════════════════════════════════
let _mqStart = null;

function initMarqueeZoom() {
  const viewer = document.getElementById('viewer');
  const marquee = document.getElementById('zoom-marquee');

  viewer.addEventListener('mousedown', e => {
    if (tool !== 'zoombox') return;
    if (e.button !== 0) return;
    e.preventDefault();
    _mqStart = { cx: e.clientX, cy: e.clientY };
    marquee.style.cssText = 'display:block;position:fixed;border:2px solid #2563eb;' +
      'background:rgba(37,99,235,.07);pointer-events:none;z-index:500;' +
      'left:' + e.clientX + 'px;top:' + e.clientY + 'px;width:0;height:0';
  }, true);

  window.addEventListener('mousemove', e => {
    if (!_mqStart || tool !== 'zoombox') return;
    const lx = Math.min(e.clientX, _mqStart.cx);
    const ly = Math.min(e.clientY, _mqStart.cy);
    marquee.style.left   = lx + 'px';
    marquee.style.top    = ly + 'px';
    marquee.style.width  = Math.abs(e.clientX - _mqStart.cx) + 'px';
    marquee.style.height = Math.abs(e.clientY - _mqStart.cy) + 'px';
  });

  window.addEventListener('mouseup', async e => {
    if (!_mqStart || tool !== 'zoombox') return;
    marquee.style.display = 'none';
    const selW = Math.abs(e.clientX - _mqStart.cx);
    const selH = Math.abs(e.clientY - _mqStart.cy);
    const start = _mqStart;
    _mqStart = null;
    if (selW < 12 || selH < 12) return; // too small — ignore

    const vr = viewer.getBoundingClientRect();
    // Centre of selection in current viewer-scroll coordinates
    const centreX = Math.min(e.clientX, start.cx) + selW / 2 - vr.left + viewer.scrollLeft;
    const centreY = Math.min(e.clientY, start.cy) + selH / 2 - vr.top  + viewer.scrollTop;

    // New zoom = fit the selection width/height into the viewer
    const newZoom = Math.min(
      (vr.width  / selW) * zoom,
      (vr.height / selH) * zoom,
      zoom * 10
    );
    const scale = newZoom / zoom;
    await applyZoom(String(Math.round(newZoom * 100) / 100));

    // After re-render, scroll so selection centre is in the viewport centre
    viewer.scrollLeft = centreX * scale - vr.width  / 2;
    viewer.scrollTop  = centreY * scale - vr.height / 2;

    // Drop back to pan
    setTool('pan');
  });
}
initMarqueeZoom();

// ── Ctrl+Wheel zoom-to-cursor ──
document.getElementById('viewer').addEventListener('wheel', async e => {
  if (!e.ctrlKey && !e.metaKey) return;
  e.preventDefault();
  if (!pdf) return;
  const viewer = document.getElementById('viewer');
  const vr = viewer.getBoundingClientRect();
  const mouseX = e.clientX - vr.left + viewer.scrollLeft;
  const mouseY = e.clientY - vr.top  + viewer.scrollTop;
  const factor = e.deltaY > 0 ? 0.88 : 1.14;
  const newZoom = Math.max(0.2, Math.min(8, zoom * factor));
  const scale = newZoom / zoom;
  await applyZoom(String(Math.round(newZoom * 100) / 100));
  viewer.scrollLeft = mouseX * scale - (e.clientX - vr.left);
  viewer.scrollTop  = mouseY * scale - (e.clientY - vr.top);
}, { passive: false });

// ═══════════════════════════════════════════════
//  ANNOTATION MOVE — drag-handle system
//  A small grip handle (⠿) is injected into each
//  annotation element when in pan mode.
//  Dragging the grip moves the annotation.
//  Clicking anywhere else on the page always pans.
//  This means pan never conflicts with annotations.
// ═══════════════════════════════════════════════
let _moveState = null;

function makeDraggable(el, a, ov) {
  // No-op: dragging is handled by per-annotation grip handles
  // injected by refreshAnnotMoveHandles() on tool change
}

const MOVE_TYPES = new Set(['highlight','rect','rectfill','strike','circle','text',
                             'cloud','pen','texthighlight','arrow','line','measure',
                             'area','stamp','image']);

// ── Ghost shown while dragging ──
function createGhost(el, ov) {
  const g = el.cloneNode(true);
  g.id = 'ann-drag-ghost';
  g.removeAttribute('data-aid');
  g.querySelectorAll('input,textarea,button,.an-reply-input-wrap,.ann-move-handle').forEach(c => c.remove());
  g.style.cssText += ';opacity:0.45;pointer-events:none;z-index:200;transition:none;' +
    'outline:2px dashed rgba(37,99,235,0.7);box-shadow:0 4px 16px rgba(0,0,0,.18);';
  ov.appendChild(g);
  return g;
}
function removeGhost() {
  document.getElementById('ann-drag-ghost')?.remove();
}

// ── Wire a move overlay onto each annotation element ──
// The overlay is a transparent div covering the whole annotation.
// In pan mode it intercepts mousedown, starts the drag, and prevents
// the event reaching the page overlay (so pan doesn't also fire).
function wireMoveOverlay(el, ann, ov) {
  const movEl = document.createElement('div');
  movEl.className = 'ann-move-overlay';
  movEl.title = 'Drag to move';
  movEl.style.cssText =
    'position:absolute;inset:0;z-index:10;cursor:grab;' +
    'pointer-events:none;border-radius:inherit;';

  movEl.addEventListener('mousedown', ev => {
    if (tool !== 'pan') return;
    if (ev.button !== 0) return;
    ev.stopPropagation();
    ev.preventDefault();

    const ovRect = ov.getBoundingClientRect();
    const ovW = ovRect.width, ovH = ovRect.height;
    const startX = ev.clientX, startY = ev.clientY;
    const orig = {
      x: ann.x, y: ann.y,
      x1: ann.x1, y1: ann.y1, x2: ann.x2, y2: ann.y2,
      lx: ann.lx, ly: ann.ly,
      leaderX: ann.leaderX, leaderY: ann.leaderY,
      points: ann.points ? JSON.parse(JSON.stringify(ann.points)) : null,
    };
    // If this annotation's resize/endpoint handles are currently showing,
    // they must be kept in sync while it's dragged — they're separate DOM
    // nodes positioned once at click time, so nothing else re-anchors them
    // to the annotation's new position while it moves.
    const wasSelected = _selectedAnnotId === ann.id;

    let hasMoved = false, ghost = null;
    movEl.style.cursor = 'grabbing';
    document.body.style.userSelect = 'none';

    const onMove = mv => {
      const dx = (mv.clientX - startX) / ovW * 100;
      const dy = (mv.clientY - startY) / ovH * 100;
      if (!hasMoved && Math.hypot(mv.clientX - startX, mv.clientY - startY) < 4) return;

      if (!hasMoved) {
        hasMoved = true;
        ghost = createGhost(el, ov);
        el.style.opacity = '0.2';
      }

      // Update data model
      if (orig.x  !== undefined) { ann.x  = orig.x  + dx; ann.y  = orig.y  + dy; }
      if (orig.x1 !== undefined) {
        ann.x1 = orig.x1 + dx; ann.y1 = orig.y1 + dy;
        ann.x2 = orig.x2 + dx; ann.y2 = orig.y2 + dy;
      }
      if (orig.points) ann.points = orig.points.map(p => ({ x: p.x + dx/100, y: p.y + dy/100 }));
      if (orig.lx !== undefined) { ann.lx = orig.lx + dx; ann.ly = orig.ly + dy; }
      // A text box's leader arrow tip is NOT translated with the box — it
      // stays pointing at the same fixed spot on the drawing while the box moves.

      // Move ghost live
      if (ghost) {
        if (ann.x !== undefined) {
          ghost.style.left = ann.x + '%'; ghost.style.top = ann.y + '%';
        } else {
          const px = dx / 100 * ovW, py = dy / 100 * ovH;
          ghost.style.transform = 'translate(' + px + 'px,' + py + 'px)';
        }
      }

      // Keep resize/endpoint handles tracking the annotation as it moves
      if (wasSelected) {
        if (ann.x1 !== undefined && ['line', 'arrow', 'measure'].includes(ann.type)) {
          showEndpointHandles(ann, ov);
        } else if (ann.x !== undefined && RESIZABLE.includes(ann.type)) {
          showResizeHandles(el, ann, ov);
        }
      }
    };

    const onUp = () => {
      document.removeEventListener('mousemove', onMove);
      document.removeEventListener('mouseup', onUp);
      movEl.style.cursor = 'grab';
      document.body.style.userSelect = '';
      removeGhost();
      el.style.opacity = '';
      if (hasMoved) {
        // Immediately clear all move overlays/proxies before syncAnnots rebuilds them
        // This prevents a flash of the old-position bounding box
        ov.querySelectorAll('[data-svg-proxy-for]').forEach(e => e.remove());
        ov.querySelectorAll('.ann-move-overlay').forEach(e => e.remove());
        syncAnnots();
        pushHistory();
        // syncAnnots rebuilds the annotation element, so `el` is now detached —
        // re-show handles against the fresh element once it exists in the DOM
        if (wasSelected) {
          setTimeout(() => {
            const newEl = ov.querySelector('[data-aid="' + ann.id + '"]');
            const freshAnn = annots.find(x => x.id === ann.id);
            if (!newEl || !freshAnn) return;
            if (freshAnn.x1 !== undefined && ['line', 'arrow', 'measure'].includes(freshAnn.type)) {
              showEndpointHandles(freshAnn, ov);
            } else if (freshAnn.x !== undefined && RESIZABLE.includes(freshAnn.type)) {
              showResizeHandles(newEl, freshAnn, ov);
            }
          }, 50);
        }
      } else if (['line', 'arrow', 'measure'].includes(ann.type)) {
        // Pure click (no drag) on a line/arrow/measure — show endpoint handles
        showEndpointHandles(ann, ov);
      } else if (ann.x !== undefined) {
        // Pure click on any box annotation — show 8-point resize handles
        showResizeHandles(el, ann, ov);
      }
    };

    document.addEventListener('mousemove', onMove);
    document.addEventListener('mouseup', onUp);
  });

  // Keep position covering the annotation
  el.style.position = 'absolute';
  el.style.overflow = 'visible';
  el.appendChild(movEl);
  return movEl;
}

function refreshAnnotMoveHandles() {
  // Enable/disable move overlays based on tool
  document.querySelectorAll('.ann-move-overlay').forEach(m => {
    m.style.pointerEvents = tool === 'pan' ? 'all' : 'none';
    m.style.cursor = tool === 'pan' ? 'grab' : '';
  });
}

// Refresh handles whenever tool changes or annotations change
// refreshAnnotMoveHandles now called in _ribbonSetTool patch below

const _origSyncAnnotsMove = syncAnnots;
syncAnnots = function() {
  _origSyncAnnotsMove();
  if (tool === 'pan') setTimeout(refreshAnnotMoveHandles, 60);
};

// Helper: snapshot current state to undo history
function pushHistory() {
  const snap = {
    annots:    JSON.parse(JSON.stringify(annots)),
    emmaRows:  JSON.parse(JSON.stringify(emmaRows)),
  };
  // Trim any redo tail
  if (typeof historyIdx !== 'undefined') history.splice(historyIdx + 1);
  history.push(snap);
  if (typeof historyIdx !== 'undefined') historyIdx = history.length - 1;
}

// ═══════════════════════════════════════════════
//  RESIZE HANDLES
//  For annotations that have x/y/w/h (box types):
//  highlight, rect, rectfill, strike, cloud, image, text
//  Shows 8-point handles in pan mode when clicked.
//  text also scales fontSize as the box is resized (see onMove below).
// ═══════════════════════════════════════════════
let _selectedAnnotId = null;
let _resizing = null; // { id, handle, startX, startY, orig{x,y,w,h,fontSize}, ovW, ovH }

const RESIZABLE = ['highlight','rect','rectfill','strike','cloud','image','text'];
const FONT_SCALABLE = ['text'];

function showResizeHandles(el, a, ov) {
  // Line-like types have two endpoints rather than a bounding box — use endpoint handles
  if (a.x1 !== undefined && ['line', 'arrow', 'measure'].includes(a.type)) {
    showEndpointHandles(a, ov);
    return;
  }
  // text boxes size to their content until first resized — backfill w/h
  // from the rendered element so handles (and edge-arrow buttons) have a box to grab
  if ((a.w === undefined || a.h === undefined) && FONT_SCALABLE.includes(a.type)) {
    const ovRect = ov.getBoundingClientRect();
    const elRect = el.getBoundingClientRect();
    if (a.w === undefined) a.w = elRect.width  / ovRect.width  * 100;
    if (a.h === undefined) a.h = elRect.height / ovRect.height * 100;
  }

  removeResizeHandles();
  _selectedAnnotId = a.id;
  el.classList.add('ann-selected');

  if (a.type === 'text') showEdgeArrowButtons(a, ov);

  const handles = [
    { cls:'nw', lx:'0%',   ly:'0%'   },
    { cls:'n',  lx:'50%',  ly:'0%'   },
    { cls:'ne', lx:'100%', ly:'0%'   },
    { cls:'e',  lx:'100%', ly:'50%'  },
    { cls:'se', lx:'100%', ly:'100%' },
    { cls:'s',  lx:'50%',  ly:'100%' },
    { cls:'sw', lx:'0%',   ly:'100%' },
    { cls:'w',  lx:'0%',   ly:'50%'  },
  ];

  handles.forEach(({ cls, lx, ly }) => {
    const h = document.createElement('div');
    h.className = 'resize-handle ' + cls;
    // Position relative to the annotation element itself
    // The handle is absolute within the overlay; compute position from annot coords
    h.style.left  = (a.x + (parseFloat(lx) / 100) * a.w) + '%';
    h.style.top   = (a.y + (parseFloat(ly) / 100) * a.h) + '%';
    h.dataset.handle = cls;
    h.dataset.annotId = a.id;

    h.addEventListener('mousedown', ev => {
      ev.stopPropagation();
      ev.preventDefault();
      const ovRect = ov.getBoundingClientRect();
      _resizing = {
        id: a.id, handle: cls,
        startX: ev.clientX, startY: ev.clientY,
        origX: a.x, origY: a.y, origW: a.w, origH: a.h,
        origFontSize: FONT_SCALABLE.includes(a.type) ? (a.fontSize || 13) : null,
        ovW: ovRect.width, ovH: ovRect.height,
      };

      const onMove = mv => {
        if (!_resizing) return;
        const dx = (mv.clientX - _resizing.startX) / _resizing.ovW * 100;
        const dy = (mv.clientY - _resizing.startY) / _resizing.ovH * 100;
        const ann = annots.find(x => x.id === _resizing.id);
        if (!ann) return;

        const { handle: hd, origX: ox, origY: oy, origW: ow, origH: oh, origFontSize } = _resizing;

        // Apply delta based on which handle
        if (hd.includes('e'))  ann.w = Math.max(1, ow + dx);
        if (hd.includes('s'))  ann.h = Math.max(1, oh + dy);
        if (hd.includes('w'))  { ann.x = ox + dx; ann.w = Math.max(1, ow - dx); }
        if (hd.includes('n'))  { ann.y = oy + dy; ann.h = Math.max(1, oh - dy); }

        // text: scale font size with the box so the content grows/shrinks
        // with the handle drag — corner handles scale both axes (averaged),
        // single-edge handles scale by that edge alone.
        if (origFontSize != null) {
          const wRatio = ann.w / ow, hRatio = ann.h / oh;
          const scale = hd.length === 2 ? (wRatio + hRatio) / 2
            : (hd === 'e' || hd === 'w') ? wRatio : hRatio;
          ann.fontSize = Math.max(6, Math.min(200, origFontSize * scale));
        }

        // Live DOM update — just reposition the ann element directly
        const domEl = ov.querySelector('[data-aid="' + _resizing.id + '"]');
        if (domEl) {
          domEl.style.left   = ann.x + '%';
          domEl.style.top    = ann.y + '%';
          if (domEl.style.width  !== undefined) domEl.style.width  = ann.w + '%';
          if (domEl.style.height !== undefined) domEl.style.height = ann.h + '%';
          if (origFontSize != null) domEl.style.fontSize = ann.fontSize + 'px';
        }
        // Keep any leader arrow anchored to the box edge while it resizes
        if (ann.type === 'text' && ann.leaderEdge) buildTextLeaderSvg(ann, ov);
        // Reposition handles live
        showResizeHandles(domEl || el, ann, ov);
      };

      const onUp = () => {
        if (_resizing) { syncAnnots(); pushHistory(); }
        _resizing = null;
        document.removeEventListener('mousemove', onMove);
        document.removeEventListener('mouseup', onUp);
        // Re-show handles after full re-render
        setTimeout(() => {
          const newEl = ov.querySelector('[data-aid="' + a.id + '"]');
          const newAnn = annots.find(x => x.id === a.id);
          if (newEl && newAnn) showResizeHandles(newEl, newAnn, ov);
        }, 50);
      };

      document.addEventListener('mousemove', onMove);
      document.addEventListener('mouseup', onUp);
    });

    ov.appendChild(h);
  });
}

// Live-update SVG line/arrow endpoints during handle drag (ticks & labels rebuilt by syncAnnots on release)
function updateLineSvgEndpoints(wrap, ann) {
  const svg = wrap.querySelector('svg');
  if (!svg) return;
  svg.querySelectorAll('line').forEach(l => {
    l.setAttribute('x1', ann.x1); l.setAttribute('y1', ann.y1);
    l.setAttribute('x2', ann.x2); l.setAttribute('y2', ann.y2);
  });
}

function showEndpointHandles(ann, ov) {
  removeResizeHandles();
  _selectedAnnotId = ann.id;

  const makeHandle = (px, py, which) => {
    const h = document.createElement('div');
    h.className = 'resize-handle ep-handle';
    h.style.left = px + '%';
    h.style.top  = py + '%';
    h.dataset.handle   = which;
    h.dataset.annotId  = ann.id;

    h.addEventListener('mousedown', ev => {
      ev.stopPropagation();
      ev.preventDefault();
      const ovRect = ov.getBoundingClientRect();

      const onMove = mv => {
        const nx = (mv.clientX - ovRect.left) / ovRect.width  * 100;
        const ny = (mv.clientY - ovRect.top)  / ovRect.height * 100;
        if (which === 'p1') { ann.x1 = nx; ann.y1 = ny; }
        else                { ann.x2 = nx; ann.y2 = ny; }
        // Move this handle live
        h.style.left = (which === 'p1' ? ann.x1 : ann.x2) + '%';
        h.style.top  = (which === 'p1' ? ann.y1 : ann.y2) + '%';
        // Update the SVG line so the annotation tracks the handle
        const domEl = ov.querySelector('[data-aid="' + ann.id + '"]');
        if (domEl) updateLineSvgEndpoints(domEl, ann);
      };

      const onUp = () => {
        document.removeEventListener('mousemove', onMove);
        document.removeEventListener('mouseup', onUp);
        syncAnnots();
        pushHistory();
        // Re-show handles at updated positions
        setTimeout(() => {
          const freshAnn = annots.find(x => x.id === ann.id);
          if (freshAnn) showEndpointHandles(freshAnn, ov);
        }, 30);
      };

      document.addEventListener('mousemove', onMove);
      document.addEventListener('mouseup', onUp);
    });

    ov.appendChild(h);
  };

  makeHandle(ann.x1, ann.y1, 'p1');
  makeHandle(ann.x2, ann.y2, 'p2');
}

function removeResizeHandles() {
  document.querySelectorAll('.resize-handle').forEach(h => h.remove());
  document.querySelectorAll('.edge-arrow-btn').forEach(h => h.remove());
  document.querySelectorAll('.ann-selected').forEach(el => el.classList.remove('ann-selected'));
  _selectedAnnotId = null;
}

// ── "+" edge buttons on a selected text box — drag from any edge to add
// a leader arrow pointing out from that edge (replaces the old note tool's
// two-click arrow-then-box flow). One button per edge; dragging the tip
// while it's already active lets you reposition or (dragged back onto the
// box) remove the arrow — see buildTextLeaderSvg.
function showEdgeArrowButtons(a, ov) {
  const edges = [
    { edge: 'top',    lx: '50%', ly: '0%'   },
    { edge: 'right',  lx: '100%',ly: '50%'  },
    { edge: 'bottom', lx: '50%', ly: '100%' },
    { edge: 'left',   lx: '0%',  ly: '50%'  },
  ];

  edges.forEach(({ edge, lx, ly }) => {
    const btn = document.createElement('div');
    btn.className = 'edge-arrow-btn';
    btn.textContent = '+';
    btn.title = 'Drag to add a leader arrow';
    btn.style.left = (a.x + (parseFloat(lx) / 100) * a.w) + '%';
    btn.style.top  = (a.y + (parseFloat(ly) / 100) * a.h) + '%';
    btn.dataset.edge = edge;
    btn.dataset.annotId = a.id;

    btn.addEventListener('mousedown', ev => {
      ev.stopPropagation();
      ev.preventDefault();
      const ann = annots.find(x => x.id === a.id);
      if (!ann) return;
      const ovRect = ov.getBoundingClientRect();

      // Give the arrow an initial tip a short distance out from the edge,
      // in case the user releases without moving the mouse at all.
      ann.leaderEdge = edge;
      ann.leaderX = (ev.clientX - ovRect.left) / ovRect.width  * 100;
      ann.leaderY = (ev.clientY - ovRect.top)  / ovRect.height * 100;
      buildTextLeaderSvg(ann, ov);

      const onMove = mv => {
        ann.leaderX = (mv.clientX - ovRect.left) / ovRect.width  * 100;
        ann.leaderY = (mv.clientY - ovRect.top)  / ovRect.height * 100;
        // Only rebuild the line here — buildTextLeaderSvg also (re)creates
        // the drag handle, which would leak a duplicate on every mousemove
        updateTextLeaderLine(ann, ov);
        const handle = ov.querySelector('.leader-tip-handle[data-leader-handle="' + ann.id + '"]');
        if (handle) { handle.style.left = ann.leaderX + '%'; handle.style.top = ann.leaderY + '%'; }
      };

      const onUp = mv => {
        document.removeEventListener('mousemove', onMove);
        document.removeEventListener('mouseup',   onUp);
        // Released right on the box (essentially a click, not a drag) —
        // detach immediately rather than leaving a zero-length arrow
        const pin = ov.querySelector('[data-aid="' + ann.id + '"]');
        if (pin) {
          const pr = pin.getBoundingClientRect();
          const pad = LEADER_DETACH_PX;
          if (mv.clientX >= pr.left - pad && mv.clientX <= pr.right + pad &&
              mv.clientY >= pr.top  - pad && mv.clientY <= pr.bottom + pad) {
            delete ann.leaderEdge; delete ann.leaderX; delete ann.leaderY;
          }
        }
        syncAnnots();
        pushHistory();
        setTimeout(() => {
          const newEl = ov.querySelector('[data-aid="' + ann.id + '"]');
          const freshAnn = annots.find(x => x.id === ann.id);
          if (newEl && freshAnn) showResizeHandles(newEl, freshAnn, ov);
        }, 50);
      };

      document.addEventListener('mousemove', onMove);
      document.addEventListener('mouseup',   onUp);
    });

    ov.appendChild(btn);
  });
}

// Attach resize-handle trigger to annotation elements in pan mode
// Called from makeDraggable — on mousedown in pan mode, show handles
// Resize handles are shown by clicking annotations in pan mode (see showResizeHandles)
// Clicking empty overlay in pan mode deselects
document.addEventListener('mousedown', ev => {
  if (tool !== 'pan') return;
  if (ev.target.closest('.resize-handle')) return;
  if (ev.target.closest('[data-aid]')) return;
  if (ev.target.closest('.ann-move-handle')) return;
  removeResizeHandles();
});

// ═══════════════════════════════════════════════
//  3D PDF SUPPORT
//  PDF.js does not support 3D (U3D/PRC) content —
//  these are embedded as PDF annotations of type
//  '3D' and require a native renderer (Acrobat).
//  We detect them and offer a clear message plus
//  a download link so the user can open in Acrobat.
// ═══════════════════════════════════════════════

async function check3DContent(pdfDoc) {
  let found3D = false;
  try {
    for (let i = 1; i <= Math.min(pdfDoc.numPages, 10); i++) {
      const page = await pdfDoc.getPage(i);
      const annots3d = await page.getAnnotations();
      if (annots3d.some(a => a.subtype === '3D' || a.annotationType === 25)) {
        found3D = true; break;
      }
    }
  } catch(e) { /* non-fatal */ }

  if (found3D) {
    // Show a persistent banner in the viewer
    show3DBanner();
  }
}

function show3DBanner() {
  const existing = document.getElementById('banner-3d');
  if (existing) return;
  const banner = document.createElement('div');
  banner.id = 'banner-3d';
  banner.style.cssText = [
    'position:fixed;bottom:36px;left:50%;transform:translateX(-50%)',
    'background:#1e293b;Color:#fff;font-size:12px;font-family:var(--font)',
    'padding:10px 18px;border-radius:8px;z-index:600',
    'display:flex;align-items:center;gap:12px',
    'box-shadow:0 4px 20px rgba(0,0,0,.3);max-width:560px;text-align:left',
  ].join(';');
  banner.innerHTML = [
    '<svg viewBox="0 0 24 24" fill="none" stroke="#f59e0b" stroke-width="2" width="20" height="20" style="flex-shrink:0">',
    '<path d="M12 9v4m0 4h.01M10.29 3.86L1.82 18a2 2 0 001.71 3h16.94a2 2 0 001.71-3L13.71 3.86a2 2 0 00-3.42 0z"/></svg>',
    '<span><strong>3D content detected.</strong> PDF.js cannot render 3D annotations (U3D/PRC). ',
    'All 2D content, annotations and markup will work normally. ',
    'To view the 3D model, open the original file in <strong>Adobe Acrobat</strong>.</span>',
    '<button onclick="document.getElementById(\'banner-3d\').remove()" ',
    'style="background:none;border:none;Color:#94a3b8;cursor:pointer;font-size:16px;flex-shrink:0;padding:0 4px">✕</button>',
  ].join('');
  document.body.appendChild(banner);
}



// ── Copy feedback in select mode — handled by _selEnd in selection engine ──

// ═══════════════════════════════════════════════
//  CUSTOM TEXT SELECTION ENGINE
//  Works in any direction, with any text rotation.
//  Uses page-space hit testing, not DOM selection.
// ═══════════════════════════════════════════════
let _selState = null; // { pageNum, ov, svgEl, rectEl, x0, y0 }
let _selHits  = [];   // currently highlighted text items

function _selStart(ev, pageNum, ov) {
  if (tool !== 'select') return;
  if (ev.button !== 0) return;
  ev.preventDefault();
  ev.stopPropagation();

  // Always clear any previous selection before starting a new one
  _selClear();

  const r = ov.getBoundingClientRect();
  const x0 = ev.clientX - r.left;
  const y0 = ev.clientY - r.top;

  // Drag rectangle (CSS div — stays visible after release showing selection bounds)
  const rectEl = document.createElement('div');
  rectEl.className = 'sel-rect';
  rectEl.style.cssText = 'left:' + x0 + 'px;top:' + y0 + 'px;width:0;height:0';
  ov.appendChild(rectEl);

  // SVG overlay for text highlight rects — data attribute for reliable cleanup
  const svgEl = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svgEl.dataset.selSvg = '1';
  svgEl.style.cssText = 'position:absolute;inset:0;width:100%;height:100%;overflow:visible;pointer-events:none;z-index:5';
  ov.appendChild(svgEl);

  _selState = { pageNum, ov, svgEl, rectEl, x0, y0, x1: x0, y1: y0 };
}

function _selMove(ev) {
  if (!_selState || tool !== 'select') return;
  const { ov, rectEl, x0, y0 } = _selState;
  const r = ov.getBoundingClientRect();
  const x1 = ev.clientX - r.left;
  const y1 = ev.clientY - r.top;
  _selState.x1 = x1; _selState.y1 = y1;

  // Update drag rect — works in all directions
  const lx = Math.min(x0, x1), ly = Math.min(y0, y1);
  const lw = Math.abs(x1 - x0), lh = Math.abs(y1 - y0);
  rectEl.style.cssText = 'left:' + lx + 'px;top:' + ly + 'px;width:' + lw + 'px;height:' + lh + 'px';

  // Live hit-test and highlight
  _selHighlight(_selState);
}

function _selEnd(ev) {
  if (!_selState || tool !== 'select') return;

  _selHighlight(_selState);

  // Sort hits into reading order: top-to-bottom, then left-to-right within each line.
  // PDF extraction order is draw order, not reading order — this is why text copies backwards.
  const LINE_THRESHOLD = 0.6; // fraction of avg font height — items within this are on the same line
  const readingOrder = [..._selHits].sort((a, b) => {
    const avgH = ((a.h || 12) + (b.h || 12)) / 2;
    const lineDiff = (a.y - b.y) / avgH;
    if (Math.abs(lineDiff) > LINE_THRESHOLD) return a.y - b.y; // different lines: top first
    return a.x - b.x; // same line: left to right
  });
  const text = readingOrder.map(h => h.str).join(' ').replace(/\s+/g, ' ').trim();

  // Tiny drag with no hits = click = try to select the item under the cursor
  const isDot = Math.abs(_selState.x1 - _selState.x0) < 4 &&
                Math.abs(_selState.y1 - _selState.y0) < 4;

  if (isDot) {
    // Point-select: find the single text item the cursor is over
    const cx = _selState.x0, cy = _selState.y0;
    const items = _pageTextItems[_selState.pageNum] || [];
    const hit = items.find(item => _rectHitsItem(cx - 2, cy - 2, 4, 4, item));
    if (hit) {
      // Highlight just that item
      const { svgEl } = _selState;
      while (svgEl.firstChild) svgEl.removeChild(svgEl.firstChild);
      _selHits = [hit];
      const rect = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
      rect.setAttribute('class', 'sel-hit');
      rect.setAttribute('x', '0'); rect.setAttribute('y', '0');
      rect.setAttribute('width', hit.w.toFixed(1)); rect.setAttribute('height', hit.h.toFixed(1));
      const tx = hit.x, ty = hit.y - hit.h;
      const deg = hit.angle * 180 / Math.PI;
      rect.setAttribute('transform',
        'translate(' + tx.toFixed(1) + ',' + ty.toFixed(1) + ')' +
        (deg !== 0 ? ' rotate(' + deg.toFixed(2) + ')' : '')
      );
      svgEl.appendChild(rect);
      // Keep a tiny invisible rect el
      _selState.rectEl.style.cssText = 'left:' + (cx-2) + 'px;top:' + (cy-2) + 'px;width:4px;height:4px;border:none;background:none';
    } else {
      _selClear();
      _selState = null;
      return;
    }
  }

  if (!_selHits.length) {
    _selClear();
    _selState = null;
    return;
  }

  // Keep rectEl and svgEl visible as selection indicator
  // Remove the drag rect's border animation, keep the fill to show selected area
  const { rectEl } = _selState;
  rectEl.style.borderStyle = 'solid';
  rectEl.style.borderColor = 'rgba(37,99,235,0.35)';
  rectEl.style.background  = 'rgba(37,99,235,0.04)';

  // Copy to clipboard
  navigator.clipboard.writeText(text)
    .then(() => toast('Copied ' + text.length + ' chars · drag to reselect · Esc to clear', 2800))
    .catch(() => {
      const ta = document.createElement('textarea');
      ta.value = text; ta.style.cssText = 'position:fixed;opacity:0;pointer-events:none';
      document.body.appendChild(ta); ta.focus(); ta.select();
      try { document.execCommand('copy'); toast('Copied · Esc to clear', 2400); }
      catch(e) { toast('Press Ctrl+C to copy selection', 2400); }
      ta.remove();
    });

  _selState = null; // clear state ref but leave DOM elements for visual feedback
}

function _selHighlight(state) {
  const { pageNum, svgEl, x0, y0, x1, y1 } = state;
  // Selection rect in page CSS-pixel coords
  const rx = Math.min(x0, x1), ry = Math.min(y0, y1);
  const rw = Math.abs(x1 - x0), rh = Math.abs(y1 - y0);

  // Clear previous SVG rects
  while (svgEl.firstChild) svgEl.removeChild(svgEl.firstChild);
  _selHits = [];

  const items = _pageTextItems[pageNum];
  if (!items) return;

  items.forEach(item => {
    // item.x, item.y = CSS pixels, bottom-left origin (y increases downward from top)
    // Convert to top-left bounding box for the hit test
    if (!_rectHitsItem(rx, ry, rw, rh, item)) return;

    _selHits.push(item);

    // Draw highlight rect in SVG — use item's own transform for rotated text
    const rect = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
    rect.setAttribute('class', 'sel-hit');
    rect.setAttribute('x', '0');
    rect.setAttribute('y', '0');
    rect.setAttribute('width',  item.w.toFixed(1));
    rect.setAttribute('height', item.h.toFixed(1));
    // Transform: translate to item position, then rotate
    const tx = item.x;
    const ty = item.y - item.h; // y is baseline; move up by height
    const deg = item.angle * 180 / Math.PI;
    rect.setAttribute('transform',
      'translate(' + tx.toFixed(1) + ',' + ty.toFixed(1) + ')' +
      (deg !== 0 ? ' rotate(' + deg.toFixed(2) + ')' : '')
    );
    svgEl.appendChild(rect);
  });
}

function _rectHitsItem(rx, ry, rw, rh, item) {
  // Axis-aligned bounding box check for the selection rect vs item.
  // For rotated text we use the item's AABB (good enough for most cases).
  const ix = item.x;
  const iy = item.y - item.h; // top-left y
  const iw = item.w;
  const ih = item.h;

  // For rotated items, compute AABB of all 4 corners
  if (item.angle !== 0) {
    const cos = Math.cos(item.angle), sin = Math.sin(item.angle);
    const corners = [
      [ix, iy], [ix + iw, iy], [ix + iw, iy + ih], [ix, iy + ih]
    ].map(([cx, cy]) => {
      // Rotate around (ix, iy) — the same top-left point the SVG rect is
      // translated to before its rotate() is applied, so the AABB lines up
      // with what's actually drawn (previously pivoted on the baseline
      // item.y, offset from iy by the full item height, which skewed the
      // hit-test box away from the real glyph position on any rotated item).
      const dx = cx - ix, dy = cy - iy;
      return [ix + dx * cos - dy * sin, iy + dx * sin + dy * cos];
    });
    const minX = Math.min(...corners.map(c => c[0]));
    const maxX = Math.max(...corners.map(c => c[0]));
    const minY = Math.min(...corners.map(c => c[1]));
    const maxY = Math.max(...corners.map(c => c[1]));
    return rx < maxX && rx + rw > minX && ry < maxY && ry + rh > minY;
  }

  return rx < ix + iw && rx + rw > ix && ry < iy + ih && ry + rh > iy;
}

function _selClear() {
  // Remove drag rect and highlight SVG from any page overlay
  document.querySelectorAll('.aoverlay [data-sel-svg]').forEach(el => el.remove());
  document.querySelectorAll('.aoverlay .sel-rect').forEach(el => el.remove());
  if (_selState) {
    _selState.rectEl?.remove?.();
    _selState = null;
  }
  _selHits = [];
}

// Wire up select events to page overlays on each render
// Called from attachEvents in renderPageContent
function attachSelectEvents(ov, pageNum) {
  ov.addEventListener('mousedown', ev => {
    if (tool !== 'select') return;
    _selStart(ev, pageNum, ov);
  });
}

// Global mousemove and mouseup for the drag (works even if mouse leaves overlay)
document.addEventListener('mousemove', ev => { if (_selState) _selMove(ev); });
document.addEventListener('mouseup',   ev => { if (_selState) _selEnd(ev); });

// Ctrl+A: select all text on current visible page
document.addEventListener('keydown', ev => {
  if (tool !== 'select') return;
  if (ev.target.closest('input,textarea,select')) return;
  if (!(ev.ctrlKey || ev.metaKey) || ev.key !== 'a') return;
  ev.preventDefault();
  const wrap = document.getElementById('pw-' + curPg);
  const ov   = wrap?.querySelector('.aoverlay');
  if (!ov || !wrap) return;
  _selClear();
  // Fake a full-page selection rect
  const vp = pageViewports[curPg];
  if (!vp) return;
  _selState = { pageNum: curPg, ov,
    svgEl: (() => {
      const s = document.createElementNS('http://www.w3.org/2000/svg','svg');
      s.dataset.selSvg = '1';
      s.style.cssText = 'position:absolute;inset:0;width:100%;height:100%;overflow:visible;pointer-events:none;z-index:5';
      ov.appendChild(s); return s;
    })(),
    rectEl: { remove: () => {}, style: {} },
    x0: 0, y0: 0, x1: vp.width, y1: vp.height,
  };
  _selHighlight(_selState);
  // Sort into reading order before copying
  const _ctrlAOrdered = [..._selHits].sort((a, b) => {
    const avgH = ((a.h || 12) + (b.h || 12)) / 2;
    const lineDiff = (a.y - b.y) / avgH;
    if (Math.abs(lineDiff) > 0.6) return a.y - b.y;
    return a.x - b.x;
  });
  const text = _ctrlAOrdered.map(h => h.str).join(' ').replace(/\s+/g, ' ').trim();
  if (text) {
    navigator.clipboard.writeText(text).catch(() => {});
    toast('Copied all text on page (' + text.length + ' chars)', 2400);
  }
  _selState.rectEl = { remove: () => {} }; // keep SVG, clear state ref
  const svgRef = _selState.svgEl;
  _selState = null;
});

// Clear selection when leaving select mode
function clearTextSelection() {
  _selClear();
  window.getSelection()?.removeAllRanges();
}

// ═══════════════════════════════════════════════
//  MOBILE UI FUNCTIONS
// ═══════════════════════════════════════════════

function toggleMobSidebar() {
  const sidebar  = document.getElementById('sidebar');
  const overlay  = document.getElementById('mob-sidebar-overlay');
  const isOpen   = sidebar.classList.contains('mob-open');
  if (isOpen) {
    sidebar.classList.remove('mob-open');
    overlay.classList.remove('open');
  } else {
    sidebar.classList.add('mob-open');
    overlay.classList.add('open');
    closeMobDrawer();
  }
}

function closeMobSidebar() {
  document.getElementById('sidebar').classList.remove('mob-open');
  document.getElementById('mob-sidebar-overlay').classList.remove('open');
}

let _drawerOpen = false;
function toggleMobDrawer() {
  _drawerOpen = !_drawerOpen;
  const drawer = document.getElementById('mob-tool-drawer');
  const btn    = document.getElementById('mob-btn-tools');
  drawer.classList.toggle('open', _drawerOpen);
  btn.classList.toggle('active', _drawerOpen);
  if (_drawerOpen) closeMobSidebar();
}

function closeMobDrawer() {
  _drawerOpen = false;
  document.getElementById('mob-tool-drawer').classList.remove('open');
  document.getElementById('mob-btn-tools').classList.remove('active');
}

function mobSetTool(t) {
  setTool(t);
  closeMobDrawer();
  // Update bottom bar active state
  document.querySelectorAll('.mob-btn').forEach(b => b.classList.remove('active'));
  const map = { pan:'mob-btn-pan', select:'mob-btn-select' };
  if (map[t]) document.getElementById(map[t])?.classList.add('active');
  else document.getElementById('mob-btn-tools')?.classList.add('active');
  // Update drawer active tool button
  document.querySelectorAll('.mob-tool-btn').forEach(b => b.classList.remove('active'));
  // Find the matching tool button by onclick attr pattern
  document.querySelectorAll('.mob-tool-btn').forEach(b => {
    if (b.getAttribute('onclick')?.includes("'" + t + "'")) b.classList.add('active');
  });
}

async function mobileZoom(factor) {
  if (!pdf) return;
  const newZoom = Math.min(Math.max(zoom * factor, 0.25), 4);
  zoom = newZoom;
  // Update zoom select if present
  const sel = document.getElementById('zsel');
  if (sel) {
    // Try to match a preset
    const pct = Math.round(zoom * 100) / 100;
    let matched = false;
    for (const opt of sel.options) {
      if (parseFloat(opt.value) === pct) { sel.value = opt.value; matched = true; break; }
    }
    if (!matched) sel.value = pct;
  }
  // Update zoom display labels
  const pctStr = Math.round(zoom * 100) + '%';
  const sbZoom = document.getElementById('sb-zoom');
  if (sbZoom) sbZoom.innerHTML = '<div class="sbdot b"></div>' + pctStr;
  const mobLabel = document.getElementById('mob-zoom-label');
  if (mobLabel) mobLabel.textContent = pctStr;
  // Re-render
  await rerenderAll();
}

// Close drawer when switching tool via keyboard
// mob zoom label now synced in _ribbonSetTool patch below

// Pinch-to-zoom on the viewer (touch devices)
(function initPinchZoom() {
  const viewer = document.getElementById('viewer');
  let _pinch = null;

  viewer.addEventListener('touchstart', ev => {
    if (ev.touches.length === 2) {
      ev.preventDefault();
      const dx = ev.touches[0].clientX - ev.touches[1].clientX;
      const dy = ev.touches[0].clientY - ev.touches[1].clientY;
      _pinch = { dist: Math.hypot(dx, dy), zoom };
    }
  }, { passive: false });

  viewer.addEventListener('touchmove', ev => {
    if (ev.touches.length === 2 && _pinch) {
      ev.preventDefault();
      const dx = ev.touches[0].clientX - ev.touches[1].clientX;
      const dy = ev.touches[0].clientY - ev.touches[1].clientY;
      const newDist = Math.hypot(dx, dy);
      const scale   = newDist / _pinch.dist;
      zoom = Math.min(Math.max(_pinch.zoom * scale, 0.25), 4);
      // Live-update zoom label without re-rendering every frame
      const pct = Math.round(zoom * 100) + '%';
      const lbl = document.getElementById('mob-zoom-label');
      if (lbl) lbl.textContent = pct;
      const sbZ = document.getElementById('sb-zoom');
      if (sbZ) sbZ.innerHTML = '<div class="sbdot b"></div>' + pct;
    }
  }, { passive: false });

  viewer.addEventListener('touchend', ev => {
    if (_pinch && ev.touches.length < 2) {
      // Commit the zoom on finger lift
      _pinch = null;
      rerenderAll();
    }
  }, { passive: true });
})();

// ═══════════════════════════════════════════════
//  CHECK MODAL TAB SWITCHER
// ═══════════════════════════════════════════════
function switchCheckTab(tab) {
  const isStandards = tab === 'standards';
  document.getElementById('check-panel-standards').style.display = isStandards ? '' : 'none';
  document.getElementById('check-panel-spelling').style.display  = isStandards ? 'none' : '';
  document.getElementById('check-add-btn').style.display  = isStandards ? (checkFindings.some(f=>f.status==='fail'||f.status==='warn') ? '' : 'none') : 'none';
  document.getElementById('spell-add-btn').style.display  = isStandards ? 'none' : (_spellSuggestions.length ? '' : 'none');

  const ts = document.getElementById('check-tab-standards');
  const tg = document.getElementById('check-tab-spelling');
  ts.style.background = isStandards ? 'var(--white)' : 'transparent';
  ts.style.borderBottomColor = isStandards ? 'var(--blue-500)' : 'transparent';
  ts.style.Color = isStandards ? 'var(--blue-600)' : 'var(--gray-500)';
  tg.style.background = isStandards ? 'transparent' : 'var(--white)';
  tg.style.borderBottomColor = isStandards ? 'transparent' : 'var(--blue-500)';
  tg.style.Color = isStandards ? 'var(--gray-500)' : 'var(--blue-600)';
}

// ═══════════════════════════════════════════════
//  AI SPELLING & GRAMMAR CHECK
//  Uses Claude API to analyse all drawing text,
//  returns structured suggestions you can add as
//  annotations with one click.
// ═══════════════════════════════════════════════
// ── British English dictionaries (client-side, no API needed) ──
const AMERICAN_TO_BRITISH = {
  // -ize → -ise
  'organize':'organise','organize':'organise','organized':'organised','organizing':'organising',
  'recognize':'recognise','recognized':'recognised','recognizing':'recognising',
  'authorize':'authorise','authorized':'authorised','authorizing':'authorising',
  'prioritize':'prioritise','prioritized':'prioritised','prioritizing':'prioritising',
  'utilize':'utilise','utilized':'utilised','utilizing':'utilising',
  'realize':'realise','realized':'realised','realizing':'realising',
  'minimize':'minimise','minimized':'minimised','maximize':'maximise','maximized':'maximised',
  'analyze':'analyse','analyzed':'analysed','analyzing':'analysing',
  'standardize':'standardise','standardized':'standardised',
  'finalize':'finalise','finalized':'finalised','finalizing':'finalising',
  'specialize':'specialise','specialized':'specialised',
  'characterize':'characterise','characterised':'characterised',
  // -or → -our
  'Color':'Color','Colors':'Colors','Colored':'Colored',
  'labor':'labour','labors':'labours',
  'harbor':'harbour','harbors':'harbours',
  'flavor':'flavour','flavors':'flavours',
  'honor':'honour','honors':'honours','honored':'honoured',
  'behavior':'behaviour','behaviors':'behaviours',
  'neighbor':'neighbour','neighbors':'neighbours',
  // -er → -re
  'center':'centre','centers':'centres','centered':'centred',
  'meter':'metre','meters':'metres',
  'fiber':'fibre','fibers':'fibres',
  'theater':'theatre','theaters':'theatres',
  'liter':'litre','liters':'litres',
  // -ense → -ence / misc
  'defense':'defence','offense':'offence','license':'licence',
  'program':'programme','programs':'programmes',
  'aluminum':'aluminium',
  'tire':'tyre','tires':'tyres',
  'gray':'grey','grays':'greys',
  'ax':'axe','draft':'draught','pajamas':'pyjamas',
  'practice':'practise',
  'catalog':'catalogue','analog':'analogue','dialog':'dialogue',
  'check':'cheque',
  'connection':'connexion',
};

const COMMON_MISSPELLINGS = {
  // Common engineering/drawing misspellings
  'accomodation':'accommodation','accomodations':'accommodations',
  'accomodate':'accommodate','accomodated':'accommodated',
  'accessable':'accessible','accessiblity':'accessibility',
  'adress':'address','adresses':'addresses',
  'agrement':'agreement','agrements':'agreements',
  'apparant':'apparent','apparantly':'apparently',
  'approximatly':'approximately','aproximate':'approximate',
  'assesment':'assessment','assesments':'assessments',
  'calulate':'calculate','calulation':'calculation',
  'catagory':'category','catagories':'categories',
  'clearence':'clearance','clearences':'clearances',
  'comission':'commission','commision':'commission',
  'compatable':'compatible','compatability':'compatibility',
  'completly':'completely','compleed':'completed',
  'conrete':'concrete','constuction':'construction',
  'critial':'critical','critcal':'critical',
  'defenitely':'definitely','definately':'definitely',
  'dependant':'dependent',
  'developement':'development','devlopment':'development',
  'dimention':'dimension','dimentions':'dimensions',
  'dissapear':'disappear','dissapeared':'disappeared',
  'drainege':'drainage',
  'eletrical':'electrical','electic':'electric',
  'enviroment':'environment','enviromental':'environmental',
  'exsiting':'existing','exisiting':'existing',
  'expantion':'expansion',
  'feild':'field',
  'founation':'foundation','foundaton':'foundation',
  'fourm':'forum',
  'goverment':'government',
  'guarentee':'guarantee','guarenteed':'guaranteed',
  'hieght':'height','higth':'height',
  'horizonal':'horizontal','horizantal':'horizontal',
  'imapct':'impact',
  'implmentation':'implementation',
  'inculde':'include','inlcude':'include',
  'infomation':'information',
  'insallation':'installation','installtion':'installation',
  'integeration':'integration',
  'lenght':'length','lentgh':'length',
  'maintenace':'maintenance','maintanance':'maintenance','maintainance':'maintenance',
  'managment':'management',
  'measurment':'measurement','measurments':'measurements',
  'minumum':'minimum','maxiumum':'maximum',
  'neccessary':'necessary','necesary':'necessary',
  'occured':'occurred','occurance':'occurrence',
  'opertion':'operation','opeartion':'operation',
  'overide':'override',
  'paremeter':'parameter','paramater':'parameter','perameter':'parameter',
  'performace':'performance','perfomance':'performance',
  'perpendicular':'perpendicular',
  'postion':'position','positon':'position',
  'practial':'practical',
  'prefered':'preferred',
  'proceedure':'procedure','procedue':'procedure',
  'procured':'procured',
  'propsed':'proposed',
  'provison':'provision','provisons':'provisions',
  'rasius':'radius',
  'recieve':'receive','recieved':'received',
  'refrence':'reference','refrences':'references',
  'reguirement':'requirement','requirment':'requirement','requirments':'requirements',
  'removeal':'removal',
  'renforced':'reinforced','reinforced':'reinforced',
  'repacement':'replacement',
  'responsibilty':'responsibility',
  'retaning':'retaining','retaing':'retaining',
  'revison':'revision','revisons':'revisions',
  'seperare':'separate','seperator':'separator','seperate':'separate',
  'settelment':'settlement','setlement':'settlement',
  'siganl':'signal','signaling':'signalling',
  'simalar':'similar','similiar':'similar',
  'specificaton':'specification','specifiaction':'specification',
  'stucture':'structure','strcuture':'structure',
  'substatial':'substantial',
  'suficient':'sufficient','sufficent':'sufficient',
  'superceed':'supersede','superced':'supersede',
  'surounding':'surrounding','surrouding':'surrounding',
  'temperory':'temporary','tempory':'temporary',
  'thier':'their',
  'treshold':'threshold','threshhold':'threshold',
  'transfered':'transferred',
  'tunnell':'tunnel',
  'unkown':'unknown',
  'utilites':'utilities',
  'vetical':'vertical','verticle':'vertical',
  'verical':'vertical',
  'visabilty':'visibility','visibily':'visibility',
  'wieght':'weight',
  'wiggly':'wiggly',
};

let _spellSuggestions = []; // [{original, corrected, type, pageNum, x, y}]

async function runSpellCheck() {
  if (!pdf) { toast('Open a PDF first'); return; }

  // Show progress
  document.getElementById('spell-idle').style.display    = 'none';
  document.getElementById('spell-results').style.display = 'none';
  document.getElementById('spell-running').style.display = 'block';
  document.getElementById('spell-add-btn').style.display = 'none';
  _spellSuggestions = [];

  const progEl   = document.getElementById('spell-progress');
  const statusEl = document.getElementById('spell-status');
  progEl.style.width = '10%';

  // ── Collect all text from the drawing ──
  statusEl.textContent = 'Extracting text from drawing…';
  const textByPage = {};
  const pagesToScan = Math.min(nPages, 10); // limit to 10 pages to keep API call fast
  for (let pg = 1; pg <= pagesToScan; pg++) {
    if (!pdfTextContent[pg]) {
      try {
        const page = await pdf.getPage(pg);
        const tc   = await page.getTextContent();
        const vp   = page.getViewport({ scale: 1 });
        pdfTextContent[pg] = tc.items.filter(i => i.str?.trim()).map(i => {
          const [,,,scaleY,tx,ty] = i.transform;
          return { str: i.str.trim(), x: tx/vp.width, y: 1-(ty/vp.height),
            fontSize: Math.abs(scaleY)/vp.height, width: i.width/vp.width };
        });
      } catch(e) { pdfTextContent[pg] = []; }
    }
    textByPage[pg] = (pdfTextContent[pg] || []).map(t => t.str).filter(s => s.length > 2);
  }

  // Build text corpus — join page text, skip very short or numeric-only strings
  const corpus = Object.entries(textByPage).map(([pg, lines]) => {
    const meaningful = lines.filter(s => /[a-zA-Z]{2,}/.test(s));
    if (!meaningful.length) return null;
    return `Page ${pg}:\n${meaningful.join('\n')}`;
  }).filter(Boolean).join('\n\n');

  if (!corpus.trim()) {
    document.getElementById('spell-running').style.display = 'none';
    document.getElementById('spell-idle').style.display    = 'block';
    document.getElementById('spell-idle').innerHTML =
      '<div style="padding:28px;text-align:center;Color:var(--gray-500);font-size:13px">' +
      'No readable text found in this drawing.</div>';
    return;
  }

  progEl.style.width = '35%';
  statusEl.textContent = 'Sending to AI for analysis…';

  // ── Client-side British English spell check (no API required) ──
  progEl.style.width = '60%';
  statusEl.textContent = 'Checking spelling…';
  await new Promise(r => setTimeout(r, 30));

  const findings = [];

  Object.entries(textByPage).forEach(([pgStr, lines]) => {
    const pg = parseInt(pgStr);
    lines.forEach(line => {
      const words = line.split(/[\s\-\/\\,;:()\.\[\]{}]+/);
      words.forEach(rawWord => {
        const word = rawWord.replace(/^[^a-zA-Z]+|[^a-zA-Z]+$/g, '');
        if (word.length < 3) return;
        if (/^[A-Z0-9]+$/.test(word)) return;
        if (/^\d/.test(word)) return;

        const lower = word.toLowerCase();
        const british = AMERICAN_TO_BRITISH[lower];
        if (british) {
          const items = pdfTextContent[pg] || [];
          const match = items.find(t => t.str.toLowerCase().includes(lower));
          findings.push({ id: 'spell-' + findings.length, original: word, corrected: british,
            type: 'spelling', reason: 'American spelling — British English uses "' + british + '"',
            pageNum: pg, x: match ? match.x * 100 : 5, y: match ? match.y * 100 : 5 + findings.length * 4, added: false });
          return;
        }
        const correction = COMMON_MISSPELLINGS[lower];
        if (correction) {
          const items = pdfTextContent[pg] || [];
          const match = items.find(t => t.str.toLowerCase().includes(lower));
          findings.push({ id: 'spell-' + findings.length, original: word, corrected: correction,
            type: 'spelling', reason: 'Possible misspelling',
            pageNum: pg, x: match ? match.x * 100 : 5, y: match ? match.y * 100 : 5 + findings.length * 4, added: false });
        }
      });

      const doubleWord = line.match(/\b(\w{2,})\s+\1\b/i);
      if (doubleWord) {
        findings.push({ id: 'spell-' + findings.length, original: doubleWord[0], corrected: doubleWord[1],
          type: 'grammar', reason: 'Repeated word', pageNum: parseInt(pgStr), x: 5, y: 5 + findings.length * 3, added: false });
      }
    });
  });

  const seen = new Set();
  _spellSuggestions = findings.filter(f => {
    const key = f.original.toLowerCase() + '|' + f.pageNum;
    if (seen.has(key)) return false;
    seen.add(key); return true;
  });
  progEl.style.width = '100%';
  document.getElementById('spell-running').style.display = 'none';
  renderSpellResults();
}

function renderSpellResults() {
  const container = document.getElementById('spell-results');
  const summary   = document.getElementById('check-summary');

  if (!_spellSuggestions.length) {
    container.innerHTML =
      '<div style="padding:32px;text-align:center">' +
      '<div style="font-size:28px;margin-bottom:10px">✓</div>' +
      '<div style="font-size:13px;font-weight:600;Color:var(--gray-700)">No issues found</div>' +
      '<div style="font-size:12px;Color:var(--gray-500);margin-top:4px">Spelling and grammar look good.</div>' +
      '</div>';
    container.style.display = '';
    summary.textContent = 'No issues found';
    return;
  }

  const typeIcon  = { spelling:'Sp', grammar:'Gr', punctuation:'Pu' };
  const typeColor = { spelling:'var(--red-500)', grammar:'#d97706', punctuation:'var(--blue-500)' };

  let html = '';
  _spellSuggestions.forEach((s, i) => {
    const icon  = typeIcon[s.type]  || 'Sp';
    const Color = typeColor[s.type] || 'var(--red-500)';
    html +=
      '<div id="spell-item-' + i + '" style="display:flex;align-items:flex-start;gap:10px;padding:10px 14px;border-bottom:1px solid var(--gray-100);' + (s.added ? 'opacity:.45;' : '') + '">' +
        '<span style="flex-shrink:0;width:24px;height:24px;border-radius:4px;background:' + Color + ';Color:#fff;font-size:9px;font-weight:700;display:flex;align-items:center;justify-content:center;font-family:var(--mono)">' + icon + '</span>' +
        '<div style="flex:1;min-width:0">' +
          '<div style="font-size:12px;font-weight:600;Color:var(--gray-700);margin-bottom:2px">' +
            '<span style="text-decoration:line-through;Color:var(--red-500)">' + escHtml(s.original) + '</span>' +
            ' → <span style="Color:var(--gray-900)">' + escHtml(s.corrected) + '</span>' +
          '</div>' +
          '<div style="font-size:11px;Color:var(--gray-500)">' + escHtml(s.reason) + ' · Pg ' + s.pageNum + '</div>' +
        '</div>' +
        '<button onclick="addSpellSuggestion(' + i + ')" id="spell-btn-' + i + '" ' +
          'style="flex-shrink:0;padding:4px 10px;font-size:11px;border:1px solid var(--gray-300);border-radius:4px;background:var(--white);cursor:pointer;font-family:var(--font);white-space:nowrap" ' +
          (s.added ? 'disabled' : '') + '>' +
          (s.added ? '✓ Added' : 'Add Comment') +
        '</button>' +
      '</div>';
  });

  container.innerHTML = html;
  container.style.display = '';
  summary.textContent = _spellSuggestions.length + ' issue' + (_spellSuggestions.length !== 1 ? 's' : '') + ' found';
  document.getElementById('spell-add-btn').style.display = '';
}

function escHtml(s) {
  return String(s||'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
}

function addSpellSuggestion(idx) {
  const s = _spellSuggestions[idx];
  if (!s || s.added) return;
  pushAnnot({
    id: nextId(), pageNum: s.pageNum, type: 'text',
    x: s.x, y: s.y, Color: 'red',
    text: '[' + (s.type.charAt(0).toUpperCase() + s.type.slice(1)) + '] ' +
          '"' + s.original + '" → "' + s.corrected + '"\n' + s.reason,
    textAlign: 'center', vAlign: 'center', box: true,
  });
  s.added = true;
  // Update button and row
  const btn = document.getElementById('spell-btn-' + idx);
  const row = document.getElementById('spell-item-' + idx);
  if (btn) { btn.textContent = '✓ Added'; btn.disabled = true; }
  if (row)   row.style.opacity = '0.45';
  toast('Comment added on page ' + s.pageNum);
}

function addAllSpellSuggestions() {
  let count = 0;
  _spellSuggestions.forEach((s, i) => {
    if (!s.added) { addSpellSuggestion(i); count++; }
  });
  document.getElementById('spell-add-btn').style.display = 'none';
  toast(count + ' spelling/grammar comment' + (count !== 1 ? 's' : '') + ' added');
}
document.addEventListener('keydown', ev => {
  if (ev.target.closest('input,textarea,select')) return;
  if (ev.key === 'z' && !ev.ctrlKey && !ev.metaKey) setTool('zoombox');
  if (ev.key === 'Escape') {
    _mqStart = null;
    document.getElementById('zoom-marquee').style.display = 'none';
    if (tool === 'select' || tool === 'zoombox') {
      clearTextSelection();
      setTool('pan');
    }
  }
});

// ═══════════════════════════════════════════════
//  STAMPS
//  Pre-built approval/review stamps rendered as
//  styled SVG overlays on the page.
// ═══════════════════════════════════════════════
const STAMPS = [
  { id:'approved',    label:'Approved',         Color:'#16a34a', textColor:'#fff', icon:'✓' },
  { id:'for-constr',  label:'For Construction', Color:'#2563eb', textColor:'#fff', icon:'⚙' },
  { id:'ifc',         label:'Issued for Comment',Color:'#7c3aed', textColor:'#fff', icon:'✎' },
  { id:'checked',     label:'Checked',          Color:'#0891b2', textColor:'#fff', icon:'✔' },
  { id:'superseded',  label:'Superseded',       Color:'#dc2626', textColor:'#fff', icon:'✕' },
  { id:'preliminary', label:'Preliminary',      Color:'#d97706', textColor:'#fff', icon:'~' },
  { id:'draft',       label:'Draft',            Color:'#6b7280', textColor:'#fff', icon:'D' },
  { id:'void',        label:'Void',             Color:'#991b1b', textColor:'#fff', icon:'∅' },
  { id:'returned',    label:'Returned',         Color:'#c2410c', textColor:'#fff', icon:'↩' },
];

let _pendingStamp = null;

function openStampPicker() {
  const grid = document.getElementById('stamp-grid');
  grid.innerHTML = '';
  STAMPS.forEach(s => {
    const div = document.createElement('div');
    div.className = 'stamp-opt';
    div.innerHTML =
      '<svg width="60" height="28" viewBox="0 0 60 28">' +
      '<rect x="1" y="1" width="58" height="26" rx="4" fill="' + s.Color + '" opacity=".15" stroke="' + s.Color + '" stroke-width="1.5"/>' +
      '<text x="30" y="17" text-anchor="middle" font-size="9" font-weight="700" font-family="monospace" fill="' + s.Color + '">' + s.label.toUpperCase() + '</text>' +
      '</svg>' +
      '<div class="stamp-opt-label">' + s.label + '</div>';
    div.onclick = () => { _pendingStamp = s; closeM('mstamp'); activateStampPlacement(); };
    grid.appendChild(div);
  });
  openM('mstamp');
}

function activateStampPlacement() {
  const stamp = _pendingStamp;
  toast('Click to place the "' + stamp.label + '" stamp · Esc to cancel', 3500);

  // Build a ghost stamp that follows the cursor
  let _ghostStamp = null;
  let _ghostOv    = null;

  function buildGhostStamp() {
    const g = document.createElement('div');
    g.id = 'stamp-ghost';
    g.style.cssText =
      'position:absolute;pointer-events:none;z-index:200;opacity:0.65;' +
      'transform:translate(-50%,-50%);transition:none;';
    const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    svg.setAttribute('width','110'); svg.setAttribute('height','36');
    svg.setAttribute('viewBox','0 0 110 36');
    const rect = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
    rect.setAttribute('x','1'); rect.setAttribute('y','1');
    rect.setAttribute('width','108'); rect.setAttribute('height','34');
    rect.setAttribute('rx','4');
    rect.setAttribute('fill', stamp.Color);
    rect.setAttribute('fill-opacity','0.15');
    rect.setAttribute('stroke', stamp.Color);
    rect.setAttribute('stroke-width','2');
    rect.setAttribute('stroke-dasharray','5,3');
    const text = document.createElementNS('http://www.w3.org/2000/svg', 'text');
    text.setAttribute('x','55'); text.setAttribute('y','23');
    text.setAttribute('text-anchor','middle');
    text.setAttribute('font-size','11'); text.setAttribute('font-weight','700');
    text.setAttribute('font-family','monospace');
    text.setAttribute('fill', stamp.Color);
    text.textContent = stamp.label.toUpperCase();
    svg.appendChild(rect); svg.appendChild(text);
    g.appendChild(svg);
    return g;
  }

  function removeGhostStamp() {
    const g = document.getElementById('stamp-ghost');
    if (g) g.remove();
    _ghostStamp = null; _ghostOv = null;
  }

  function onMouseMove(ev) {
    if (!_pendingStamp) { removeGhostStamp(); return; }
    const ov = ev.target.closest('.aoverlay');
    if (!ov) { removeGhostStamp(); return; }

    // Move ghost to a different overlay if needed
    if (_ghostOv !== ov) {
      removeGhostStamp();
      _ghostStamp = buildGhostStamp();
      _ghostOv = ov;
      ov.appendChild(_ghostStamp);
    }

    const r = ov.getBoundingClientRect();
    const xPct = (ev.clientX - r.left) / ov.offsetWidth  * 100;
    const yPct = (ev.clientY - r.top)  / ov.offsetHeight * 100;
    _ghostStamp.style.left = xPct + '%';
    _ghostStamp.style.top  = yPct + '%';
  }

  // Click to commit
  const onClick = ev => {
    if (!_pendingStamp) return;
    ev.stopPropagation();
    ev.preventDefault();
    const ov = ev.currentTarget;
    const pn = parseInt(ov.dataset.page);
    const r  = ov.getBoundingClientRect();
    const x  = (ev.clientX - r.left) / ov.offsetWidth  * 100;
    const y  = (ev.clientY - r.top)  / ov.offsetHeight * 100;
    cleanup();
    pushAnnot({ id: nextId(), pageNum: pn, type: 'stamp',
      stampId: stamp.id, x, y, Color: stamp.Color,
      textColor: stamp.textColor, label: stamp.label });
  };

  function cleanup() {
    _pendingStamp = null;
    removeGhostStamp();
    document.removeEventListener('mousemove', onMouseMove, true);
    document.querySelectorAll('.aoverlay').forEach(o => {
      o.removeEventListener('click', onClick, true);
      o.style.cursor = '';
    });
    document.removeEventListener('keydown', onEsc);
  }

  const onEsc = ev => { if (ev.key === 'Escape') cleanup(); };

  // Set crosshair on all overlays and attach listeners
  document.querySelectorAll('.aoverlay').forEach(o => {
    o.style.cursor = 'crosshair';
    o.addEventListener('click', onClick, true);
  });
  document.addEventListener('mousemove', onMouseMove, true);
  document.addEventListener('keydown', onEsc);
}

function buildStampEl(a) {
  const stamp = STAMPS.find(s => s.id === a.stampId) || STAMPS[0];
  const wrap = document.createElement('div');
  wrap.className = 'astamp';
  wrap.style.cssText = 'position:absolute;left:' + a.x + '%;top:' + a.y + '%';
  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svg.setAttribute('width', '110'); svg.setAttribute('height', '36');
  svg.setAttribute('viewBox', '0 0 110 36');
  const rect = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
  rect.setAttribute('x','1'); rect.setAttribute('y','1');
  rect.setAttribute('width','108'); rect.setAttribute('height','34');
  rect.setAttribute('rx','4'); rect.setAttribute('fill', a.Color || stamp.Color);
  rect.setAttribute('fill-opacity','0.12');
  rect.setAttribute('stroke', a.Color || stamp.Color); rect.setAttribute('stroke-width','2');
  const text = document.createElementNS('http://www.w3.org/2000/svg', 'text');
  text.setAttribute('x','55'); text.setAttribute('y','23');
  text.setAttribute('text-anchor','middle');
  text.setAttribute('font-size','11'); text.setAttribute('font-weight','700');
  text.setAttribute('font-family','monospace'); text.setAttribute('fill', a.Color || stamp.Color);
  text.textContent = (a.label || stamp.label).toUpperCase();
  svg.appendChild(rect); svg.appendChild(text);
  wrap.appendChild(svg);
  return wrap;
}

// Add stamp to buildAnnotEl
typeLabels['stamp'] = 'Stamp';
typeLabels['image'] = 'Image';

// ═══════════════════════════════════════════════
//  ANNOTATION STATUS TRACKING
//  STATUS_CYCLE and STATUS_LABEL defined at top of state block.
// ═══════════════════════════════════════════════

function cycleAnnotStatus(id, ev) {
  if (ev) ev.stopPropagation();
  const a = annots.find(x => x.id === id);
  if (!a) return;
  const cur = a.status || 'open';
  const next = STATUS_CYCLE[(STATUS_CYCLE.indexOf(cur) + 1) % STATUS_CYCLE.length];
  a.status = next;
  syncAnnots(); updateAnnotPanel(); updateEmmaRegister(); pushHistory();
  toast('Status → ' + STATUS_LABEL[next]);
}

// Status tracking is integrated directly into updateAnnotPanel above

// Status badge is now rendered directly in buildAnnotEl

// ═══════════════════════════════════════════════
//  ANNOTATION KEYBOARD NAVIGATION
//  Tab / Shift+Tab cycles through annotations.
//  The view scrolls to each one and highlights it.
// ═══════════════════════════════════════════════
let _annotNavIdx = -1;

function updateAnnotNavBar() {
  const label = document.getElementById('ann-nav-label');
  const prev  = document.getElementById('ann-nav-prev');
  const next  = document.getElementById('ann-nav-next');
  if (!label) return;
  const n = annots.length;
  label.textContent = n === 0 ? 'No annotations' : (_annotNavIdx >= 0 ? (_annotNavIdx + 1) + ' / ' + n : n + ' annotation' + (n !== 1 ? 's' : ''));
  if (prev) prev.disabled = n === 0;
  if (next) next.disabled = n === 0;
}

function navAnnot(dir) {
  if (!annots.length) return;
  _annotNavIdx = (_annotNavIdx + dir + annots.length) % annots.length;
  const a = annots[_annotNavIdx];
  updateAnnotNavBar();
  scrollToAnnotation(a);
}

// Tab / Shift+Tab shortcut in markup panel
document.addEventListener('keydown', ev => {
  if (ev.target.closest('input,textarea,select')) return;
  const inMarkup = document.getElementById('stab-notes')?.classList.contains('active');
  if (!inMarkup) return;
  if (ev.key === 'Tab') {
    ev.preventDefault();
    navAnnot(ev.shiftKey ? -1 : 1);
  }
});

// ═══════════════════════════════════════════════
//  MEASUREMENT TABLE
//  Lists all measure and area annotations with
//  their values. Exportable to CSV.
// ═══════════════════════════════════════════════
function updateMeasurementTable() {
  const wrap = document.getElementById('meas-table-wrap');
  if (!wrap) return;
  const measAnnots = annots.filter(a => a.type === 'measure' || a.type === 'area');
  if (!measAnnots.length) {
    wrap.innerHTML = '<div class="meas-empty">No measurements yet.<br>Use the Distance or Area tools.</div>';
    return;
  }
  let html = '<table class="meas-table"><thead><tr><th>Type</th><th>Value</th><th>Page</th><th>Scale</th></tr></thead><tbody>';
  measAnnots.forEach(a => {
    const type  = a.type === 'area' ? 'Area' : 'Distance';
    const value = a.label || (a.type === 'area' ? '—' : Math.round(a.pxDist || 0) + ' px');
    const scale = a.unit && a.unit !== 'px' ? '1:set (' + a.unit + ')' : 'uncalibrated';
    html += '<tr><td>' + type + '</td><td style="font-weight:600">' + value + '</td><td>' + a.pageNum + '</td><td>' + scale + '</td></tr>';
  });
  html += '</tbody></table>';
  wrap.innerHTML = html;
}

function exportMeasurementsCsv() {
  const measAnnots = annots.filter(a => a.type === 'measure' || a.type === 'area');
  if (!measAnnots.length) { toast('No measurements to export'); return; }
  const rows = [['Type','Value','Page','Scale','Author']];
  measAnnots.forEach(a => {
    rows.push([
      a.type === 'area' ? 'Area' : 'Distance',
      a.label || (Math.round(a.pxDist || 0) + ' px'),
      a.pageNum,
      a.unit && a.unit !== 'px' ? '1:set (' + a.unit + ')' : 'uncalibrated',
      a.author || '',
    ]);
  });
  const csv = rows.map(r => r.map(v => '"' + String(v).replace(/"/g, '""') + '"').join(',')).join('\n');
  const blob = new Blob([csv], { type: 'text/csv' });
  const url  = URL.createObjectURL(blob);
  const a = document.createElement('a'); a.href = url; a.download = (pdfName || 'measurements').replace(/\.pdf$/i,'') + '_measurements.csv';
  a.click(); URL.revokeObjectURL(url);
  toast('Measurements exported to CSV');
}



// ═══════════════════════════════════════════════
//  PDF LAYER VISIBILITY
//  Reads Optional Content Groups from pdf.js and
//  provides toggle checkboxes.
// ═══════════════════════════════════════════════
let _pdfLayers = []; // [{ name, id, visible }]

async function loadPdfLayers() {
  _pdfLayers = [];
  if (!pdf) return;
  const myGen = docGen; // bail if the user switches tabs before this finishes
  try {
    const optContent = await pdf.getOptionalContentConfig();
    if (myGen !== docGen) return;
    if (!optContent) return;
    const groups = optContent.getGroups?.() || {};
    Object.entries(groups).forEach(([id, group]) => {
      _pdfLayers.push({ id, name: group.name || id, visible: group.visible !== false });
    });
  } catch(e) { /* PDF may not have layers */ }
}

function updateLayerPanel() {
  const list = document.getElementById('layer-modal-list') || document.getElementById('layer-list');
  if (!list) return;
  if (!_pdfLayers.length) {
    list.innerHTML = '<div class="meas-empty">No layers found in this PDF.<br>Layers require Optional Content Groups.</div>';
    return;
  }
  list.innerHTML = '';
  _pdfLayers.forEach(layer => {
    const item = document.createElement('div');
    item.className = 'layer-item' + (layer.visible ? '' : ' hidden-layer');
    const cb = document.createElement('input');
    cb.type = 'checkbox'; cb.checked = layer.visible;
    cb.onchange = async () => {
      layer.visible = cb.checked;
      item.classList.toggle('hidden-layer', !cb.checked);
      await applyLayerVisibility();
    };
    const lbl = document.createElement('span');
    lbl.textContent = layer.name;
    item.appendChild(cb); item.appendChild(lbl);
    list.appendChild(item);
  });
}

async function applyLayerVisibility() {
  if (!pdf || !_pdfLayers.length) return;
  try {
    const optContent = await pdf.getOptionalContentConfig();
    _pdfLayers.forEach(layer => optContent.setVisibility(layer.id, layer.visible));
    renderedPages.clear();
    Object.keys(_pageCache).forEach(k => delete _pageCache[k]);
    scheduleRender();
    toast('Layer visibility updated');
  } catch(e) { toast('Layer toggle not supported for this PDF'); }
}

function openLayerModal() {
  // Build a lightweight floating modal for layer visibility
  const existing = document.getElementById('mlayers');
  if (existing) { existing.classList.toggle('open'); return; }

  const overlay = document.createElement('div');
  overlay.className = 'overlay'; overlay.id = 'mlayers';
  overlay.innerHTML =
    '<div class="modal" style="width:320px">' +
      '<div class="mhead">' +
        '<span class="mtitle">PDF Layers</span>' +
        '<button class="mclose" onclick="document.getElementById(\'mlayers\').classList.remove(\'open\')">✕</button>' +
      '</div>' +
      '<div class="mbody" style="padding:8px 0;max-height:320px;overflow-y:auto">' +
        '<div id="layer-modal-list"></div>' +
      '</div>' +
      '<div class="mfoot">' +
        '<button class="hbtn outline" onclick="document.getElementById(\'mlayers\').classList.remove(\'open\')">Close</button>' +
      '</div>' +
    '</div>';
  document.body.appendChild(overlay);
  overlay.classList.add('open');
  overlay.addEventListener('click', e => { if (e.target === overlay) overlay.classList.remove('open'); });
  updateLayerPanel();
}

// Single loadPDF post-hook — file handle reset, 3D check, layer load
const _origLoadPDFBase = loadPDF;
loadPDF = async function(file) {
  // Reset save handle (new file = new save location)
  _fileHandle = null;
  _loadedEngdocName = null;
  // Clear 3D banner from previous file
  document.getElementById('banner-3d')?.remove();
  await _origLoadPDFBase(file);
  // Post-load: check 3D content and load PDF layers
  if (pdf) check3DContent(pdf);
  await loadPdfLayers();
  updateLayerPanel();
};

// ═══════════════════════════════════════════════
//  BATCH EMMA EXPORT
//  Exports all drawings in the Drawing Set
//  register to a single consolidated EMMA register.
// ═══════════════════════════════════════════════
async function batchExportEmma() {
  if (!drawingSet.length) {
    toast('Add drawings to the Drawing Set Register first (Review tab)', 4000); return;
  }
  if (!emmaTemplateBuf) {
    toast('⚠ Load your EMMA Checksheet template first', 4000); return;
  }

  toast('Building consolidated EMMA register…');
  await loadJSZip();
  const { PDFDocument } = await (window.PDFLib ? Promise.resolve(window) : loadPdfLib().then(() => window));

  // We build one workbook per drawing then combine rows
  // Reuse exportEmma logic but collect all annotations across drawing set
  const allRows = [];
  drawingSet.forEach(drawing => {
    const drawingAnnots = (drawing.annots || []).filter(a =>
      ['text','measure'].includes(a.type) && !a.emmaExclude
    );
    drawingAnnots.forEach(a => {
      allRows.push({
        docNo:  drawing.name.replace(/\.pdf$/i,''),
        text:   a.text || a.label || '',
        author: a.author || '',
        status: a.status || 'open',
        priority: a.priority || '',
        pageNum: a.pageNum,
        type:   a.type,
      });
    });
  });

  // Also include current open drawing
  const curAnnots = annots.filter(a =>
    ['text','measure'].includes(a.type) && !a.emmaExclude
  );
  curAnnots.forEach(a => {
    allRows.push({
      docNo:   pdfName ? pdfName.replace(/\.pdf$/i,'') : 'Current',
      text:    a.text || a.label || '',
      author:  a.author || '',
      status:  a.status || 'open',
      priority: a.priority || '',
      pageNum: a.pageNum,
      type:    a.type,
    });
  });

  if (!allRows.length) { toast('No EMMA comments found across drawing set'); return; }

  try {
    const zip = await JSZip.loadAsync(emmaTemplateBuf);

    // Get sheet paths
    const wbXml  = await zip.file('xl/workbook.xml').async('string');
    const relXml = await zip.file('xl/_rels/workbook.xml.rels').async('string');
    const getPath = name => {
      const esc = s => s.replace(/[.*+?^${}()|[\]\\]/g,'\\$&');
      const m = wbXml.match(new RegExp('sheet[^>]+name="'+esc(name)+'"[^>]+r:id="([^"]+)"')) ||
                wbXml.match(new RegExp('sheet[^>]+r:id="([^"]+)"[^>]+name="'+esc(name)+'"'));
      if (!m) return null;
      const rm = relXml.match(new RegExp('Id="'+m[1]+'"[^>]+Target="([^"]+)"'));
      if (!rm) return null;
      return 'xl/' + rm[1].replace(/^\/?xl\//,'');
    };

    let ssXml = await zip.file('xl/sharedStrings.xml').async('string');
    const ssEntries = [...ssXml.matchAll(/<si>[\s\S]*?<\/si>/g)].map(m => {
      return [...m[0].matchAll(/<t[^>]*>([^<]*)<\/t>/g)].map(x=>x[1]).join('');
    });
    const ssIndex = str => {
      const s = String(str);
      const i = ssEntries.indexOf(s);
      if (i !== -1) return i;
      ssEntries.push(s);
      const esc = s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
      ssXml = ssXml.replace('</sst>', '<si><t>' + esc + '</t></si></sst>');
      return ssEntries.length - 1;
    };
    const writeCell = (xml, ref, idx) => {
      const re = new RegExp('(<c\\s+r="'+ref+'"(?:\\s+[^>]*)?)(?:\\s*/>|>[\\s\\S]*?</c>)', 'i');
      const rep = (_, open) => open.replace(/\s+t="[^"]*"/,'') + ' t="s"><v>' + idx + '</v></c>';
      if (re.test(xml)) return xml.replace(re, rep);
      const row = ref.match(/\d+$/)[0];
      return xml.replace(new RegExp('(<row\\b[^>]*\\br="'+row+'"[^>]*>)([\\s\\S]*?)(</row>)'),
        (_,o,b,cl) => o+b+'<c r="'+ref+'" t="s"><v>'+idx+'</v></c>'+cl);
    };

    const crPath = getPath('Checking Review');
    if (!crPath) { toast('Checking Review sheet not found in template'); return; }
    let crXml = await zip.file(crPath).async('string');

    const today = new Date().toLocaleDateString('en-GB');
    allRows.forEach((row, idx) => {
      const r = 11 + idx;
      crXml = writeCell(crXml, 'C'+r, ssIndex(row.docNo));
      crXml = writeCell(crXml, 'E'+r, ssIndex(today));
      crXml = writeCell(crXml, 'F'+r, ssIndex(row.author));
      crXml = writeCell(crXml, 'G'+r, ssIndex(row.author));
      crXml = writeCell(crXml, 'H'+r, ssIndex(row.priority));
      crXml = writeCell(crXml, 'I'+r, ssIndex(row.text));
      crXml = writeCell(crXml, 'M'+r, ssIndex(row.status === 'resolved' ? 'Yes' : 'No'));
    });
    zip.file(crPath, crXml);

    // Update shared strings count
    const cnt = ssEntries.length;
    ssXml = ssXml.replace(/(<sst[^>]+count=")[^"]*(")/,'$1'+cnt+'$2')
                 .replace(/(<sst[^>]+uniqueCount=")[^"]*(")/,'$1'+cnt+'$2');
    zip.file('xl/sharedStrings.xml', ssXml);

    const out = await zip.generateAsync({ type:'uint8array', compression:'DEFLATE',
      compressionOptions:{ level:6 }, mimeType:'application/vnd.ms-excel.sheet.macroEnabled.12' });

    dl(out, 'EMMA_Consolidated_' + new Date().toISOString().slice(0,10) + '.xlsm');
    toast('✓ Consolidated EMMA exported — ' + allRows.length + ' comments from ' + (drawingSet.length + 1) + ' drawings');
  } catch(e) {
    console.error('[EngDoc] batchExportEmma:', e);
    toast('Batch export failed: ' + e.message);
  }
}

// ═══════════════════════════════════════════════
//  SEARCH — persist highlights across navigation
//  When a search result is clicked, keep the
//  highlight visible until search is cleared.
// ═══════════════════════════════════════════════
let _searchPersistHits = []; // [{pageNum, x, y, w, h}]

function clearSearchHighlights() {
  document.querySelectorAll('.search-hit-persist').forEach(el => el.remove());
  _searchPersistHits = [];
}

// Patch highlightSearchHit to also add persistent highlight
const _origHighlightSearchHit = highlightSearchHit;
highlightSearchHit = function(hit) {
  _origHighlightSearchHit(hit);
  // Add persistent highlight div to the overlay
  const ov = document.querySelector('.aoverlay[data-page="' + hit.pageNum + '"]');
  if (!ov) return;
  // Remove existing on same page+position
  ov.querySelectorAll('.search-hit-persist').forEach(e => e.remove());
  const ph = document.createElement('div');
  ph.className = 'search-hit-persist';
  ph.style.cssText =
    'left:' + (hit.x * 100) + '%;top:' + (hit.y * 100) + '%;' +
    'width:' + Math.max(hit.width * 100, 3) + '%;' +
    'height:' + Math.max((hit.fontSize || 0.015) * 100 * 1.6, 1.5) + '%';
  ov.appendChild(ph);
  _searchPersistHits.push(hit);
};

// Clear highlights when search input is cleared
const _origOnSearchInput = onSearchInput;
onSearchInput = function(query) {
  _origOnSearchInput(query);
  if (!query.trim()) clearSearchHighlights();
};

// ═══════════════════════════════════════════════
//  TOUCH / STYLUS SUPPORT
//  Convert pointer events to mouse events so all
//  drawing tools work on touchscreens and tablets.
// ═══════════════════════════════════════════════
function initPointerSupport() {
  document.querySelectorAll('.aoverlay').forEach(ov => {
    if (ov._pointerInited) return;
    ov._pointerInited = true;
    ov.addEventListener('pointerdown', ev => {
      if (ev.pointerType === 'mouse') return;
      ov.setPointerCapture(ev.pointerId);
      ov.dispatchEvent(Object.assign(new MouseEvent('mousedown', ev), { button: 0 }));
    }, { passive: false });
    ov.addEventListener('pointermove', ev => {
      if (ev.pointerType === 'mouse') return;
      ov.dispatchEvent(new MouseEvent('mousemove', ev));
    }, { passive: true });
    ov.addEventListener('pointerup', ev => {
      if (ev.pointerType === 'mouse') return;
      ov.dispatchEvent(new MouseEvent('mouseup', ev));
    });
  });
}

// pointer support now called inside _origRenderPageContent patch above

// ═══════════════════════════════════════════════
//  UPDATE ANNOTATION NAV when annots change
// ═══════════════════════════════════════════════
const _origDeleteAnnotByIdNav = deleteAnnotById;
deleteAnnotById = function(id) {
  _origDeleteAnnotByIdNav(id);
  _annotNavIdx = Math.min(_annotNavIdx, annots.length - 1);
  updateAnnotNavBar();
};

// ═══════════════════════════════════════════════
//  IMAGE INSERTION
//  Click the Image button → file picker opens →
//  image loads as base64 → cursor-following preview
//  appears → click anywhere on the drawing to place
//  → resize with the standard 8-handle resize system.
// ═══════════════════════════════════════════════
let _pendingImage = null; // { src, naturalW, naturalH }

function onImageFileSelected(e) {
  const file = e.target.files[0];
  e.target.value = '';
  if (!file) return;
  const reader = new FileReader();
  reader.onload = ev => {
    const src = ev.target.result;
    const img = new Image();
    img.onload = () => {
      _pendingImage = { src, naturalW: img.naturalWidth, naturalH: img.naturalHeight };
      activateImagePlacement();
    };
    img.src = src;
  };
  reader.readAsDataURL(file);
}

function activateImagePlacement() {
  if (!_pendingImage) return;
  toast('Click on the drawing to place the image · Esc to cancel', 3000);

  let _ghostImg = null, _ghostOv = null;

  function buildGhostImg(ov) {
    const g = document.createElement('div');
    g.id = 'image-ghost';
    g.style.cssText =
      'position:absolute;pointer-events:none;z-index:200;opacity:0.7;' +
      'transform:translate(-50%,-50%);border:2px dashed #2563eb;border-radius:2px;' +
      'background:#fff;overflow:hidden;';
    // Default display size: 20% page width, proportional height
    const aspectH = _pendingImage.naturalH / _pendingImage.naturalW;
    g.style.width  = '20%';
    g.style.height = (20 * aspectH) + '%';
    const img = document.createElement('img');
    img.src = _pendingImage.src;
    img.style.cssText = 'width:100%;height:100%;object-fit:fill;display:block;pointer-events:none';
    g.appendChild(img);
    return g;
  }

  function removeGhostImg() {
    document.getElementById('image-ghost')?.remove();
    _ghostImg = null; _ghostOv = null;
  }

  function onMouseMove(ev) {
    if (!_pendingImage) { removeGhostImg(); return; }
    const ov = ev.target.closest('.aoverlay');
    if (!ov) { removeGhostImg(); return; }
    if (_ghostOv !== ov) {
      removeGhostImg();
      _ghostImg = buildGhostImg(ov);
      _ghostOv  = ov;
      ov.appendChild(_ghostImg);
    }
    const r = ov.getBoundingClientRect();
    _ghostImg.style.left = ((ev.clientX - r.left) / ov.offsetWidth  * 100) + '%';
    _ghostImg.style.top  = ((ev.clientY - r.top)  / ov.offsetHeight * 100) + '%';
  }

  function onClick(ev) {
    if (!_pendingImage) return;
    ev.stopPropagation(); ev.preventDefault();
    const ov  = ev.currentTarget;
    const pn  = parseInt(ov.dataset.page);
    const r   = ov.getBoundingClientRect();
    const xPct = (ev.clientX - r.left) / ov.offsetWidth  * 100;
    const yPct = (ev.clientY - r.top)  / ov.offsetHeight * 100;
    // Default 20% wide, proportional height
    const w = 20;
    const h = w * (_pendingImage.naturalH / _pendingImage.naturalW);
    const img = _pendingImage;
    cleanup();
    const a = { id: nextId(), pageNum: pn, type: 'image',
      x: xPct - w/2, y: yPct - h/2, w, h,
      src: img.src, Color: 'yellow' };
    pushAnnot(a);
    // Select it immediately so resize handles show
    setTimeout(() => {
      const el = document.querySelector('[data-aid="' + a.id + '"]');
      const ov2 = el?.closest('.aoverlay');
      if (el && ov2) showResizeHandles(el, annots.find(x => x.id === a.id), ov2);
    }, 80);
  }

  function cleanup() {
    _pendingImage = null;
    removeGhostImg();
    document.removeEventListener('mousemove', onMouseMove, true);
    document.querySelectorAll('.aoverlay').forEach(o => {
      o.removeEventListener('click', onClick, true);
      o.style.cursor = '';
    });
    document.removeEventListener('keydown', onEsc);
  }

  const onEsc = ev => { if (ev.key === 'Escape') cleanup(); };

  document.querySelectorAll('.aoverlay').forEach(o => {
    o.style.cursor = 'crosshair';
    o.addEventListener('click', onClick, true);
  });
  document.addEventListener('mousemove', onMouseMove, true);
  document.addEventListener('keydown', onEsc);
}

// ═══════════════════════════════════════════════
//  PRINT
//  Renders the current PDF page spread with
//  annotations into a hidden iframe and triggers
//  the browser print dialog.
// ═══════════════════════════════════════════════
async function printDrawing() {
  if (!pdf) { toast('Open a PDF first'); return; }
  toast('Preparing print…', 3000);

  // Build a full-page HTML snapshot of all rendered pages + overlays
  const viewer = document.getElementById('pdfpages');
  const pages  = viewer.querySelectorAll('.pwrap');
  if (!pages.length) { toast('No pages rendered — scroll through the document first'); return; }

  // Clone the page wrappers (canvas + overlays) into a print document
  let bodyHtml = '<style>' +
    'body{margin:0;background:#fff}' +
    '.pwrap{position:relative;page-break-after:always;margin:0 auto 0;display:block}' +
    '.pwrap:last-child{page-break-after:auto}' +
    'canvas{display:block}' +
    '.aoverlay{position:absolute;inset:0;pointer-events:none}' +
    // Copy key annotation CSS
    '.ah{position:absolute;mix-blend-mode:multiply;border-radius:1px}' +
    '.ar{position:absolute;border:2px solid #2563eb;background:rgba(37,99,235,.07);border-radius:1px}' +
    '.an{position:absolute;min-width:140px;background:#fff;border-radius:4px;box-shadow:0 2px 8px rgba(0,0,0,.18);font-family:sans-serif;font-size:11px}' +
    '.an-header{padding:5px 8px;font-size:10px;font-weight:700;font-family:monospace;border-radius:4px 4px 0 0}' +
    '.an-body{padding:5px 8px;font-size:11.5px;line-height:1.45;Color:#333;background:#fff}' +
    '.atxt{position:absolute;font-size:13px;font-weight:500;padding:2px 4px}' +
    '.aimage{position:absolute;overflow:hidden;border-radius:2px}' +
    '.aimage img{width:100%;height:100%;object-fit:fill;display:block}' +
    '.astamp{position:absolute}' +
    '.asvg-wrap{position:absolute;inset:0;overflow:visible}' +
    '.asvg-wrap svg{position:absolute;top:0;left:0;width:100%;height:100%;overflow:visible}' +
    '.ann-move-overlay{display:none}' +
    '.pnbadge{display:none}' +
    '@page{margin:8mm}' +
    '</style>';

  // Convert each canvas to a data URL and clone overlays
  for (const wrap of pages) {
    const canvas = wrap.querySelector('canvas');
    const ov     = wrap.querySelector('.aoverlay');
    const w = wrap.style.width || (canvas?.width + 'px') || '800px';

    let canvasDataUrl = '';
    if (canvas) {
      try { canvasDataUrl = canvas.toDataURL('image/png'); } catch(e) { /* tainted canvas */ }
    }

    // Clone overlay HTML — strip interactive elements
    let ovHtml = '';
    if (ov) {
      const clone = ov.cloneNode(true);
      clone.querySelectorAll('.ann-move-overlay,.resize-handle,[data-leader-handle],.ann-drag-ghost').forEach(e => e.remove());
      clone.querySelectorAll('.an-reply-input-wrap,.an-actions').forEach(e => e.remove());
      clone.style.pointerEvents = 'none';
      ovHtml = clone.outerHTML;
    }

    bodyHtml +=
      '<div class="pwrap" style="width:' + w + '">' +
        (canvasDataUrl ? '<img src="' + canvasDataUrl + '" style="display:block;width:' + w + '">' : '') +
        ovHtml +
      '</div>';
  }

  // Write into hidden iframe and print
  let frame = document.getElementById('print-frame');
  if (frame) frame.remove();
  frame = document.createElement('iframe');
  frame.id = 'print-frame';
  frame.style.cssText = 'position:fixed;top:-9999px;left:-9999px;width:1px;height:1px;border:none';
  document.body.appendChild(frame);

  const doc = frame.contentDocument || frame.contentWindow.document;
  doc.open();
  doc.write('<!DOCTYPE html><html><head><meta charset="UTF-8"></head><body>' + bodyHtml + '</body></html>');
  doc.close();

  frame.contentWindow.focus();
  setTimeout(() => {
    frame.contentWindow.print();
    setTimeout(() => frame.remove(), 2000);
  }, 600);
}
// ═══════════════════════════════════════════════
//  AUTOSAVE RESTORE
// ═══════════════════════════════════════════════
async function doRestore() {
  closeM('mrestore');
  const saved = window._pendingRestore;
  window._pendingRestore = null;
  if (!saved) return;

  toast('Restoring session\u2026', 2500);

  try {
    if (saved.pdfBytes) {
      // This runs at boot, before any tab exists \u2014 wrap the recovered
      // document into tab 1 so it participates in the tab system from
      // here on, same bookkeeping as openFileAsNewTab.
      const id = ++tabIdSeq;
      tabs.push({
        id, name: saved.pdfName, bytes: null, nPages: 0,
        annots: [], emmaRows: {}, annotIdSeq: 0, pageLabels: {},
        history: [], historyIdx: -1,
        zoom: 1, curPg: 1,
        measureScale: null, lastMeasurePx: null,
        selectedPages: [], lastClickedPage: null,
        fileHandle: null, loadedEngdocName: null,
        checkFindings: [], pdfLayers: [],
        searchIndex: [], searchPersistHits: [],
        annotNavIdx: -1, emmaFields: {},
      });
      activeTabId = id;
      const file = new File([saved.pdfBytes], saved.pdfName, { type: 'application/pdf' });
      await loadPDF(file);
    } else {
      pdfName = saved.pdfName;
      const dn = document.getElementById('doc-name');
      if (dn) dn.textContent = saved.pdfName;
    }

    annots     = saved.annots     || [];
    emmaRows   = saved.emmaRows   || {};
    annotIdSeq = saved.annotIdSeq || annots.reduce((m, a) => Math.max(m, a.id || 0), 0);

    if (saved.emmaFields) {
      Object.entries(saved.emmaFields).forEach(([id, val]) => {
        const el = document.getElementById(id);
        if (el) el.value = val;
      });
    }

    syncAnnots(); updateAnnotPanel(); updateEmmaRegister();
    if (activeTabId != null) { saveActiveTabState(); renderTabBar(); }

    const n = annots.length;
    toast('\u2713 Session restored \u2014 ' + n + ' annotation' + (n !== 1 ? 's' : '') +
      (saved.pdfBytes ? '' : ' \u00b7 Re-open the PDF to see the drawing'), 4000);
  } catch(e) {
    toast('Restore failed: ' + e.message);
  }
}

function dismissRestore() {
  closeM('mrestore');
  window._pendingRestore = null;
  idbClearAutosave();
  toast('Auto-save discarded');
}

// Clear autosave after a deliberate file save (it's been committed properly)
const _origSaveSessionAuto = saveSession;
saveSession = function() {
  _origSaveSessionAuto();
  setTimeout(idbClearAutosave, 600);
};
const _origSaveWithPdfAuto = saveSessionWithPdf;
saveSessionWithPdf = async function() {
  await _origSaveWithPdfAuto();
  setTimeout(idbClearAutosave, 600);
};

// Final save on tab close / navigation away
window.addEventListener('beforeunload', () => {
  if (idb && pdfName && annots.length) {
    try {
      const data = {
        id: 'autosave',
        pdfName, annots, emmaRows, annotIdSeq,
        emmaFields: captureEmmaFields(),
        savedAt: new Date().toISOString(),
        annotCount: annots.length,
        pdfBytes: pdfBytes || undefined,
      };
      const tx = idb.transaction('sessions', 'readwrite');
      tx.objectStore('sessions').put(data);
    } catch(e) { /* best-effort on unload */ }
  }
});

_ribbonSetTool('pan');
const _hBtn = document.getElementById('t-pan');
if (_hBtn) _hBtn.classList.add('active');
const _erBtn2 = document.getElementById('t-erase');
if (_erBtn2) _erBtn2.classList.add('eraser-active');
// Start on File tab
switchRibbon('file', document.getElementById('rtab-file'));

// ═══════════════════════════════════════════════
//  RIBBON BUTTON TOOLTIPS
//  #ribbon-body scrolls horizontally (overflow-x:auto),
//  which forces overflow-y to clip too — so a CSS ::after
//  tooltip anchored inside it gets cut off instead of
//  floating over the strip below. Render it in a
//  position:fixed element appended to <body> instead,
//  so it escapes that clipping.
// ═══════════════════════════════════════════════
(() => {
  const tip = document.createElement('div');
  tip.id = 'rbtn-tooltip';
  document.body.appendChild(tip);
  const ribbonBody = document.getElementById('ribbon-body');
  if (!ribbonBody) return;

  const hide = () => { tip.classList.remove('show'); };

  ribbonBody.addEventListener('mouseover', (e) => {
    const btn = e.target.closest('.rbtn[data-tip]');
    if (!btn) return;
    tip.textContent = btn.getAttribute('data-tip');
    const r = btn.getBoundingClientRect();
    tip.style.left = (r.left + r.width / 2) + 'px';
    tip.style.top = (r.bottom + 6) + 'px';
    tip.classList.add('show');
  });
  ribbonBody.addEventListener('mouseout', (e) => {
    if (e.target.closest('.rbtn[data-tip]')) hide();
  });
  ribbonBody.addEventListener('mousedown', hide);
  ribbonBody.addEventListener('scroll', hide);
})();
