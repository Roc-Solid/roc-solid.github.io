const encoder = new TextEncoder();
const decoder = new TextDecoder();
export class NotReady extends Error {
constructor(wait) {
super("not ready");
this.wait = wait;
}
}
export class Failed extends Error {
constructor(message, memo = null) {
super(message);
this.memo = memo;
}
}
const wire = (method, target, headers, body) => [`${method} ${target}`, ...headers.map(([name, value]) => `${name}: ${value}`)].join("\n") + `\n\n${body}`;
let ids = 0;
const making_ = () => ({ children: NONE, kept: NONE, sources: NONE, signals: NONE, cleanups: NONE, queries: NONE, live: false, untracked: 0 });
function addSource(making, source) {
const sources = making.sources;
if (sources === NONE) making.sources = [source];
else if (sources instanceof Set) sources.add(source);
else if (!sources.includes(source)) {
if (sources.length < 8) sources.push(source);
else (making.sources = new Set(sources)).add(source);
}
}
const sourceCount = (sources) => (sources instanceof Set ? sources.size : sources.length);
const NONE = Object.freeze([]);
const own = (record, name) => (record[name] === NONE ? (record[name] = []) : record[name]);
const spare = (record) => {
for (const name of ["children", "kept", "signals", "cleanups", "queries"]) if (record[name]?.length === 0) record[name] = NONE;
return record;
};
const MADE_NONE = Object.freeze({ children: NONE, kept: NONE, cleanups: NONE, signals: NONE, queries: NONE, sources: NONE, live: false });
const MADE_READ = Object.freeze({ children: NONE, kept: NONE, cleanups: NONE, signals: NONE, queries: NONE, sources: NONE, live: true });
const madeNothing = (making) => making.children.length === 0 && making.kept.length === 0 && making.cleanups.length === 0 && making.signals.length === 0 && making.queries.length === 0;
const inert = (making) => !making.live && sourceCount(making.sources) === 0 && making.children.length === 0 && making.signals.length === 0 && making.cleanups.length === 0 && making.queries.length === 0;
class Computation {
constructor(runtime, { kind, runner = null, owner, scope, target = null, name = null }) {
this.id = ++ids;
this.runtime = runtime;
this.kind = kind;
this.runner = runner;
this.scope = scope;
this.target = target;
this.name = name;
this.sources = NONE;
this.observers = null;
this.made = MADE_NONE;
this.calls = null;
this.disposed = false;
this.untracked = false;
owner?.adopt(this);
}
adopt(child) {
own(this.making ?? this.ownMade(), "children").push(child);
}
ownMade() {
if (this.made === MADE_NONE || this.made === MADE_READ) this.made = { ...this.made };
return this.made;
}
}
class Loading {
constructor() {
this.waiting = new Set();
this.revealed = false;
}
wait(computation) {
if (!this.revealed) this.waiting.add(computation);
}
done(computation) {
this.waiting.delete(computation);
if (!this.revealed && this.built && this.waiting.size === 0) this.reveal();
}
reveal() {
this.revealed = true;
replaceRange(this.range, this.children);
}
}
class Errored {
constructor(runtime, { runner, nodes, owner, scope, range }) {
this.runtime = runtime;
this.id = ++ids;
this.runner = runner;
this.nodes = nodes;
this.owner = owner;
this.scope = scope;
this.range = range;
this.failed = null;
this.memos = new Set();
runtime.boundaries.set(this.id, this);
}
build() {
this.inside = new Computation(this.runtime, { kind: "boundary", owner: this.owner, scope: { ...this.scope, errored: this } });
const fragment = document.createDocumentFragment();
for (const node of this.nodes) fragment.append(this.runtime.build(node, this.inside, this.inside.scope));
return fragment;
}
adopt(cursor) {
this.inside = new Computation(this.runtime, { kind: "boundary", owner: this.owner, scope: { ...this.scope, errored: this } });
for (const node of this.nodes) this.runtime.adopt(node, this.inside, this.inside.scope, cursor);
}
fail(problem, memo) {
if (memo) this.memos.add(memo);
if (this.failed !== null) return;
this.failed = problem;
queueMicrotask(() => {
if (this.failed === null) return;
this.runtime.dispose(this.inside);
this.fallback = new Computation(this.runtime, { kind: "html", runner: this.runner, owner: this.owner, scope: this.scope, target: this.range, name: "fallback" });
this.fallback.boundary = this;
this.runtime.run(this.fallback);
});
}
retry() {
if (this.failed === null) return;
this.failed = null;
this.runtime.dispose(this.fallback);
const failed = new Set(this.memos);
for (const memo of failed) {
for (const source of memo.sources) if (source.kind === "memo" && source.state === "failed") failed.add(source);
}
for (const memo of failed) this.runtime.refresh(memo);
this.memos.clear();
replaceRange(this.range, this.build());
}
}
function choosing(computation) {
for (let at = computation; at; at = at.owner) {
if (at.choosing) return true;
if (at.kind === "component") return false;
}
return false;
}
function loneText(nodes) {
return nodes.length === 1 && nodes[0]?.t === "s" ? nodes[0].v : null;
}
function answered(parsed) {
return typeof parsed === "string" ? [{ t: "s", v: parsed }] : Array.isArray(parsed) ? parsed : [parsed];
}
function makeRange(label) {
const start = document.createComment(label);
const end = document.createComment(`/${label}`);
const fragment = document.createDocumentFragment();
fragment.append(start, end);
return { start, end, fragment };
}
function replaceRange(range, content) {
while (range.start.nextSibling && range.start.nextSibling !== range.end) range.start.nextSibling.remove();
range.end.parentNode.insertBefore(content, range.end);
}
function detached(range) {
return range.start.parentNode === null || range.start.parentNode.nodeType === 11;
}
function steady(was) {
const tails = [];
const before = new Array(was.length).fill(-1);
for (let index = 0; index < was.length; index++) {
if (was[index] < 0) continue;
let low = 0;
let high = tails.length;
while (low < high) {
const middle = (low + high) >> 1;
if (was[tails[middle]] < was[index]) low = middle + 1;
else high = middle;
}
if (low > 0) before[index] = tails[low - 1];
tails[low] = index;
}
const stays = new Array(was.length).fill(false);
for (let index = tails.length ? tails[tails.length - 1] : -1; index >= 0; index = before[index]) stays[index] = true;
return stays;
}
function collectRange(range) {
const fragment = document.createDocumentFragment();
let node = range.start;
while (node) {
const next = node.nextSibling;
fragment.append(node);
if (node === range.end) break;
node = next;
}
return fragment;
}
function provided(scope, node) {
return { ...scope, contexts: { ...scope.contexts, [node.n]: node.v } };
}
function inside(range) {
const nodes = [];
for (let node = range.start.nextSibling; node && node !== range.end; node = node.nextSibling) nodes.push(node);
return nodes;
}
function clearRange(range) {
const parent = range.start.parentNode;
if (!parent) return;
if (parent.firstChild === range.start && parent.lastChild === range.end) {
parent.textContent = "";
parent.append(range.start, range.end);
} else {
const between = document.createRange();
between.setStartAfter(range.start);
between.setEndBefore(range.end);
between.deleteContents();
}
}
function removeRange(range) {
let node = range.start;
while (node) {
const next = node.nextSibling;
node.remove();
if (node === range.end) break;
node = next;
}
}
function isRegionStart(data) {
return data === "nohydration" || data === "nohydration:read";
}
function serverRegions(root) {
const starts = [];
const walker = root.ownerDocument.createTreeWalker(root, 128 );
for (let node = walker.nextNode(); node; node = walker.nextNode()) if (isRegionStart(node.data)) starts.push(node);
return starts
.map((start) => {
let end = start.nextSibling;
while (end && !(end.nodeType === 8 && end.data === "/nohydration")) end = end.nextSibling;
return end ? collectRange({ start, end }) : null;
})
.filter(Boolean);
}
const inRegion = (tag, event) => `rocx: <${tag} on:${event}> is inside <NoHydration>, which the browser never hydrates, so its handler would never run: render what has it outside <NoHydration>`;
class Mismatch extends Error {
constructor(message, found = null) {
super(message);
this.found = found;
}
}
function named(node) {
if (!node) return "nothing";
if (node.nodeType === 1) {
const id = node.id ? `#${node.id}` : "";
const classes = words(node.getAttribute("class") ?? "").filter((name) => !name.startsWith("rx-")).slice(0, 3);
return `<${node.localName}${id}${classes.map((name) => `.${name}`).join("")}>`;
}
if (node.nodeType === 3) return "text";
if (node.nodeType === 8) return `<!--${node.data.slice(0, 40)}-->`;
if (node.nodeType === 10) return "<!doctype>";
return node.nodeName;
}
function placed(element) {
const path = [];
for (let at = element; at?.nodeType === 1 && at.localName !== "html" && path.length < 6; at = at.parentNode) path.unshift(named(at).slice(1, -1));
return path.length ? ` in ${path.join(" > ")}` : "";
}
const foreignNodes = new WeakSet();
let foreignKept = true;
class Pending {
constructor() {
this.set = new Set();
this.heap = [];
}
get size() {
return this.set.size;
}
has(computation) {
return this.set.has(computation);
}
add(computation) {
if (this.set.has(computation)) return;
this.set.add(computation);
const heap = this.heap;
let at = heap.push(computation) - 1;
while (at > 0) {
const parent = (at - 1) >> 1;
if (heap[parent].id <= computation.id) break;
heap[at] = heap[parent];
at = parent;
}
heap[at] = computation;
}
delete(computation) {
return this.set.delete(computation);
}
take() {
const heap = this.heap;
while (heap.length) {
const top = heap[0];
const last = heap.pop();
if (heap.length) {
let at = 0;
for (;;) {
const left = 2 * at + 1;
if (left >= heap.length) break;
const right = left + 1;
const child = right < heap.length && heap[right].id < heap[left].id ? right : left;
if (heap[child].id >= last.id) break;
heap[at] = heap[child];
at = child;
}
heap[at] = last;
}
if (this.set.delete(top)) return top;
}
return undefined;
}
}
const hosts = (node) => node.nodeType === 1 && node.hasAttribute("data-rocx");
const blank = (text) => /^[\t\n\f\r ]*$/.test(text);
const words = (text) => text.split(/[\t\n\f\r ]+/).filter(Boolean);
const joined = (attrs, name) => attrs.some(([kind]) => (name === "class" ? kind === "ci" || kind === "co" : name === "style" && (kind === "sv" || kind === "so")));
const computedOf = (attrs, name) => attrs.some(([kind, named]) => named === name && (kind === "vo" || kind === "oo"));
class Cursor {
constructor(node, parent = node?.parentNode ?? null, rebuild = false) {
this.parent = parent;
this.rebuild = rebuild;
this.node = node;
}
get node() {
return this.at;
}
set node(node) {
while (node && hosts(node)) node = node.nextSibling;
this.at = node;
}
get top() {
return this.parent?.nodeType === 9 || (this.parent !== null && this.parent === this.parent.ownerDocument?.documentElement);
}
get foreign() {
const parent = this.parent;
const doc = parent?.ownerDocument;
return foreignKept && !this.rebuild && !!doc && (parent === doc.body || parent === doc.head || parent === doc.documentElement);
}
passForeign(check) {
if (!this.foreign) return;
let at = this.node;
while (at && at.nodeType === 1 && !check(at)) at = at.nextSibling;
if (!at || !check(at)) return;
for (let node = this.node; node !== at; node = node.nextSibling) foreignNodes.add(node);
this.node = at;
}
left(blankToo) {
const foreign = this.foreign;
for (let node = this.node; node; node = node.nextSibling) {
if (hosts(node) || ((blankToo || foreign) && node.nodeType === 3 && blank(node.data))) continue;
if (foreign && node.nodeType === 1) {
foreignNodes.add(node);
continue;
}
return node;
}
return null;
}
take(check, what) {
if (this.parent?.nodeType === 9 && this.node?.nodeType === 10 && !check(this.node)) this.node = this.node.nextSibling;
if (this.rebuild) while (this.node && !check(this.node)) this.node = this.node.nextSibling;
if (this.node && !check(this.node)) this.passForeign(check);
const node = this.node;
if (!node || !check(node)) throw new Mismatch(`expected ${what}, found ${named(node)}${placed(this.parent)}`, node);
this.node = node.nextSibling;
return node;
}
comment(label) {
return this.take((node) => node.nodeType === 8 && node.data === label, `<!--${label}-->`);
}
closing(label) {
let depth = 0;
for (let node = this.node; node; node = node.nextSibling) {
if (node.nodeType !== 8) continue;
if (!node.data.startsWith("/") && RANGES.has(node.data.split(":")[0])) depth++;
else if (node.data.startsWith("/")) {
if (depth === 0) {
if (node.data !== `/${label}`) break;
return node;
}
depth--;
}
}
throw new Mismatch(`no <!--/${label}-->`);
}
end(end) {
if (this.node !== end) this.passForeign((node) => node === end);
if (this.node !== end) throw new Mismatch(`expected the end of a range, found ${named(this.node)}${placed(this.parent)}`, this.node);
}
}
function inertScript() {
const template = document.createElement("template");
template.innerHTML = "<script></script>";
return document.importNode(template.content.firstChild, true);
}
function plainName(name, attribute) {
const length = name.length;
for (let at = 0; at < length; at++) {
const c = name.charCodeAt(at) | 32;
if (c >= 97 && c <= 122) continue;
const code = name.charCodeAt(at);
if (at === 0 || !((code >= 48 && code <= 57) || code === 45 || (attribute && (code === 95 || code === 46 || code === 58)))) return false;
}
return length > 0 && !(attribute && length >= 2 && (name.charCodeAt(0) | 32) === 111 && (name.charCodeAt(1) | 32) === 110);
}
const NAMED = new Set(["v", "o", "vo", "oo", "f", "fo"]);
function ownsCurrent(node) {
for (const [kind, name] of node.a) if (NAMED.has(kind) && name === "aria-current") return true;
return false;
}
const refusedNames = new Set();
function writable(node, runtime) {
const tag = node.tag;
if (!plainName(tag, false) || (isScript(tag) && !(node.c.length && node.c.every((part) => part.t === "raw")))) {
refuse(`<${tag}>`);
return null;
}
let kept = null;
for (let at = 0; at < node.a.length; at++) {
const attribute = node.a[at];
if (NAMED.has(attribute[0]) && !plainName(attribute[1], true)) {
kept ??= node.a.slice(0, at);
refuse(`${attribute[1]} on <${tag}>`);
if (runtime && attribute[0].length === 2) runtime.releaseKept(attribute[2]);
} else if (kept) kept.push(attribute);
}
return kept ? { ...node, a: kept } : node;
}
function isScript(tag) {
if (tag.length !== 6) return false;
for (let at = 0; at < 6; at++) if ((tag.charCodeAt(at) | 32) !== "script".charCodeAt(at)) return false;
return true;
}
function refuse(what) {
if (refusedNames.has(what)) return;
refusedNames.add(what);
console.warn(`rocx: ${what} isn't written: a page can't have that name (D-079). Markup built by hand (Html.element, Html.attr) names only plain elements and attributes, never an inline handler (on…) or a <script> of data`);
}
const RANGES = new Set(["app", "html", "list", "loading", "errored", "x", "show", "for", "row", "fallback", "nohydration"]);
const RCDATA = new Set(["title", "textarea"]);
const VOID = new Set(["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"]);
const escape = (text) => String(text).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;").replace(/'/g, "&#39;");
const START = '<script type="module" data-rocx src="/rocx/start.js"></script>';
const startWith = (build) => (build === null ? START : `<script type="module" data-rocx data-build="${build.replace(/&/g, "&amp;").replace(/"/g, "&quot;").replace(/</g, "&lt;")}" src="/rocx/start.js"></script>`);
const REMADE = Symbol("remade");
function regionRanges(doc) {
const ranges = [];
const walker = doc.createTreeWalker(doc.documentElement ?? doc, 128 );
for (let node = walker.nextNode(); node; node = walker.nextNode()) {
if (!isRegionStart(node.data)) continue;
let end = node.nextSibling;
while (end && !(end.nodeType === 8 && end.data === "/nohydration")) end = end.nextSibling;
if (end) ranges.push({ start: node, end });
}
return ranges;
}
const REACHED = Promise.resolve();
const DOCUMENT = /^\s*(?:<!--[^>]*-->\s*|<!doctype[^>]*>\s*)*<html[\s>]/i;
const SVG = "http://www.w3.org/2000/svg";
const OWN_PARTS = new Set(["show", "for", "leaving"]);
const reducedMotion = () => typeof matchMedia === "function" && matchMedia("(prefers-reduced-motion: reduce)").matches;
const WAITS = 0xffffffff;
const READERS = new Set(["memo", "text", "attr", "flag", "class", "optional", "style", "html", "show", "for", "reaction", "transition", "drag"]);
const submissionJson = ({ id, state, input, json, status, body }, listed = false) => JSON.stringify(listed ? { id, state, input, json, status, body } : { state, input, json, status, body });
const CLEARED = submissionJson({ state: "cleared", input: "", json: false, status: 0, body: "" });
const DRAG_EVENTS = new Set(["dragstart", "dragenter", "dragleave", "drop"]);
const dropEffect = (allowed) => (/move|all|uninitialized/i.test(allowed ?? "all") ? "move" : /copy/i.test(allowed) ? "copy" : /link/i.test(allowed) ? "link" : "none");
const POINTER_DRAG = { hold: 250, slop: 8, edge: 48, speed: 16 };
const MOVES = new Set(["pointermove", "mousemove", "touchmove", "pointerrawupdate"]);
const POPOVER_LOOK = ["color", "background-color", "overflow-x", "overflow-y", "padding-top", "padding-right", "padding-bottom", "padding-left", ...["top", "right", "bottom", "left"].flatMap((side) => [`border-${side}-width`, `border-${side}-style`, `border-${side}-color`])];
const itemsOf = (transfer) => JSON.stringify([...(transfer?.types ?? [])].filter((type) => type !== "Files" && type !== "application/x-rocx").map((type) => ({ type, value: transfer.getData(type) })));
function makeTransfer() {
try {
const transfer = new DataTransfer();
let allowed = "uninitialized";
let effect = "none";
Object.defineProperties(transfer, {
effectAllowed: { get: () => allowed, set: (value) => void (allowed = String(value)), configurable: true },
dropEffect: { get: () => effect, set: (value) => void (/^(none|copy|link|move)$/.test(value) && (effect = value)), configurable: true },
});
return transfer;
} catch {
const data = new Map();
return {
dropEffect: "none",
effectAllowed: "uninitialized",
files: [],
items: [],
get types() {
return [...data.keys()];
},
setData: (type, value) => void data.set(String(type).toLowerCase(), String(value)),
getData: (type) => data.get(String(type).toLowerCase()) ?? "",
clearData: (type) => (type === undefined ? data.clear() : data.delete(String(type).toLowerCase())),
setDragImage: () => {},
};
}
}
const MAC = typeof navigator !== "undefined" && /mac|iphone|ipad|ipod/i.test(navigator.userAgentData?.platform ?? navigator.platform ?? "");
const MODIFIERS = { Shift: ["shiftKey", "Shift"], Ctrl: ["ctrlKey", "Control"], Alt: ["altKey", "Alt"], Meta: ["metaKey", "Meta"] };
function keyCombo(wanted) {
const parts = wanted.split("+");
const key = parts.pop();
const held = new Set(parts.map((name) => (name === "Mod" ? (MAC ? "Meta" : "Ctrl") : name)));
const single = /^[a-z0-9]$/i.test(key) ? key.toLowerCase() : null;
const code = single && (/[0-9]/.test(single) ? `Digit${single}` : `Key${single.toUpperCase()}`);
return (event) => {
if (event.isComposing) return false;
const pressed = event.key ?? "";
if (single ? (/^[a-z0-9]$/i.test(pressed) ? pressed.toLowerCase() !== single : event.code !== code) : pressed !== key) return false;
return Object.entries(MODIFIERS).every(([name, [flag, own]]) => key === own || Boolean(event[flag]) === held.has(name));
};
}
const keysOf = (event) => [event.shiftKey, event.ctrlKey, event.altKey, event.metaKey, MAC ? event.metaKey : event.ctrlKey].map((on) => (on ? "1" : "0")).join("") + (event.key ?? "");
const camel = (property) => property.replace(/-([a-z])/g, (_, letter) => letter.toUpperCase());
const within = (node, scope) => (node.tag === "svg" && !scope.svg ? { ...scope, svg: true } : scope);
class Hub {
constructor(runtime) {
this.runtime = runtime;
this.channels = new Map();
this.stream = null;
this.reconciling = null;
this.retrying = null;
this.drops = 0;
this.first = 500;
this.most = 30000;
this.steady = 10000;
this.unavailable = null;
this.outbox = [];
this.flushing = false;
this.tabId = null;
this.stats = { connects: 0, posts: 0 };
}
tab({ fresh = false } = {}) {
if (this.tabId && !fresh) return this.tabId;
const made = () => [...crypto.getRandomValues(new Uint8Array(12))].map((byte) => byte.toString(16).padStart(2, "0")).join("");
try {
this.tabId = (!fresh && sessionStorage.getItem("rocx-tab")) || made();
sessionStorage.setItem("rocx-tab", this.tabId);
} catch {
this.tabId = made();
}
return this.tabId;
}
subscribe(url, ptr) {
const runtime = this.runtime;
if (runtime.onServer) return runtime.ex.release(ptr);
const cleanups = runtime.cleanupsOf(runtime.current);
if (!cleanups) {
runtime.ex.release(ptr);
throw new Failed(`Endpoint.subscribe!(${url}) is called in a component, a computation or an effect, not in a handler: nothing would end it`);
}
const id = ++ids;
runtime.kept.set(id, ptr);
const subscriber = { id, url, scope: runtime.current?.scope ?? null, owner: runtime.owner(), queue: [], busy: false, gone: false };
let channel = this.channels.get(url);
const fresh = !channel;
if (fresh) {
channel = { subscribers: new Map(), open: false, refused: null, ended: null };
this.channels.set(url, channel);
}
channel.subscribers.set(id, subscriber);
cleanups.push(() => this.unsubscribe(subscriber));
runtime.notify("subscribe", { url });
const told = this.unavailable ? { Refused: this.unavailable } : channel.refused ? { Refused: channel.refused } : channel.ended !== null ? { Ended: channel.ended } : null;
if (told) queueMicrotask(() => this.deliver(subscriber, told));
else if (channel.open) this.post(`{"channel":${JSON.stringify(url)},"resync":true}`);
if (fresh) this.changed();
}
unsubscribe(subscriber) {
subscriber.gone = true;
subscriber.queue.length = 0;
queueMicrotask(() => this.runtime.releaseKept(subscriber.id));
this.runtime.notify("unsubscribe", { url: subscriber.url });
const channel = this.channels.get(subscriber.url);
if (!channel?.subscribers.delete(subscriber.id) || channel.subscribers.size) return;
this.changed();
}
say(url, json) {
if (this.runtime.onServer) return;
this.post(`{"channel":${JSON.stringify(url)},"message":${json}}`);
}
resync(url) {
if (this.channels.get(url)?.open) this.post(`{"channel":${JSON.stringify(url)},"resync":true}`);
}
changed() {
if (this.reconciling) return;
this.reconciling = setTimeout(() => {
this.reconciling = null;
this.reconcile();
}, 0);
}
reconcile() {
for (const [url, channel] of this.channels) if (!channel.subscribers.size) this.channels.delete(url);
if (this.unavailable || this.retrying) return;
const urls = [...this.channels.keys()].sort();
const stream = this.stream;
if (!stream) {
if (urls.length) this.connect(urls);
return;
}
const wanted = new Set(urls);
const dropped = [...stream.urls].filter((url) => !wanted.has(url));
const added = urls.filter((url) => !stream.urls.has(url));
if (!dropped.length && !added.length) return;
if (stream.legacy) {
stream.controller.abort();
this.stream = null;
if (urls.length) this.connect(urls);
return;
}
if (!stream.id) return;
for (const url of dropped) {
stream.urls.delete(url);
this.post(`{"channel":${JSON.stringify(url)},"unsubscribe":true}`, { stream });
}
for (const url of added) {
stream.urls.add(url);
this.post(`{"channel":${JSON.stringify(url)},"subscribe":true}`, { stream });
}
}
async connect(urls) {
const controller = new AbortController();
const stream = { urls: new Set(urls), controller, opened: performance.now(), id: null, legacy: false };
this.stream = stream;
this.outbox = this.outbox.filter((item) => !item.stream);
for (const channel of this.channels.values()) Object.assign(channel, { open: false, refused: null, ended: null });
this.stats.connects++;
this.runtime.notify("connect", { urls });
const query = [`tab=${encodeURIComponent(this.tab())}`, ...urls.map((url) => `c=${encodeURIComponent(url)}`)].join("&");
try {
const response = await fetch(this.runtime.under(`/rocx/live?${query}`), { headers: { accept: "text/event-stream" }, cache: "no-store", signal: controller.signal });
if (!(response.headers.get("content-type") ?? "").startsWith("text/event-stream")) {
response.body?.cancel();
if (response.status < 500) return this.giveUp(stream);
throw new Error(`${response.status}`);
}
const reader = response.body.pipeThrough(new TextDecoderStream()).getReader();
let buffer = "";
for (;;) {
const { value, done } = await reader.read();
if (done || this.stream !== stream) break;
buffer += value.replaceAll("\r\n", "\n");
for (let end = buffer.indexOf("\n\n"); end >= 0; end = buffer.indexOf("\n\n")) {
const lines = buffer.slice(0, end).split("\n");
buffer = buffer.slice(end + 2);
const field = (name) => lines.filter((line) => line.startsWith(`${name}:`)).map((line) => line.slice(name.length + 1).replace(/^ /, ""));
const data = field("data");
const kind = field("event")[0] ?? "message";
if (!data.length || this.stream !== stream) continue;
if (kind === "hello") {
stream.id = data[0];
this.runtime.notify("hello", { stream: stream.id });
this.reconcile();
continue;
}
if (!stream.id && !stream.legacy) {
stream.legacy = true;
this.reconcile();
}
this.dispatch(kind, data[0], data.slice(1).join("\n"));
}
}
} catch {
}
if (this.stream !== stream) return;
this.stream = null;
this.drops = performance.now() - stream.opened >= this.steady ? 0 : this.drops + 1;
const wait = Math.min(this.most, this.first * 2 ** Math.max(0, this.drops - 1)) * (1 + Math.random() / 4);
this.runtime.notify("dropped", { wait });
this.retrying = setTimeout(() => {
this.retrying = null;
this.reconcile();
}, wait);
}
giveUp(stream) {
if (this.stream === stream) this.stream = null;
this.unavailable = [404, "no server answers channels here (a static copy of the site?)"];
for (const channel of this.channels.values()) for (const subscriber of channel.subscribers.values()) this.deliver(subscriber, { Refused: this.unavailable });
}
dispatch(kind, url, said) {
if (kind === "replaced") {
this.runtime.notify("replaced", { tab: this.tabId });
this.tab({ fresh: true });
return;
}
const channel = this.channels.get(url);
if (!channel) return;
let heard;
if (kind === "resync") {
Object.assign(channel, { open: true, refused: null, ended: null });
heard = "Resync";
} else if (kind === "message") heard = { Message: said };
else if (kind === "refused") {
const { status, why } = JSON.parse(said);
channel.refused = [status, why];
heard = { Refused: channel.refused };
} else if (kind === "ended") {
Object.assign(channel, { open: false, ended: JSON.parse(said) });
heard = { Ended: channel.ended };
} else return;
this.runtime.notify("heard", { url, heard });
for (const subscriber of channel.subscribers.values()) this.deliver(subscriber, heard);
}
deliver(subscriber, heard) {
if (subscriber.gone) return;
subscriber.queue.push(heard);
this.pump(subscriber);
}
pump(subscriber) {
while (!subscriber.busy && !subscriber.gone && subscriber.queue.length && this.runtime.kept.has(subscriber.id)) {
const heard = subscriber.queue.shift();
subscriber.busy = true;
let returned = false;
this.runtime.handle(subscriber.id, JSON.stringify(heard), subscriber.scope, {
owner: subscriber.owner,
done: () => {
subscriber.busy = false;
if (returned) this.pump(subscriber);
},
});
returned = true;
}
}
post(text, { stream = null } = {}) {
if (this.unavailable) return;
this.outbox.push({ text, stream });
if (this.flushing) return;
this.flushing = true;
const go = () => {
this.flushing = false;
this.send();
};
if (typeof requestAnimationFrame === "function" && document.visibilityState === "visible") requestAnimationFrame(go);
else setTimeout(go, 0);
}
async send() {
const stream = this.stream;
const items = this.outbox.splice(0).filter((item) => !item.stream || item.stream === stream);
if (!items.length) return;
this.stats.posts++;
const query = `tab=${encodeURIComponent(this.tab())}${stream?.id ? `&stream=${encodeURIComponent(stream.id)}` : ""}`;
try {
const response = await fetch(this.runtime.under(`/rocx/live/send?${query}`), { method: "POST", headers: { "content-type": "application/json" }, body: `[${items.map((item) => item.text).join(",")}]` });
if (response.status === 200) {
const { refused = [] } = await response.json();
for (const { index, status, why } of refused) {
if (items[index].stream && status === 404) {
if (this.stream === stream) {
stream.controller.abort();
this.stream = null;
this.reconcile();
}
} else console.warn(`rocx: ${JSON.parse(items[index].text).channel} refused what was said: ${status} ${why}`);
}
} else if (response.status === 404 || response.status === 405) this.unavailable ??= [404, "no server answers channels here (a static copy of the site?)"];
else if (!response.ok) console.warn(`rocx: what was said wasn't heard: ${response.status} ${await response.text()}`);
} catch {
}
if (this.stream === stream && stream && !this.channels.size && !stream.urls.size) {
stream.controller.abort();
this.stream = null;
}
}
}
export class Runtime {
static CACHE = 8;
static FRESH = 10_000;
static REST = 65;
static LEAVES = 64;
static ASKED = 1000;
static async load(source, { base = "/", effects = {} } = {}) {
const runtime = new Runtime(null, base);
const env = new Proxy(runtime.imports, { get: (imports, name) => imports[name] ?? (() => { throw new Error(`rocx: the runtime has no import ${String(name)}`); }) });
const resolved = await source;
const { instance } =
resolved instanceof Response && typeof WebAssembly.instantiateStreaming === "function" && resolved.headers.get("content-type")?.startsWith("application/wasm")
? await WebAssembly.instantiateStreaming(resolved, { env })
: await WebAssembly.instantiate(resolved instanceof Response ? await resolved.arrayBuffer() : resolved, { env });
runtime.ex = instance.exports;
runtime.effects = effects;
return runtime;
}
constructor(exports, base = "/") {
this.ex = exports;
this.base = base.endsWith("/") ? base : `${base}/`;
this.kept = new Map();
this.signals = new Map();
this.memos = new Map();
this.selectors = new Map();
this.templateIds = new Map();
this.templates = [null];
this.links = new WeakSet();
this.lists = new Map();
this.boundaries = new Map();
this.timers = new Map();
this.effects = {};
this.calling = [];
this.toEffects = Object.freeze({ under: (url) => this.under(url) });
this.builtins = { "rocx:focus": (id) => this.page?.getElementById?.(id)?.focus() };
this.transitions = new WeakMap();
this.animates = false;
this.rawStyles = new WeakMap();
this.computedClasses = new WeakMap();
this.computedStyles = new WeakMap();
this.classToggles = new WeakMap();
this.enhancedImages = new WeakMap();
this.entering = [];
this.titles = new Map();
this.titleSeqs = 0;
this.titlesDirty = false;
this.titled = null;
this.heads = new Map();
this.headSeqs = 0;
this.headsDirty = false;
this.headed = [];
this.transition = null;
this.leaving = new Map();
this.leavingNodes = new WeakMap();
this.keys = new WeakMap();
this.gliders = new Set();
this.measured = null;
this.measuredIn = null;
this.glides = new WeakMap();
this.lifted = new Map();
this.inFlush = false;
this.overs = new Set();
this.dragEnds = null;
this.dragged = new WeakMap();
this.pointerDrag = null;
this.files = new Map();
this.keeping = false;
this.current = null;
this.dirty = new Pending();
this.due = new Pending();
this.flushing = false;
this.actions = new Map();
this.submissions = new Map();
this.submitting = null;
this.readers = new Set();
this.waiting = null;
this.flash = "";
this.flashed = "";
this.secrets = [];
this.taken = null;
this.stats = { runs: 0, aborts: 0, patches: 0, selections: 0 };
this.answers = new Map();
this.flashReaders = new Set();
this.refreshed = null;
this.request = "";
this.recorded = [];
this.headers = [];
this.onServer = false;
this.hydrating = null;
this.status = 200;
this.page = typeof document === "undefined" ? null : document;
this.observer = null;
this.place = null;
this.warned = new Set();
this.hub = new Hub(this);
this.locationSource = { observers: new Set() };
this.committed = null;
this.routing = { on: false, observers: new Set() };
this.leaveListeners = new Set();
this.leaves = new Map();
this.leaveAsked = null;
this.unloadGuard = null;
this.loadAsked = -Infinity;
this.app = null;
this.built = null;
this.imports = this.makeImports();
}
notify(kind, detail) {
if (this.observer) this.observer[kind]?.(detail);
}
text(ptr, len) {
return decoder.decode(new Uint8Array(this.ex.memory.buffer, ptr >>> 0, len >>> 0));
}
enter(call) {
const sp = this.ex.__stack_pointer.value;
const frame = this.ex.frame_begin();
try {
call();
this.ex.frame_end(frame);
return this.text(this.ex.result_ptr(), this.ex.result_len());
} catch (error) {
this.ex.__stack_pointer.value = sp;
this.ex.frame_unwound(frame);
if (error && typeof error === "object") error.frame = frame;
throw error;
}
}
reclaim(error) {
if (error?.frame) this.ex.reclaim(error.frame);
if (error) error.frame = 0;
}
give(text) {
this.taken = encoder.encode(text);
return this.taken.length;
}
makeImports() {
const text = (ptr, len) => this.text(ptr, len);
return {
js_log: (ptr, len) => console.log(text(ptr, len)),
js_crashed: (ptr, len) => {
throw new Error(`roc crashed: ${text(ptr, len)}`);
},
js_take: (dest) => new Uint8Array(this.ex.memory.buffer, dest >>> 0, this.taken.length).set(this.taken),
js_keep: (ptr) => {
const id = ++ids;
this.kept.set(id, ptr);
const making = this.current?.making;
if (making) own(making, "kept").push(id);
return id;
},
js_signal_new: (ptr) => {
this.touch();
const id = ++ids;
this.signals.set(id, { id, value: ptr, observers: new Set() });
const making = this.current?.making;
if (making) own(making, "signals").push(id);
return id;
},
js_signal_get: (id) => {
const signal = this.signals.get(id);
if (!signal) throw new Error("rocx: a signal was read after the part that made it went away");
this.track(signal);
if (this.current?.own > 0) return this.ownWrite(this.current, signal) ?? signal.value;
return signal.value;
},
js_signal_set: (id, ptr) => {
const handler = this.current;
if (handler?.kind !== "handler") {
this.ex.release(ptr);
throw new Failed("a signal is written in a handler, not while computing");
}
handler.writes.push({ signal: this.signals.get(id), value: ptr });
},
js_memo_new: (ptr) => {
this.touch();
const memo = new Computation(this, { kind: "memo", runner: ptr, owner: this.current, scope: this.current?.scope ?? {} });
memo.state = "pending";
memo.value = 0;
memo.refreshing = memo.stale = false;
memo.pending = { observers: new Set() };
this.memos.set(memo.id, memo);
this.run(memo);
return memo.id;
},
js_memo_done: (ptr, same) => {
if (this.current?.next) this.ex.release(this.current.next);
this.current.next = ptr;
this.current.same = same !== 0;
},
js_tracking: () => {
const running = this.current;
return !this.onServer && running?.making && running.making.untracked === 0 && !running.untracked && running.kind !== "component" && running.kind !== "once" ? 1 : 0;
},
js_memo_last: () => {
this.stats.selections++;
const memo = this.current;
return memo?.kind === "memo" && memo.state === "ok" && memo.value ? memo.value : 0;
},
js_signal_latest: (id) => {
const signal = this.signals.get(id);
if (!signal) throw new Error("rocx: a signal was read after the part that made it went away");
return (this.current?.kind === "handler" && this.ownWrite(this.current, signal)) || signal.value;
},
js_own_writes: (on) => {
const handler = this.current;
if (handler?.kind === "handler") handler.own = Math.max(0, (handler.own ?? 0) + (on ? 1 : -1));
},
js_selector_new: (ptr) => {
this.touch();
const selector = new Computation(this, { kind: "selector", runner: ptr, owner: this.current, scope: this.current?.scope ?? {} });
selector.key = null;
selector.keys = new Map();
this.selectors.set(selector.id, selector);
this.run(selector);
return selector.id;
},
js_template: (ptr, len) => {
if (this.onServer || this.current?.adopting) return 0;
const site = text(ptr, len);
let id = this.templateIds.get(site);
if (id === undefined) {
id = this.templates.length;
this.templates.push(null);
this.templateIds.set(site, id);
}
const template = this.templates[id];
return template === false ? 0 : id * 2 + (template ? 1 : 0);
},
js_selector_is: (id, ptr, len) => {
const selector = this.selectors.get(id);
if (!selector) throw new Error("rocx: a selector was read after the part that made it went away");
const key = text(ptr, len);
let source = selector.keys.get(key);
if (!source) selector.keys.set(key, (source = { observers: null, selector, key }));
this.track(source);
if (selector.key === null) throw new NotReady(selector.settled ??= new Promise((resolve) => (selector.settle = resolve)));
return selector.key === key ? 1 : 0;
},
js_memo_get: (id) => {
const memo = this.memos.get(id);
if (this.current?.kind === "probe") this.current.memos.add(memo);
this.track(memo);
if (memo.state === "failed") throw new Failed(memo.error, memo);
if (memo.value) return memo.value;
throw new NotReady(memo.settled ??= new Promise((resolve) => (memo.settle = resolve)));
},
js_refresh: (ptr) => {
let memos;
try {
memos = this.probe(ptr);
} finally {
this.ex.release(ptr);
}
for (const memo of memos) this.later({ refresh: memo });
},
js_is_pending: (ptr) => {
this.touch(true);
if (this.onServer) {
this.ex.release(ptr);
return 0;
}
let memos;
try {
memos = this.probe(ptr);
} catch (error) {
this.ex.release(ptr);
throw error;
}
const answer = this.pending(memos);
const making = this.current?.making;
if (!making || making.untracked > 0) {
this.ex.release(ptr);
return answer ? 1 : 0;
}
const id = ++ids;
this.kept.set(id, ptr);
own(making, "kept").push(id);
own(making, "queries").push({ probe: id, memos, answer });
for (const memo of memos) this.track(memo.pending);
return answer ? 1 : 0;
},
js_fail: (ptr, len) => {
throw new Failed(text(ptr, len));
},
js_event_value: () => this.give(this.current?.event ?? ""),
js_boundary: () => this.current.boundary.id,
js_problem: () => this.give(this.current.boundary.failed ?? ""),
js_retry: (id) => this.later({ retry: this.boundaries.get(id) }),
js_request: () => this.give(this.request),
js_for_new: () => {
const id = ++ids;
this.lists.set(id, { id, rows: new Map(), indexes: new Map(), items: new Map() });
return id;
},
js_row_index: (id, ptr, len) => {
const index = this.lists.get(id).indexes.get(text(ptr, len));
this.track(index);
return index.value;
},
js_row_set: (id, keyPtr, keyLen, ptr, same) => {
const list = this.lists.get(id);
const at = text(keyPtr, keyLen);
const item = list.items.get(at);
if (!item) {
list.items.set(at, { value: ptr, observers: null });
return list.rows.has(at) ? 1 : 0;
}
this.ex.release(item.value);
item.value = ptr;
if (!same) for (const observer of item.observers ?? NONE) this.schedule(observer);
return list.rows.has(at) ? 1 : 0;
},
js_row_last: (id, keyPtr, keyLen) => this.lists.get(id).items.get(text(keyPtr, keyLen))?.value ?? 0,
js_row_get: (id, keyPtr, keyLen) => {
const item = this.lists.get(id).items.get(text(keyPtr, keyLen));
this.track(item);
return item.value;
},
js_context_value: (ptr) => {
const id = ++ids;
this.kept.set(id, ptr);
const making = this.current?.making;
if (making) own(making, "kept").push(id);
return id;
},
js_context_find: (ptr, len) => this.current?.scope?.contexts?.[text(ptr, len)] ?? 0,
js_context_get: (id) => this.kept.get(id),
js_fetch: (mp, ml, up, ul, hp, hl, bp, bl) => {
try {
return this.fetchFor(text(mp, ml), text(up, ul), text(hp, hl), text(bp, bl));
} catch (error) {
if (!(error instanceof NotReady || error instanceof Failed)) throw error;
this.waiting = error;
return WAITS;
}
},
js_waits: () => {
const error = this.waiting;
this.waiting = null;
throw error;
},
js_listen: (up, ul, ptr) => {
this.touch();
return this.listenTo(text(up, ul), ptr);
},
js_subscribe: (up, ul, ptr) => {
this.touch();
return this.hub.subscribe(text(up, ul), ptr);
},
js_say: (up, ul, sp, sl) => this.hub.say(text(up, ul), text(sp, sl)),
js_resync: (up, ul) => this.hub.resync(text(up, ul)),
js_live_publish: () => {
throw new Failed("Endpoint.publish! is the server's: a page says things on a channel with Endpoint.say!");
},
js_timer: (ms, repeat, ptr) => {
this.touch();
return this.startTimer(ms, repeat === 1, ptr);
},
js_clear_timer: (id) => this.clearTimer(id),
js_browser_call: (np, nl, ap, al) => {
const name = text(np, nl);
const handler = this.current;
if (handler?.kind !== "handler") throw new Failed(`Browser.call!("${name}") is a handler's: call it from an event, a frame or a timer, not while computing`);
handler.writes.push({ effect: name, arg: text(ap, al) });
},
js_location: () => {
this.touch(true);
const reader = this.current;
if (reader?.making && reader.making.untracked === 0) addSource(reader.making, this.locationSource);
if (reader && !choosing(reader) && (reader.kind === "component" || reader.making?.untracked > 0 || reader.untracked)) this.readOnce?.(reader);
return this.give(this.location());
},
js_app: (bp, bl, dev, rp, rl) => {
const build = text(bp, bl);
if (this.onServer) {
this.built = build;
return;
}
const routes = text(rp, rl);
if (this.app?.build === build && this.app.routes === routes && this.app.dev === (dev === 1)) return;
this.app = { ...Runtime.routeTable(routes), build, dev: dev === 1, routes };
if (this.app.posts.length) this.listenForSubmits();
},
js_navigate: (tp, tl, replace, scroll) => {
if (this.onServer) return;
const to = text(tp, tl);
const handler = this.current;
if (handler?.kind !== "handler") throw new Failed(`Router.navigate!("${to}") is a handler's: call it from an event, a timer or an effect's apply, not while computing (render <Navigate> to send the visitor elsewhere as a page renders)`);
handler.writes.push({ navigate: { to, replace: replace === 1, scroll: scroll === 1 } });
},
js_is_routing: () => {
this.touch(true);
if (this.onServer) return 0;
this.track(this.routing);
return this.routing.on ? 1 : 0;
},
js_before_leave: (ptr) => {
this.touch();
if (this.onServer) return this.ex.release(ptr);
const owner = this.current;
if (!owner?.making) {
this.ex.release(ptr);
throw new Failed("Router.use_before_leave! is called in a component or a computation, which its listener goes with: in a handler or an effect's apply, nothing would own it");
}
const id = ++ids;
this.kept.set(id, ptr);
const listener = new Computation(this, { kind: "leave", runner: id, owner, scope: owner.scope ?? {} });
listener.owner = owner;
listener.prevents = false;
this.leaveListeners.add(listener);
this.schedule(listener);
},
js_leave_prevent: (id) => {
const asking = this.current;
if (asking?.leaveProbe) {
if (id === 0) asking.prevented = true;
} else if (this.leaveAsked?.id === id) this.leaveAsked.prevented = true;
},
js_leave_retry: (id, force) => {
if (this.onServer) return;
const handler = this.current;
if (handler?.kind !== "handler") throw new Failed("Leave.retry! is a handler's: call it from an event, a timer or an effect's apply, not while computing");
handler.writes.push({ leaveRetry: { id, force: force === 1 } });
},
js_status: (code) => {
if (this.onServer) this.status = code;
},
js_effect_new: (ptr) => {
this.touch();
if (this.onServer) return this.ex.release(ptr);
const owner = this.current;
if (!owner?.making) {
this.ex.release(ptr);
throw new Failed("create_effect! is made in a component or a computation, not in a handler or an effect's apply: nothing would own it");
}
const effect = new Computation(this, { kind: "reaction", runner: ptr, owner, scope: owner.scope ?? {} });
effect.cleanups = [];
effect.apply = 0;
effect.render = false;
effect.onError = 0;
effect.failure = null;
this.run(effect);
},
js_effect_options: (render, error) => {
const effect = this.current;
if (effect?.kind !== "reaction") return;
effect.render = render === 1;
effect.onError = error;
},
js_cleanup: (ptr) => {
this.touch();
if (this.onServer) return this.ex.release(ptr);
const cleanups = this.cleanupsOf(this.current);
if (!cleanups) {
this.ex.release(ptr);
throw new Failed("on_cleanup! is called in a component, a computation or an effect: in a handler, nothing would ever run it");
}
const id = ++ids;
this.kept.set(id, ptr);
cleanups.push(id);
},
js_flash: (ptr, len) => {
if (!this.onServer) {
if (this.current) this.flashReaders.add(this.current);
return this.give(this.flash);
}
const found = text(ptr, len);
if (found) this.flashed = found;
return this.give(found);
},
js_action: (ptr, len) => {
this.touch();
if (this.onServer) return;
const key = this.actionKey(text(ptr, len));
this.actions.set(key, (this.actions.get(key) ?? 0) + 1);
this.listenForSubmits();
this.cleanupsOf(this.current)?.push(() => {
const left = (this.actions.get(key) ?? 1) - 1;
if (left > 0) this.actions.set(key, left);
else this.actions.delete(key);
});
},
js_submission: (ptr, len) => {
this.touch(true);
if (this.onServer) return this.give("");
const source = this.submissionOf(this.actionKey(text(ptr, len)));
this.track(source);
if (source.cleared) return this.give(CLEARED);
const latest = source.list.at(-1);
return this.give(latest ? submissionJson(latest) : "");
},
js_submissions: (ptr, len) => {
this.touch(true);
if (this.onServer) return this.give("");
const source = this.submissionOf(this.actionKey(text(ptr, len)));
this.track(source);
if (!source.list.length && !source.cleared) return this.give("");
return this.give(`{"cleared":${source.cleared},"list":[${source.list.map((entry) => submissionJson(entry, true)).join(",")}]}`);
},
js_submission_clear: (ptr, len) => {
if (!this.onServer) this.later({ cleared: this.actionKey(text(ptr, len)) });
},
js_submission_drop: (ptr, len, id) => {
if (!this.onServer) this.later({ dropped: this.actionKey(text(ptr, len)), id });
},
js_submit: (mp, ml, up, ul, bp, bl, ip, il) => {
if (this.onServer) return;
const handler = this.current;
const url = text(up, ul);
if (handler?.kind !== "handler") throw new Failed(`use_action!(${url})'s function sends from a handler (an event, a timer, an effect's apply), not while computing`);
handler.writes.push({ submit: { method: text(mp, ml), url, body: text(bp, bl), input: text(ip, il) } });
},
js_revalidate: (ptr, len) => {
if (this.onServer) return;
const keys = JSON.parse(text(ptr, len));
const handler = this.current;
if (handler?.kind !== "handler") throw new Failed("Router.revalidate! reads again from a handler (an event, a timer, an effect's apply), not while computing");
handler.writes.push({ revalidate: keys });
},
js_submission_retry: (ptr, len, id) => {
if (!this.onServer) this.later({ retried: this.actionKey(text(ptr, len)), id });
},
js_optimistic_set: (id, ptr) => {
const handler = this.current;
if (handler?.kind !== "handler") {
this.ex.release(ptr);
throw new Failed("an optimistic value is written in a handler, not while computing");
}
handler.writes.push({ optimistic: { signal: this.signals.get(id), value: ptr } });
},
js_now_millis: () => Date.now(),
js_now_precise: () => performance.timeOrigin + performance.now(),
js_title: (ptr, len) => {
this.touch();
const title = text(ptr, len);
if (this.onServer) {
this.titled = title;
return;
}
const owner = this.current;
const cleanups = this.cleanupsOf(owner);
if (!cleanups) throw new Failed("a <Title> says the title in its own hole: Html.document_title is rocx's to write");
owner.titleSeq ??= ++this.titleSeqs;
this.titles.set(owner, { seq: owner.titleSeq, title });
cleanups.push(() => {
this.titles.delete(owner);
this.titleChanged();
});
this.titleChanged();
},
js_head: (kp, kl, mp, ml) => {
this.touch();
const key = text(kp, kl);
const markup = text(mp, ml);
if (this.onServer) {
this.headed.push({ key, markup });
return;
}
const owner = this.current;
const cleanups = this.cleanupsOf(owner);
if (!cleanups) throw new Failed("a <Meta>, <Link> or <Style> says its element in its own hole: Html.document_head is rocx's to write");
owner.headSeq ??= ++this.headSeqs;
this.heads.set(owner, { seq: owner.headSeq, key, markup });
cleanups.push(() => {
this.heads.delete(owner);
this.headChanged();
});
this.headChanged();
},
js_untrack: (on) => {
const making = this.current?.making;
if (making) making.untracked = Math.max(0, making.untracked + (on ? 1 : -1));
},
js_read_at: (ptr, len) => {
const outer = this.place ?? "";
this.place = text(ptr, len) || null;
return this.give(outer);
},
};
}
cleanupsOf(current) {
return current?.making ? own(current.making, "cleanups") : (current?.cleanups ?? null);
}
cleanUp(cleanups) {
if (!cleanups?.length) return;
for (const cleanup of cleanups.splice(0).reverse()) {
if (typeof cleanup === "function") {
cleanup();
continue;
}
if (!this.kept.has(cleanup)) continue;
this.handle(cleanup, "");
const ptr = this.kept.get(cleanup);
this.kept.delete(cleanup);
if (ptr) this.ex.release(ptr);
}
}
actionKey(url) {
if (typeof location === "undefined") return url;
const resolved = new URL(this.under(url), location.href);
return `${this.unbased(resolved.pathname)}${resolved.search}`;
}
submissionOf(key) {
let source = this.submissions.get(key);
if (!source) this.submissions.set(key, (source = { list: [], cleared: false, observers: new Set() }));
return source;
}
submissionsChanged(source) {
for (const observer of source.observers) this.schedule(observer);
}
listenForSubmits() {
if (this.submitting || typeof this.page?.addEventListener !== "function") return;
this.submitting = (event) => this.submitted(event);
this.page.addEventListener("submit", this.submitting);
}
submitted(event) {
if (event.defaultPrevented) return;
const form = event.target;
if (!form || form.localName !== "form") return;
const submitter = event.submitter ?? null;
const of = (name, attribute) => (submitter?.hasAttribute(attribute) ? submitter.getAttribute(attribute) : form.getAttribute(name)) ?? "";
if (of("method", "formmethod").toLowerCase() !== "post") return;
if (Runtime.reloads(submitter) || Runtime.reloads(form)) return;
const enctype = of("enctype", "formenctype").toLowerCase();
if (enctype === "text/plain") return;
const target = of("target", "formtarget").toLowerCase();
if (target && target !== "_self") return;
const url = new URL(of("action", "formaction"), location.href);
const key = this.formKey(url);
if (key === null) return;
event.preventDefault();
const data = new FormData(form, submitter ?? undefined);
const own = new URLSearchParams([...data].map(([name, value]) => [name, typeof value === "string" ? value : value.name])).toString();
const input = [url.search.slice(1), own].filter(Boolean).join("&");
const plain = !this.actions.has(key);
if (enctype === "multipart/form-data") this.submit(key, url.href, { body: data, input, json: false, plain, form });
else this.submit(key, url.href, { headers: { "content-type": "application/x-www-form-urlencoded" }, body: new URLSearchParams(data).toString(), input, json: false, plain, form });
}
formKey(url) {
if (url.origin !== location.origin) return null;
const base = this.base.slice(0, -1);
if (base && url.pathname !== base && !url.pathname.startsWith(this.base)) return null;
const path = this.unbased(url.pathname);
return this.submittedKey(`${path}${url.search}`) ?? (this.postOf(path) ? path : null);
}
submittedKey(key) {
if (this.actions.has(key)) return key;
let found = null;
for (const known of this.actions.keys()) {
if ((key.startsWith(`${known}?`) || key.startsWith(`${known}&`)) && known.length > (found?.length ?? -1)) found = known;
}
return found;
}
sendAction({ method, url, body, input }) {
const href = typeof location === "undefined" ? this.under(url) : new URL(this.under(url), location.href).href;
const data = this.filesForm(body);
if (data) return this.submit(this.actionKey(url), href, { method, body: data, input, json: true });
const headers = method === "GET" || method === "HEAD" ? {} : { "content-type": "application/json" };
this.submit(this.actionKey(url), href, { method, headers, body, input, json: true });
}
filesForm(json) {
let arg;
try {
arg = JSON.parse(json);
} catch {
return null;
}
if (!arg || typeof arg !== "object" || Array.isArray(arg)) return null;
const file = (value) => (typeof value === "string" ? this.fileOf(value) : null);
const holdsFiles = Object.values(arg).some((value) => file(value) || (Array.isArray(value) && value.length && value.every((item) => file(item))));
if (!holdsFiles) return null;
const data = new FormData();
for (const [name, value] of Object.entries(arg)) {
for (const item of Array.isArray(value) ? value : [value]) {
const found = file(item);
if (found) data.append(name, found, found.name);
else if (item === null) continue;
else if (typeof item === "object") throw new Failed(`an action with a file goes as a form, and its field ${name} is a record, which a form doesn't have`);
else data.append(name, String(item));
}
}
return data;
}
submit(key, href, { method = "POST", headers = {}, body, input, json, plain = false, form = null }) {
const source = this.submissionOf(key);
const entry = { id: ++ids, state: "pending", input, json, status: 0, body: "", form };
entry.request = { href, method, headers, body, plain };
source.list.push(entry);
source.cleared = false;
this.sendSubmission(key, source, entry);
}
sendSubmission(key, source, entry) {
const { href, method, headers, body, plain = false } = entry.request;
const input = entry.input;
const transition = this.transition;
if (transition) {
transition.sent = true;
transition.pending++;
}
this.submissionsChanged(source);
const asked = performance.now();
const navigations = this.navigations;
this.notify("submit", { method, url: key, input, id: entry.id });
const done = (status, said) => {
Object.assign(entry, { state: "done", status, body: said });
if (source.list.includes(entry)) this.submissionsChanged(source);
if (transition && --transition.pending === 0) this.endTransition(transition);
};
const asked_as = plain ? { accept: "text/html,application/xhtml+xml,*/*;q=0.8", "x-rocx-in-place": "1" } : { accept: "application/json", "x-rocx-submission": "1" };
fetch(href, { method, headers: { ...headers, ...asked_as }, body: method === "GET" || method === "HEAD" ? undefined : body }).then(
async (response) => {
const to = response.headers.get("x-rocx-redirect");
if (to !== null || response.redirected) {
this.notify("submitted", { url: key, input, id: entry.id, status: response.status, redirect: to ?? response.url, ms: performance.now() - asked });
this.pages?.clear();
const finish = () => {
done(200, "");
if (!(plain && Runtime.flashStatus(this.flash) >= 400)) Runtime.emptied(entry.form);
if (plain) {
source.list = source.list.filter((each) => each !== entry);
this.submissionsChanged(source);
}
};
if (this.navigations === navigations) {
const before = new Set(this.readers);
const keys = Runtime.revalidating(response.headers.get("x-rocx-revalidate"));
this.refreshed = null;
Promise.resolve(this.navigate(to !== null ? this.urlOf(to) : new URL(response.url), { refresh: true })).then(() => {
const rest = new Set([...before].filter((computation) => !this.refreshed?.has(computation)));
this.revalidate(finish, keys, rest);
});
} else finish();
return;
}
const said = await response.text();
this.notify("submitted", { url: key, input, id: entry.id, status: response.status, body: said, ms: performance.now() - asked });
if (response.status === 200) {
this.revalidate(() => {
done(200, said);
Runtime.emptied(entry.form);
this.refreshRegionsFromServer();
}, Runtime.revalidating(response.headers.get("x-rocx-revalidate")));
} else if (plain) {
this.failAround(entry.form, `${method} ${key}: ${response.status}: ${said}`);
done(response.status, said);
} else {
this.unread(method, key, response.status, said);
done(response.status, said);
}
},
(error) => {
const why = `${method} ${key}: ${error?.message ?? error}`;
this.notify("submitted", { url: key, input, id: entry.id, error: why, ms: performance.now() - asked });
if (plain) this.failAround(entry.form, why);
else this.unread(method, key, 0, error?.message ?? String(error));
done(0, why);
},
);
}
static reloads(element) {
const marked = element?.closest?.("[data-rocx-reload]");
return !!marked && marked.getAttribute("data-rocx-reload") !== "off";
}
static emptied(form) {
if (form?.isConnected && !form.closest("[data-rocx-keep]")) form.reset();
}
static flashStatus(flash) {
try {
return JSON.parse(flash || "null")?.status ?? 0;
} catch {
return 0;
}
}
failAround(node, problem) {
const inside = (boundary) => {
const { start, end } = boundary.range;
return !!node && start.isConnected && (start.compareDocumentPosition(node) & Node.DOCUMENT_POSITION_FOLLOWING) !== 0 && (end.compareDocumentPosition(node) & Node.DOCUMENT_POSITION_PRECEDING) !== 0;
};
let nearest = null;
for (const boundary of this.boundaries.values()) {
if (boundary.failed !== null || !inside(boundary)) continue;
if (!nearest || (nearest.range.start.compareDocumentPosition(boundary.range.start) & Node.DOCUMENT_POSITION_FOLLOWING) !== 0) nearest = boundary;
}
if (nearest) nearest.fail(problem);
else console.error(`rocx: ${problem}, and no <Errored> on the page is around the form to show it`);
}
async refreshRegionsFromServer() {
if (!regionRanges(document).some((range) => range.start.data === "nohydration:read")) return;
try {
const fetched = await this.pageFor(new URL(location.href), {});
const doc = this.appDocument(fetched);
if (doc) this.refreshRegions(doc);
} catch {}
}
unread(method, key, status, why) {
if (this.actions.has(key)) return;
const what = status === 0 ? `had no answer (${why})` : `was refused (${status}: ${why})`;
console.warn(`rocx: ${method} ${key} ${what}, and nothing on the page reads its submissions: use_submission! or use_submissions! shows it`);
}
static revalidating(header) {
if (header === null) return null;
try {
const keys = JSON.parse(header);
return Array.isArray(keys) && keys.every((key) => typeof key === "string") ? keys : null;
} catch {
return null;
}
}
retrySubmission(key, id) {
const source = this.submissionOf(key);
const entry = id === 0 ? (source.cleared ? undefined : source.list.at(-1)) : source.list.find((each) => each.id === id);
if (!entry?.request || entry.state === "pending") return;
Object.assign(entry, { state: "pending", status: 0, body: "" });
this.sendSubmission(key, source, entry);
}
revalidate(done, keys = null, among = null) {
this.pages?.clear();
const named = (key) => {
if (!key.startsWith("GET ")) return false;
if (keys === null) return true;
const url = key.slice(4, key.includes("\n") ? key.indexOf("\n") : undefined);
return keys.some((wanted) => url === wanted || url.startsWith(`${wanted}/`) || url.startsWith(`${wanted}?`));
};
const targets = [...this.readers].filter((computation) => !computation.disposed && (among === null || among.has(computation)) && computation.calls !== null && [...computation.calls.keys()].some(named));
this.notify("revalidate", { reads: targets.length });
if (!targets.length) return done();
let left = targets.length;
const one = () => {
if (--left === 0) done();
};
for (const target of targets) {
(target.revalidating ??= []).push(one);
this.refresh(target);
}
}
openTransition() {
const transition = { pending: 0, sent: false, signals: new Set() };
this.transition = transition;
queueMicrotask(() => {
if (this.transition === transition) this.transition = null;
if (!transition.sent) this.endTransition(transition);
});
return transition;
}
hold({ signal, value }, transition) {
if (!signal || !this.signals.has(signal.id)) return this.ex.release(value);
signal.held ??= { base: signal.value, writes: [] };
signal.held.writes.push({ value, transition });
transition.signals.add(signal);
signal.value = value;
for (const observer of signal.observers) this.schedule(observer);
}
endTransition(transition) {
for (const signal of transition.signals) {
const held = signal.held;
if (!held || !this.signals.has(signal.id)) continue;
const kept = [];
for (const write of held.writes) {
if (write.transition === transition) this.ex.release(write.value);
else kept.push(write);
}
held.writes = kept;
signal.value = kept.at(-1)?.value ?? held.base;
if (!kept.length) signal.held = null;
for (const observer of signal.observers) this.schedule(observer);
}
}
releaseSignal(signal) {
if (!signal.held) return this.ex.release(signal.value);
this.ex.release(signal.held.base);
for (const write of signal.held.writes) this.ex.release(write.value);
}
revalidated(computation) {
const waiting = computation.revalidating;
if (!waiting) return;
computation.revalidating = null;
for (const one of waiting) one();
}
track(source) {
const reader = this.current;
if (!reader?.making || reader.making.untracked > 0) return;
addSource(reader.making, source);
if (this.place && reader.kind === "component" && !this.onServer) this.warnRead(this.place);
}
touch(read = false) {
const making = this.current?.making;
if (making && !(read && making.untracked > 0)) making.live = true;
}
warnRead(place) {
if (this.warned.has(place)) return;
this.warned.add(place);
this.notify("warn", { place });
console.warn(`rocx: ${place} reads a value that changes (a signal, a memo or a prop) in a component's body, once, as the component runs: what it shows won't follow it. Read it where it is used (in markup, a memo, an effect's compute or a handler), or, if one read is what you want, say so: untrack!(|| …)`);
}
later(write) {
if (this.current?.kind === "handler") this.current.writes.push(write);
else this.apply([write]);
}
location() {
if (this.onServer) return Runtime.target(/^\S+ (\S*)/.exec(this.request)?.[1] ?? "/");
return this.committed ?? this.here();
}
here() {
return Runtime.target(typeof location === "undefined" ? "/" : `${this.unbased(location.pathname)}${location.search}`);
}
static target(target) {
const [path, query] = target.split("#")[0].split(/\?(.*)/s);
const trimmed = path.length > 1 ? path.replace(/\/+$/, "") || "/" : path || "/";
return query === undefined ? trimmed : `${trimmed}?${query}`;
}
commitLocation(target) {
if (this.committed === target) return;
this.committed = target;
for (const observer of this.locationSource.observers) this.schedule(observer);
this.markLinks();
}
linkMark(href) {
if (typeof href !== "string" || !href.startsWith("/") || href.startsWith("//")) return null;
const [path, query = ""] = Runtime.target(href).split(/\?(.*)/s);
const [here, asked = ""] = this.location().split(/\?(.*)/s);
if (path === here) return !query || query === asked ? "page" : null;
return !query && path !== "/" && here.startsWith(`${path}/`) ? "true" : null;
}
markLink(element) {
this.links.add(element);
const href = element.getAttribute("href");
const mark = href === null ? null : this.linkMark(this.unbased(href));
const was = element.getAttribute("aria-current");
if (mark === was) return;
element.removeAttribute("aria-current");
if (mark) element.setAttribute("aria-current", mark);
}
markLinks() {
for (const link of this.page?.querySelectorAll?.("a[href]") ?? []) if (this.links.has(link)) this.markLink(link);
}
setRouting(on) {
if (this.routing.on === on) return;
this.routing.on = on;
for (const observer of this.routing.observers) this.schedule(observer);
}
static routeTable(routes) {
const table = JSON.parse(routes);
const parts = (path) => path.split("/").filter(Boolean).map((part) => (/^\[.+\]$/.test(part) ? null : part));
const pages = (table.pages ?? []).map((page) => ({ ...page, parts: parts(page.path) }));
const posts = (table.posts ?? []).map((path) => ({ path, parts: parts(path) }));
return { pages, error: table.error ?? null, posts };
}
static segmentsOf(path) {
try {
return path.split("/").filter(Boolean).map(decodeURIComponent);
} catch {
return null;
}
}
static matched(parts, segments) {
return parts.length === segments.length && parts.every((part, at) => part === null || part === segments[at]);
}
postOf(path) {
const segments = Runtime.segmentsOf(path);
return segments !== null && (this.app?.posts ?? []).some((post) => Runtime.matched(post.parts, segments));
}
routeOf(path) {
if (!this.app) return null;
const segments = Runtime.segmentsOf(path);
if (segments === null) return null;
for (const page of this.app.pages) {
if (!Runtime.matched(page.parts, segments)) continue;
const params = {};
page.path
.split("/")
.filter(Boolean)
.forEach((part, at) => {
if (page.parts[at] === null) params[part.slice(1, -1)] = segments[at];
});
return { page, params };
}
return null;
}
pageCode(level) {
return REACHED;
}
codeOf(route) {
return Promise.all((route?.page.levels ?? []).map((level) => this.pageCode(level)));
}
urlOf(to) {
return new URL(to.startsWith("/") && !to.startsWith("//") ? this.under(to) : to, location.href);
}
listenForNavigation() {
if (this.navigating || !this.app || typeof window === "undefined" || this.page !== document) return;
this.navigating = true;
this.navigation = null;
this.navigations = 0;
this.pages = new Map();
const state = history.state;
this.entryKey = state?.rocx?.key ?? Runtime.entryKey();
this.entryIndex = state?.rocx?.index ?? 0;
if (state?.rocx?.key !== this.entryKey || state?.rocx?.index !== this.entryIndex) history.replaceState({ ...(state && typeof state === "object" ? state : {}), rocx: { key: this.entryKey, index: this.entryIndex } }, "");
if ("scrollRestoration" in history) history.scrollRestoration = "manual";
const kept = this.scrollOf(this.entryKey);
if (kept && !location.hash) window.scrollTo(kept.x, kept.y);
document.addEventListener("click", (event) => this.clicked(event));
document.addEventListener("pointerover", (event) => this.hovered(event));
document.addEventListener("pointerout", (event) => this.unhovered(event));
document.addEventListener("focusin", (event) => event.target?.matches?.(":focus-visible") && this.prefetchLink(this.linkOf(event.target)));
document.addEventListener("touchstart", (event) => this.prefetchLink(this.linkOf(event.target)), { passive: true });
this.watchSight();
document.addEventListener("submit", (event) => this.gotForm?.(event));
window.addEventListener("popstate", (event) => this.popped(event));
window.addEventListener("pagehide", () => this.keepScroll());
}
static entryKey() {
return Math.random().toString(36).slice(2, 10);
}
scrollOf(key) {
try {
const kept = sessionStorage.getItem(`rocx:scroll:${key}`);
return kept ? JSON.parse(kept) : null;
} catch {
return null;
}
}
keepScroll() {
try {
sessionStorage.setItem(`rocx:scroll:${this.entryKey}`, JSON.stringify({ x: window.scrollX, y: window.scrollY }));
} catch {}
}
clicked(event) {
if (event.defaultPrevented || event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
const link = this.linkOf(event.target);
if (!link) return;
event.preventDefault();
this.navigate(link.url, { replace: link.anchor.hasAttribute("replace"), scroll: !link.anchor.hasAttribute("noscroll") });
}
linkOf(node) {
const anchor = node?.closest?.("a");
if (!anchor) return null;
const href = anchor.getAttribute("href") ?? anchor.getAttribute("xlink:href");
if (href === null || anchor.hasAttribute("download")) return null;
if (/(^|\s)external(\s|$)/i.test(anchor.getAttribute("rel") ?? "")) return null;
const target = anchor.getAttribute("target");
if (target && target !== "_self") return null;
const mode = document.documentElement.getAttribute("data-rocx-navigation");
if (mode === "off" || (mode === "explicit" && !anchor.hasAttribute("data-rocx-link"))) return null;
if (Runtime.reloads(anchor)) return null;
const url = new URL(href, document.baseURI);
if (!this.ours(url) || Runtime.samePage(url)) return null;
return { anchor, url };
}
static preloadOf(anchor) {
return anchor.closest("[data-rocx-preload]")?.getAttribute("data-rocx-preload") || "hover";
}
hovered(event) {
const link = this.linkOf(event.target);
if (this.hovering?.anchor === link?.anchor) return;
clearTimeout(this.hovering?.timer);
this.hovering = link && { anchor: link.anchor, timer: setTimeout(() => this.prefetchLink(link), Runtime.REST) };
}
unhovered(event) {
const anchor = this.hovering?.anchor;
if (!anchor || anchor.contains(event.relatedTarget)) return;
clearTimeout(this.hovering.timer);
this.hovering = null;
}
prefetchLink(link) {
if (link && Runtime.preloadOf(link.anchor) !== "off") this.prefetch(link.url);
}
prefetch(url) {
if (!this.navigating || !this.ours(url) || Runtime.documentKey(url) === Runtime.documentKey(new URL(location.href))) return;
const key = Runtime.documentKey(url);
const promise = this.pageFor(url, { preload: true });
const entry = this.pages.get(key);
promise.then(
(fetched) => {
if (!fetched.text.includes(`data-build="${this.app.build}"`) && this.pages.get(key) === entry) this.pages.delete(key);
},
() => {},
);
}
watchSight() {
this.sight?.disconnect();
this.added?.disconnect();
if (typeof IntersectionObserver === "undefined" || !document.querySelector('[data-rocx-preload="viewport"]')) return;
this.sight ??= new IntersectionObserver((entries) => {
for (const entry of entries) {
if (!entry.isIntersecting) continue;
this.sight.unobserve(entry.target);
this.prefetchLink(this.linkOf(entry.target));
}
});
const watch = (root) => {
const anchors = root.localName === "a" ? [root] : [...(root.querySelectorAll?.("a[href]") ?? [])];
for (const anchor of anchors) if (Runtime.preloadOf(anchor) === "viewport") this.sight.observe(anchor);
};
watch(document.documentElement);
this.added ??= new MutationObserver((records) => {
for (const record of records) for (const node of record.addedNodes) if (node.nodeType === 1) watch(node);
});
this.added.observe(document.body, { childList: true, subtree: true });
}
transitionsWanted() {
return typeof document.startViewTransition === "function" && document.documentElement.hasAttribute("data-rocx-transitions") && !reducedMotion();
}
static samePage(url) {
return url.href.includes("#") && url.origin === location.origin && url.pathname === location.pathname && url.search === location.search;
}
ours(url) {
if (url.origin !== location.origin) return false;
const base = this.base.slice(0, -1);
if (base && url.pathname !== base && !url.pathname.startsWith(this.base)) return false;
return this.routeOf(this.unbased(url.pathname)) !== null;
}
popped(event) {
if (this.restoring) {
this.restoring = false;
return;
}
const forced = this.forcing;
this.forcing = false;
const key = event.state?.rocx?.key ?? null;
const index = event.state?.rocx?.index;
if (this.here() === this.committed && !this.navigation) {
if (key) {
this.entryKey = key;
if (typeof index === "number") this.entryIndex = index;
} else {
this.entryIndex++;
history.replaceState({ ...(event.state ?? {}), rocx: { key: this.entryKey, index: this.entryIndex } }, "");
}
return;
}
const url = new URL(location.href);
const delta = typeof index === "number" ? index - this.entryIndex : 0;
if (delta && !forced && !this.mayLeave(url, { delta })) {
this.restoring = true;
history.go(-delta);
return;
}
if (typeof index === "number") this.entryIndex = index;
this.keepScroll();
this.navigate(url, { pop: key ?? Runtime.entryKey(), asked: true });
}
load(url, { replace = false, pop = null, asked = false } = {}) {
if (asked) this.loadAsked = performance.now();
if (pop) location.reload();
else if (replace) location.replace(url.href ?? url);
else location.assign(url.href ?? url);
}
mayLeave(url, { replace = false, scroll = true, delta = 0 } = {}) {
if (!this.leaveListeners.size) return true;
const leave = { id: ++ids, to: Runtime.target(`${this.unbased(url.pathname)}${url.search}`), url, replace, scroll, delta, key: this.entryKey, index: this.entryIndex, prevented: false };
this.leaves.set(leave.id, leave);
while (this.leaves.size > Runtime.LEAVES) this.leaves.delete(this.leaves.keys().next().value);
const outer = this.leaveAsked;
this.leaveAsked = leave;
try {
for (const listener of [...this.leaveListeners]) {
if (listener.disposed) continue;
this.handle(listener.runner, this.leaveEvent(leave), listener.scope, { owner: listener.owner, again: false });
}
} finally {
this.leaveAsked = outer;
}
this.notify("leave", { to: leave.to, delta, prevented: leave.prevented });
return !leave.prevented;
}
leaveEvent(leave) {
const [path, query = ""] = this.location().split(/\?(.*)/s);
return [leave.id, leave.to, path, query, leave.replace ? 1 : 0, leave.scroll ? 1 : 0, leave.delta, leave.prevented ? 1 : 0].join("\n");
}
probeLeave(listener) {
const making = making_();
const probe = {
kind: "handler",
leaveProbe: true,
prevented: false,
runner: listener.runner,
calls: new Map(),
writes: [],
own: 0,
event: this.leaveEvent({ id: 0, to: "", replace: false, scroll: true, delta: 0, prevented: false }),
scope: listener.scope,
owner: listener.owner,
making,
adopt: (child) => own(making, "children").push(child),
};
const previous = this.current;
this.current = probe;
let ok = true;
try {
this.enter(() => this.ex.run(this.kept.get(listener.runner)));
} catch (error) {
if (!(error instanceof NotReady || error instanceof Failed)) throw error;
ok = false;
this.reclaim(error);
} finally {
this.current = previous;
}
for (const write of probe.writes) {
if (write.signal) this.ex.release(write.value);
else if (write.optimistic) this.ex.release(write.optimistic.value);
}
for (const source of listener.sources) source.observers?.delete(listener);
listener.sources = making.sources;
for (const source of listener.sources) (source.observers ??= new Set()).add(listener);
making.cleanups = making.cleanups.filter((cleanup) => typeof cleanup === "function" || (this.releaseKept(cleanup), false));
this.drop(making);
listener.prevents = ok && probe.prevented;
this.guardUnload();
return "ok";
}
retryLeave(id, force) {
const leave = this.leaves.get(id);
if (!leave) return;
queueMicrotask(() => {
if (leave.delta && this.entryKey === leave.key && this.entryIndex === leave.index) {
this.forcing = force;
history.go(leave.delta);
} else this.navigate(leave.url, { replace: leave.replace, scroll: leave.scroll, force });
});
}
guardUnload() {
if (typeof window === "undefined") return;
let wanted = false;
for (const listener of this.leaveListeners) if (listener.prevents) wanted = true;
if (wanted === (this.unloadGuard !== null)) return;
if (wanted) {
this.unloadGuard = (event) => {
if (performance.now() - this.loadAsked < Runtime.ASKED) return;
event.preventDefault();
event.returnValue = "";
};
window.addEventListener("beforeunload", this.unloadGuard);
} else {
window.removeEventListener("beforeunload", this.unloadGuard);
this.unloadGuard = null;
}
}
async navigate(to, { replace = false, scroll = true, pop = null, force = false, asked = false, refresh = false } = {}) {
const url = to instanceof URL ? to : this.urlOf(to);
if (!this.navigating || !this.ours(url)) return this.load(url, { replace, pop, asked });
if (!pop && Runtime.samePage(url)) return this.load(url, { replace });
if (!force && !asked && !this.mayLeave(url, { replace, scroll })) return;
if (!pop && url.href === location.href) replace = true;
if (this.inPlace?.(url, { replace, scroll, pop })) return;
const started = performance.now();
if (!pop) this.keepScroll();
const previous = this.navigation;
if (previous && Runtime.documentKey(previous.url) !== Runtime.documentKey(url)) {
previous.controller.abort();
const key = Runtime.documentKey(previous.url);
if (this.pages.get(key)?.signal === previous.controller.signal) this.pages.delete(key);
}
const navigation = (this.navigation = { id: ++ids, url, controller: new AbortController() });
this.setRouting(true);
this.notify("navigate", { url: url.href });
document.dispatchEvent(new CustomEvent("rocx:navigate", { detail: { url: url.href } }));
let fetched;
try {
fetched = await this.pageFor(url, { signal: navigation.controller.signal });
} catch (error) {
if (this.navigation !== navigation) return;
this.navigation = null;
return this.load(url, { replace, pop, asked: true });
}
if (this.navigation !== navigation) return;
let at = url;
if (fetched.redirected) {
const ended = new URL(fetched.url);
ended.hash = url.hash;
if (!(ended.origin === url.origin && ended.pathname === `${url.pathname}/` && ended.search === url.search)) at = ended;
}
const doc = this.appDocument(fetched);
if (!doc || (at !== url && !this.ours(at))) {
this.navigation = null;
this.pages.delete(Runtime.documentKey(url));
return this.load(at, { replace, pop, asked: true });
}
const stays = refresh && Runtime.documentKey(at) === Runtime.documentKey(new URL(location.href));
if (pop) this.entryKey = pop;
else {
this.entryKey = Runtime.entryKey();
if (!replace) this.entryIndex++;
history[replace ? "replaceState" : "pushState"]({ rocx: { key: this.entryKey, index: this.entryIndex } }, "", at.href);
}
if (pop && history.state?.rocx?.key !== pop) history.replaceState({ ...(history.state ?? {}), rocx: { key: pop, index: this.entryIndex } }, "");
this.navigation = null;
this.navigations++;
try {
const show = () => {
this.commit(doc, Runtime.target(`${this.unbased(at.pathname)}${at.search}`), { refresh });
this.afterNavigate?.(doc);
if (!stays) this.scrolled(at, { pop, scroll });
};
if (this.transitionsWanted()) {
this.notify("transition", { url: at.href });
const transition = document.startViewTransition(show);
transition.ready.catch(() => {});
transition.finished.catch(() => {});
await transition.updateCallbackDone;
} else show();
if (!stays) {
this.focused(at);
this.announce(at);
}
this.watchSight();
const ms = performance.now() - started;
this.notify("navigated", { url: at.href, ms });
document.dispatchEvent(new CustomEvent("rocx:navigated", { detail: { url: at.href, ms } }));
} finally {
this.holdingEffects = false;
this.wake();
}
}
static documentKey(url) {
return url.href.split("#")[0];
}
pageFor(url, { signal = undefined, preload = false } = {}) {
const key = Runtime.documentKey(url);
const cached = this.pages.get(key);
if (cached && (cached.at === null || performance.now() - cached.at <= Runtime.FRESH)) return cached.promise;
const entry = { at: null, promise: null, signal };
const asked = performance.now();
this.notify("fetch", { method: "GET", url: key, body: "", preload });
const document = fetch(key, { headers: { accept: "text/html", "x-rocx-navigate": preload ? "preload" : "1" }, signal, credentials: "same-origin", priority: preload ? "low" : "auto" }).then(async (response) => {
const text = await response.text();
this.notify("fetched", { method: "GET", url: key, status: response.status, body: "", ms: performance.now() - asked, preload });
return { status: response.status, url: response.url, redirected: response.redirected, type: response.headers.get("content-type") ?? "", text };
});
entry.promise = Promise.all([document, this.codeOf(this.routeOf(this.unbased(url.pathname)))]).then(
([fetched]) => {
entry.at = performance.now();
return fetched;
},
(error) => {
if (this.pages.get(key) === entry) this.pages.delete(key);
throw error;
},
);
this.pages.delete(key);
this.pages.set(key, entry);
while (this.pages.size > Runtime.CACHE) this.pages.delete(this.pages.keys().next().value);
return entry.promise;
}
appDocument(fetched) {
if (!/^text\/html\b/i.test(fetched.type)) return null;
const doc = new DOMParser().parseFromString(fetched.text, "text/html");
const start = [...doc.querySelectorAll("script[data-rocx][src]")].find((script) => /(^|\/)rocx\/start\.js$/.test(script.getAttribute("src")));
if (!start || start.getAttribute("data-build") !== this.app.build) return null;
return doc;
}
commit(doc, target, { refresh = false } = {}) {
const flashBefore = this.flash;
const before = [...this.readers];
this.flash = "";
this.seed(doc);
this.refreshing = refresh;
const hydrating = (this.hydrating = { asked: [] });
this.arriving = doc;
this.holdingEffects = true;
this.setRouting(false);
try {
if (this.committed === target) for (const observer of this.locationSource.observers) this.schedule(observer);
this.commitLocation(target);
if (this.root && (this.remakeRoot?.(target) ?? true)) this.schedule(this.root);
this.flush();
this.refreshKept(before, flashBefore);
} finally {
this.refreshing = false;
this.arriving = null;
this.hydrating = null;
this.answers.clear();
}
if (this.strict && hydrating.asked.length) throw new Error(`rocx: navigating to ${target}, the page asked the server again for ${hydrating.asked.join(", ")}: its document didn't carry it`);
}
refreshKept(before, flashBefore) {
const refreshed = new Set();
let again = false;
for (const computation of before) {
if (computation.disposed || !computation.calls) continue;
const reads = [...computation.calls.keys()].filter((key) => key.startsWith("GET "));
if (!reads.length || !reads.every((key) => this.answers.has(key))) continue;
refreshed.add(computation);
if (reads.every((key) => computation.calls.get(key)?.value === this.answers.get(key))) continue;
for (const key of reads) computation.calls.delete(key);
this.schedule(computation);
again = true;
}
for (const reader of this.flashReaders) {
if (reader.disposed) this.flashReaders.delete(reader);
else if (this.flash !== flashBefore) {
this.schedule(reader);
again = true;
}
}
this.refreshed = refreshed;
if (again) this.flush();
}
scrolled(url, { pop, scroll }) {
if (pop) {
const kept = this.scrollOf(pop);
window.scrollTo(kept?.x ?? 0, kept?.y ?? 0);
return;
}
if (!scroll) return;
const hash = url.hash ? decodeURIComponent(url.hash.slice(1)) : "";
const target = hash ? (document.getElementById(hash) ?? document.getElementsByName(hash)[0]) : null;
if (target) target.scrollIntoView();
else window.scrollTo(0, 0);
}
focused(url) {
const auto = document.body?.querySelector("[autofocus]");
if (auto) return auto.focus();
const hash = url.hash ? decodeURIComponent(url.hash.slice(1)) : "";
const target = hash ? document.getElementById(hash) : null;
if (target && target.tabIndex >= 0) return target.focus({ preventScroll: true });
const body = document.body;
if (!body) return;
const tabindex = body.getAttribute("tabindex");
body.tabIndex = -1;
body.focus({ preventScroll: true });
if (tabindex === null) body.removeAttribute("tabindex");
else body.setAttribute("tabindex", tabindex);
const selection = getSelection();
if (selection && selection.type !== "Range") selection.removeAllRanges();
}
announce(url) {
let announcer = this.announcer;
if (!announcer?.isConnected) {
announcer = this.announcer = document.createElement("div");
announcer.setAttribute("data-rocx", "");
announcer.setAttribute("aria-live", "assertive");
announcer.setAttribute("aria-atomic", "true");
Object.assign(announcer.style, { position: "absolute", width: "1px", height: "1px", margin: "-1px", padding: "0", border: "0", overflow: "hidden", clip: "rect(0 0 0 0)", clipPath: "inset(50%)", whiteSpace: "nowrap" });
document.body.append(announcer);
}
announcer.textContent = document.title || this.unbased(url.pathname);
}
reconcileHead(head, from) {
const live = [...head.childNodes].filter((node) => !hosts(node));
const wanted = [...from.childNodes].filter((node) => !hosts(node));
const kept = new Set();
const plan = [];
let at = 0;
for (const node of wanted) {
let found = null;
for (let i = at; i < live.length; i++) {
if (live[i].isEqualNode(node)) {
found = live[i];
at = i + 1;
break;
}
}
if (found) kept.add(found);
plan.push(found ?? node);
}
const sheet = (node) => node.nodeType === 1 && node.localName === "link" && /(^|\s)stylesheet(\s|$)/i.test(node.getAttribute("rel") ?? "");
const going = live.filter((node) => !kept.has(node));
const coming = [];
let next = null;
for (let i = plan.length - 1; i >= 0; i--) {
const node = plan[i];
if (kept.has(node)) {
next = node;
continue;
}
const made = node.nodeType === 1 && node.localName === "script" ? Runtime.inertCopy(node) : document.importNode(node, true);
if (sheet(made)) coming.push(made);
head.insertBefore(made, next ?? Runtime.headEnd(head));
next = made;
}
const sheets = going.filter(sheet);
for (const node of going) if (!sheets.includes(node)) node.remove();
if (sheets.length) {
if (!coming.length) for (const node of sheets) node.remove();
else {
let left = coming.length;
const done = () => {
if (--left === 0) for (const node of sheets) node.remove();
};
for (const made of coming) {
made.addEventListener("load", done, { once: true });
made.addEventListener("error", done, { once: true });
}
}
}
const own = head.querySelector("title[data-rocx]");
const first = [...head.querySelectorAll("title")].find((title) => !hosts(title));
if (own && first && own.compareDocumentPosition(first) & Node.DOCUMENT_POSITION_PRECEDING) head.insertBefore(own, first);
}
static headEnd(head) {
let end = null;
for (let node = head.lastChild; node && hosts(node) && node.localName !== "title"; node = node.previousSibling) end = node;
return end;
}
static inertCopy(script) {
const made = inertScript();
for (const { name, value } of script.attributes) made.setAttribute(name, value);
made.textContent = script.textContent;
return made;
}
static attributesFrom(element, node, from) {
const names = new Set();
for (const [kind, name] of node.a) {
if (kind === "v" || kind === "vo" || kind === "o" || kind === "oo" || kind === "f" || kind === "fo") names.add(name);
else if (kind === "ci" || kind === "co") names.add("class");
else if (kind === "sv" || kind === "so") names.add("style");
}
for (const name of names) {
const value = from?.getAttribute(name) ?? null;
if (value === null) element.removeAttribute(name);
else if (element.getAttribute(name) !== value) element.setAttribute(name, value);
}
}
fetchFor(method, url, headerLines, body) {
const tracked = !(this.current?.making?.untracked > 0);
if (tracked) this.touch();
if (this.onServer) {
const found = this.given?.find(([named, asked]) => named === `${method} ${url}` && asked === body);
if (!found) throw new Failed(`599: ${method} ${url} wasn't answered as the server rendered the page`);
if (!this.current?.scope?.region && !this.recorded.includes(found)) this.recorded.push(found);
return this.give(found[2]);
}
const asking = this.current;
const key = `${method} ${url}\n${body}`;
let answer = asking.calls?.get(key);
if (!answer && this.answers.has(key)) {
answer = { state: "ok", value: this.answers.get(key) };
(asking.calls ??= new Map()).set(key, answer);
this.notify("seeded", { method, url, value: answer.value });
}
if (!answer) {
this.hydrating?.asked.push(`${method} ${url}`);
answer = { state: "pending" };
const headers = Object.fromEntries(headerLines.split("\n").filter(Boolean).map((line) => [line.slice(0, line.indexOf(": ")), line.slice(line.indexOf(": ") + 2)]));
const asked = performance.now();
this.notify("fetch", { method, url, body });
answer.promise = fetch(this.under(url), { method, headers, body: method === "GET" || method === "HEAD" ? undefined : body }).then(
async (response) => {
const text = await response.text();
this.notify("fetched", { method, url, status: response.status, body: text, ms: performance.now() - asked });
return Object.assign(answer, { state: "ok", value: JSON.stringify({ status: response.status, body: text }) });
},
(error) => {
this.notify("fetched", { method, url, error: String(error.message ?? error), ms: performance.now() - asked });
return Object.assign(answer, { state: "failed", error: `${method} ${url}: ${error.message ?? error}` });
},
);
(asking.calls ??= new Map()).set(key, answer);
}
if (asking.used !== undefined) (asking.used ??= new Set()).add(key);
if (method === "GET" && tracked && READERS.has(asking.kind)) this.readers.add(asking);
if (answer.state === "pending") throw new NotReady(answer.promise);
if (answer.state === "failed") throw new Failed(answer.error);
return this.give(answer.value);
}
under(url) {
return url.startsWith("/") && !url.startsWith("//") ? `${this.base}${url.slice(1)}` : url;
}
written(name, value) {
return this.base !== "/" && (name === "href" || name === "src" || name === "action") && typeof value === "string" ? this.under(value) : value;
}
unbased(path) {
const base = this.base.slice(0, -1);
const under = !base || (path !== base && !path.startsWith(this.base)) ? path : path.slice(base.length) || "/";
return under.endsWith("/index.html") ? under.slice(0, -"index.html".length) : under;
}
async listenTo(url, ptr) {
const id = ++ids;
this.kept.set(id, ptr);
const scope = this.current?.scope ?? null;
const owner = this.owner();
const controller = new AbortController();
let stopped = false;
const stop = () => {
if (stopped) return;
stopped = true;
controller.abort();
if (!this.kept.has(id)) return;
this.kept.delete(id);
this.ex.release(ptr);
};
this.cleanupsOf(this.current)?.push(() => {
if (!stopped) this.notify("unlisten", { url });
stop();
});
const tell = (heard) => {
if (stopped) return;
this.notify("heard", { url, heard });
if (this.kept.has(id)) this.handle(id, JSON.stringify(heard), scope, { owner });
};
const done = (heard) => {
tell(heard);
stop();
};
this.notify("listen", { url });
try {
const response = await fetch(this.under(url), { headers: { accept: "text/event-stream" }, signal: controller.signal });
if (!response.ok || !(response.headers.get("content-type") ?? "").startsWith("text/event-stream")) {
return done({ Refused: [response.status, await response.text()] });
}
const reader = response.body.pipeThrough(new TextDecoderStream()).getReader();
let buffer = "";
for (;;) {
const { value, done: over } = await reader.read();
if (over) return done({ Failed: "the stream was cut off before it ended" });
buffer += value.replaceAll("\r\n", "\n");
for (let end = buffer.indexOf("\n\n"); end >= 0; end = buffer.indexOf("\n\n")) {
const lines = buffer.slice(0, end).split("\n");
buffer = buffer.slice(end + 2);
const field = (name) => lines.filter((line) => line.startsWith(`${name}:`)).map((line) => line.slice(name.length + 1).replace(/^ /, ""));
if (field("event")[0] === "end") {
reader.cancel();
return done("Ended");
}
const data = field("data");
if (data.length) tell({ Event: data.join("\n") });
}
}
} catch (error) {
done({ Failed: String(error?.message ?? error) });
}
}
startTimer(ms, repeat, ptr) {
if (this.onServer) {
this.ex.release(ptr);
return 0;
}
const id = ++ids;
this.kept.set(id, ptr);
const cleanups = this.cleanupsOf(this.current);
if (cleanups)
cleanups.push(() => {
this.stopTimer(id);
this.releaseKept(id);
});
else if (this.current?.owner?.made) own(this.current.owner.ownMade?.() ?? this.current.owner.made, "kept").push(id);
const scope = this.current?.scope ?? null;
const owner = this.owner();
const fire = () => {
if (!this.kept.has(id)) return;
if (repeat) return this.handle(id, "", scope, { owner });
this.timers.delete(id);
this.handle(id, "", scope, { owner, done: () => this.releaseKept(id) });
};
this.timers.set(id, { repeat, handle: repeat ? setInterval(fire, ms) : setTimeout(fire, ms) });
return id;
}
clearTimer(id) {
this.stopTimer(id);
if (this.current?.kind === "handler") queueMicrotask(() => this.releaseKept(id));
else this.releaseKept(id);
}
stopTimer(id) {
const timer = this.timers.get(id);
if (!timer) return;
this.timers.delete(id);
if (timer.repeat) clearInterval(timer.handle);
else clearTimeout(timer.handle);
}
releaseKept(id) {
const ptr = this.kept.get(id);
if (!ptr) return;
this.kept.delete(id);
this.ex.release(ptr);
}
owner() {
return this.current?.making ? this.current : (this.current?.owner ?? null);
}
readOnce(reader) {
if (this.onServer || reader.making?.untracked > 0) return;
const level = reader.scope?.level;
if (level) (this.onceLevels ??= new Set()).add(level);
else this.rootOnce = true;
}
readsOnce() {
if (this.rootOnce) return true;
for (const level of this.onceLevels ?? []) if (!level.disposed) return true;
return false;
}
failedBoundaries() {
return [...this.boundaries.values()].filter((boundary) => boundary.failed !== null && boundary.fallback && !boundary.fallback.disposed && boundary.range.start.isConnected);
}
inPlace(url, { replace = false, scroll = true, pop = null } = {}) {
const target = Runtime.target(`${this.unbased(url.pathname)}${url.search}`);
const now = this.location();
this.leftFrom = now;
if (target === now || target.split("?")[0] !== now.split("?")[0]) return false;
if (this.readsOnce() || this.failedBoundaries().length) return false;
const previous = this.navigation;
if (previous) {
previous.controller.abort();
const key = Runtime.documentKey(previous.url);
if (this.pages.get(key)?.signal === previous.controller.signal) this.pages.delete(key);
}
this.navigation = null;
this.setRouting(false);
const started = performance.now();
this.notify("navigate", { url: url.href, inPlace: true });
document.dispatchEvent(new CustomEvent("rocx:navigate", { detail: { url: url.href } }));
if (pop) {
this.entryKey = pop;
if (history.state?.rocx?.key !== pop) history.replaceState({ ...(history.state ?? {}), rocx: { key: pop, index: this.entryIndex } }, "");
} else {
this.keepScroll();
this.entryKey = Runtime.entryKey();
if (!replace) this.entryIndex++;
history[replace ? "replaceState" : "pushState"]({ rocx: { key: this.entryKey, index: this.entryIndex } }, "", url.href);
}
this.commitLocation(target);
this.flush();
this.navigations++;
this.scrolled(url, { pop, scroll });
this.watchSight();
const ms = performance.now() - started;
this.notify("navigated", { url: url.href, ms, inPlace: true });
document.dispatchEvent(new CustomEvent("rocx:navigated", { detail: { url: url.href, ms } }));
return true;
}
remakeRoot(target) {
const previous = this.leftFrom;
this.leftFrom = null;
this.rootKept = !(this.rootOnce || (target === previous && !this.refreshing));
if (!this.rootKept) {
if (this.rootOnce) this.madeAnew("the root layout");
this.rootOnce = false;
this.onceLevels = new Set();
this.remade = [];
return true;
}
const failed = this.failedBoundaries();
this.remakeLevels();
if (failed.length) {
this.flush();
for (const boundary of failed) if (boundary.failed !== null && boundary.range.start.isConnected) boundary.retry();
}
return false;
}
remakeLevels() {
const levels = this.onceLevels ?? [];
this.onceLevels = new Set();
this.remade = [];
for (const level of levels) {
if (level.disposed) continue;
this.remade.push({ level, key: level.holds });
level.holds = REMADE;
this.schedule(level);
}
}
madeAnew(what) {
this.notify("remade", { level: what });
if (this.app?.dev) console.info(`rocx: ${what} was made anew: it read Router.location! once, in its body, and the location changed. Read it where it is used (in markup, or a memo) for it to be kept across navigations (D-040)`);
}
afterNavigate(doc) {
for (const { level, key } of this.remade ?? []) {
if (!level.disposed && level.holds === key) this.madeAnew(typeof key === "string" ? key.slice(1) : "a <Show>'s part");
}
this.remade = [];
this.enhancedFrom(doc);
if (this.rootKept) this.refreshRegions(doc);
if (this.rootKept && doc.head && document.head) this.reconcileHead(document.head, doc.head);
this.rootKept = false;
this.forgetSubmissions();
}
enhancedFrom(doc) {
const made = new Map();
for (const image of doc.querySelectorAll("img[srcset]")) {
const src = image.getAttribute("src");
if (!made.has(src)) made.set(src, []);
made.get(src).push(image);
}
if (!made.size) return;
const counted = new Map();
for (const image of document.querySelectorAll("img")) {
const added = this.enhancedImages.get(image);
if (!added) continue;
const src = image.getAttribute("src");
const at = counted.get(src) ?? 0;
counted.set(src, at + 1);
const from = made.get(src)?.[at];
if (!from) continue;
for (const name of added) {
const value = from.getAttribute(name);
if (value !== null && image.getAttribute(name) !== value) image.setAttribute(name, value);
}
}
}
refreshRegions(doc) {
const live = regionRanges(document);
const fetched = regionRanges(doc);
if (live.length !== fetched.length) {
console.warn(`rocx: the page has ${live.length} <NoHydration> regions and its document ${fetched.length}: they are left as they are`);
return;
}
live.forEach((range, at) => {
if (range.start.data !== fetched[at].start.data) range.start.data = fetched[at].start.data;
const now = inside(range);
const then = inside(fetched[at]);
if (now.length === then.length && now.every((node, i) => node.isEqualNode(then[i]))) return;
const fragment = document.createDocumentFragment();
for (const node of then) {
const script = node.nodeType === 1 && node.localName === "script";
const made = script ? Runtime.inertCopy(node) : document.importNode(node, true);
if (!script && made.nodeType === 1) for (const inner of made.querySelectorAll("script")) inner.replaceWith(Runtime.inertCopy(inner));
fragment.append(made);
}
replaceRange(range, fragment);
});
}
forgetSubmissions() {
for (const [key, source] of this.submissions) {
if (this.actions.has(key)) continue;
const pending = source.list.filter((entry) => entry.state === "pending");
if (pending.length === source.list.length) continue;
source.list = pending;
this.submissionsChanged(source);
if (!pending.length && !source.observers.size) this.submissions.delete(key);
}
}
gotForm(event) {
if (event.defaultPrevented) return;
const form = event.target;
if (form?.localName !== "form") return;
const submitter = event.submitter ?? null;
const of = (name, attribute) => (submitter?.hasAttribute(attribute) ? submitter.getAttribute(attribute) : form.getAttribute(name)) ?? "";
if ((of("method", "formmethod").toLowerCase() || "get") !== "get") return;
const target = of("target", "formtarget");
if (target && target !== "_self") return;
const mode = document.documentElement.getAttribute("data-rocx-navigation");
if (mode === "off" || (mode === "explicit" && !form.hasAttribute("data-rocx-link"))) return;
if (Runtime.reloads(submitter) || Runtime.reloads(form)) return;
const url = new URL(of("action", "formaction") || location.href, document.baseURI);
const data = new FormData(form, submitter ?? undefined);
url.search = new URLSearchParams([...data].map(([name, value]) => [name, typeof value === "string" ? value : value.name])).toString();
url.hash = "";
if (!this.ours(url)) return;
event.preventDefault();
this.navigate(url, { replace: form.hasAttribute("replace"), scroll: !form.hasAttribute("noscroll") });
}
run(computation) {
if (computation.disposed) return;
if (computation.kind === "leave") return this.probeLeave(computation);
if (computation.recheck) {
computation.recheck = false;
if (!this.answersChanged(computation)) return;
}
this.cleanUp(computation.made.cleanups);
const making = making_();
const previous = this.current;
this.current = computation;
computation.making = making;
computation.used = null;
this.stats.runs++;
let out;
let outcome = "ok";
let failure = null;
let waited = null;
try {
out = this.enter(() => (computation.kind === "root" ? this.ex.mount() : this.ex.run(computation.runner)));
} catch (error) {
if (error instanceof NotReady) {
outcome = "pending";
waited = error;
this.stats.aborts++;
error.wait.then(() => this.schedule(computation));
} else if (error instanceof Failed) {
outcome = "failed";
failure = error;
} else throw error;
} finally {
this.current = previous;
}
for (const source of computation.sources) source.observers?.delete(computation);
computation.sources = computation.untracked ? NONE : making.sources;
for (const source of computation.sources) (source.observers ??= new Set()).add(computation);
if (outcome === "ok") {
computation.making = making;
try {
this.settle(computation, out);
} finally {
const old = computation.made;
computation.made = !madeNothing(making) ? spare(making) : inert(making) ? MADE_NONE : MADE_READ;
computation.queries = making.queries;
computation.making = null;
this.drop(old);
}
if (computation.calls !== null) for (const key of computation.calls.keys()) if (!computation.used?.has(key)) computation.calls.delete(key);
computation.scope.loading?.done(computation);
} else {
computation.making = null;
this.drop(making);
if (computation.kind === "memo") {
if (computation.next) this.ex.release(computation.next);
computation.next = 0;
}
this.reclaim(failure ?? waited);
if (outcome === "pending" && computation.kind === "root") {
throw new Error("rocx: a component read a value that isn't in yet outside its markup: read it in a hole ({…}), which waits");
}
if (outcome === "pending") {
if (computation.kind !== "reaction") computation.scope.loading?.wait(computation);
} else this.failed(computation, failure);
}
if (computation.kind === "memo") {
computation.refreshing = outcome === "pending" && computation.value !== 0 && computation.state !== "failed";
this.restale(computation);
if (outcome !== "pending") this.recheckReaders(computation);
}
if (outcome !== "pending") this.revalidated(computation);
return outcome;
}
isStatic(computation, outcome) {
return outcome === "ok" && inert(computation.made);
}
forget(computation, owner) {
if (computation.made.kept.length) return;
computation.disposed = true;
const children = owner ? (owner.making ?? owner.made).children : null;
if (children?.at(-1) === computation) children.pop();
}
restale(memo) {
if (memo.disposed) return;
let stale = memo.refreshing;
if (memo.state !== "failed") for (const source of memo.sources) if (source.kind === "memo" && source.stale) stale = true;
if (stale === memo.stale) return;
memo.stale = stale;
this.recheckReaders(memo);
for (const observer of memo.observers ?? NONE) if (observer.kind === "memo") this.restale(observer);
}
pending(memos) {
return memos.some((memo) => memo.stale);
}
recheckReaders(memo) {
for (const reader of memo.pending.observers) {
if (reader.disposed || this.dirty.has(reader)) continue;
reader.recheck = true;
this.dirty.add(reader);
this.wake();
}
}
answersChanged(computation) {
for (const { probe, memos, answer } of computation.queries ?? []) {
const ptr = this.kept.get(probe);
if (!ptr) return true;
const now = this.probe(ptr);
if (this.pending(now) !== answer || now.length !== memos.length || now.some((memo, i) => memo !== memos[i])) return true;
}
return false;
}
probe(ptr) {
const probe = { kind: "probe", memos: new Set(), calls: new Map() };
const previous = this.current;
this.current = probe;
try {
this.enter(() => this.ex.run(ptr));
} catch (error) {
if (!(error instanceof NotReady || error instanceof Failed)) throw error;
this.reclaim(error);
} finally {
this.current = previous;
}
return [...probe.memos];
}
settle(computation, out) {
const { kind, target, name } = computation;
if (kind === "selector") {
const was = computation.key;
computation.key = out;
computation.settle?.();
computation.settled = computation.settle = null;
if (was !== null && was !== out) {
for (const key of [was, out]) for (const observer of computation.keys.get(key)?.observers ?? NONE) this.schedule(observer);
if (computation.keys.size > 2 * (computation.swept ?? 0) + 64) {
for (const [key, source] of computation.keys) if (!source.observers?.size) computation.keys.delete(key);
computation.swept = computation.keys.size;
}
}
return;
}
if (kind === "memo") {
const quiet = computation.same && computation.state === "ok" && computation.value !== 0;
computation.same = false;
if (computation.value) this.ex.release(computation.value);
computation.value = computation.next;
computation.next = 0;
computation.state = "ok";
computation.settle?.();
computation.settled = computation.settle = null;
if (!quiet) for (const observer of computation.observers ?? NONE) this.schedule(observer);
return;
}
if (kind === "reaction") {
computation.apply = Number(out);
computation.failure = null;
if (computation.render) {
this.due.delete(computation);
this.applyReaction(computation);
return;
}
this.due.add(computation);
this.wake();
return;
}
if (kind === "show") return this.settleShow(computation, JSON.parse(out));
if (kind === "for") return this.settleFor(computation, JSON.parse(out));
if (kind === "transition") return this.setTransition(target, name, JSON.parse(out));
if (kind === "key") return this.keys.set(target, JSON.parse(out));
if (kind === "drag") return this.setDrag(target, name, JSON.parse(out));
if (kind === "text" || kind === "attr" || kind === "flag" || kind === "class" || kind === "optional" || kind === "style") {
const value = kind === "attr" || kind === "optional" ? this.written(name, JSON.parse(out)) : JSON.parse(out);
if (computation.adopting && kind === "text") {
computation.adopting = false;
target.data = value;
return;
}
if (kind === "attr" && name === "value" && "value" in target && !target.hasAttribute("value")) {
target.setAttribute(name, value);
target.value = value;
return;
}
if (computation.attrs && (kind === "class" || ((kind === "attr" || kind === "optional") && (name === "class" || name === "style")))) {
if (kind === "class") {
let toggles = this.classToggles.get(target);
if (!toggles) this.classToggles.set(target, (toggles = new Map()));
toggles.set(name, value);
const computed = computedOf(computation.attrs, "class");
if (computed && this.computedClasses.has(target)) return this.writeWhole(target, "class", this.wholeClass(target, computation.attrs), kind, name);
if (target.classList.contains(name) === value) return;
this.stats.patches++;
this.notify("patch", { kind, name, node: target });
target.classList.toggle(name, value);
if (value && !computed) this.writeWhole(target, "class", this.wholeClass(target, computation.attrs));
return;
}
if (name === "class") {
const old = this.computedClasses.get(target) ?? "";
this.computedClasses.set(target, value);
return this.writeWhole(target, "class", this.wholeClass(target, computation.attrs, old), kind, name);
}
this.computedStyles.set(target, value);
return this.writeWhole(target, "style", this.wholeStyle(target, computation.attrs), kind, name);
}
if (kind === "style") {
let raw = this.rawStyles.get(target);
if (!raw) this.rawStyles.set(target, (raw = new Map()));
raw.set(name, value);
}
const now =
kind === "text"
? target.data
: kind === "attr"
? name === "value" && "value" in target
? target.value
: target.getAttribute(name)
: kind === "optional"
? (target.getAttribute(name) ?? "")
: kind === "style"
? target.style.getPropertyValue(name).trim()
: kind === "class"
? target.classList.contains(name)
: name in target
? target[name]
: target.hasAttribute(name);
if (now === value) return;
this.stats.patches++;
this.notify("patch", { kind, name, node: target });
if (kind === "text") target.data = value;
else if (kind === "attr") {
target.setAttribute(name, value);
if (name === "src") this.enhancedImages.get(target)?.forEach((added) => target.removeAttribute(added));
if (name === "value" && "value" in target) target.value = value;
}
else if (kind === "optional") value === "" ? target.removeAttribute(name) : target.setAttribute(name, value);
else if (kind === "style") value === "" ? target.style.removeProperty(name) : target.style.setProperty(name, value);
else if (kind === "class") target.classList.toggle(name, value);
else {
target.toggleAttribute(name, value);
if (name in target) target[name] = value;
}
if (name === "href" && this.links.has(target)) this.markLink(target);
return;
}
if (target?.document) return this.settleDocument(computation, JSON.parse(out));
if (kind === "html" && computation.text && !computation.peek && this.settleHoleText(computation, JSON.parse(out))) return;
if (kind === "html" || kind === "root") {
const nodes = answered(JSON.parse(out));
if (computation.peek) {
computation.peeked = nodes;
return;
}
if (computation.adopting) {
computation.adopting = false;
const cursor = new Cursor(target.start.nextSibling);
for (const node of nodes) this.adopt(node, computation, computation.scope, cursor);
cursor.end(target.end);
return;
}
this.stats.patches++;
this.notify("patch", { kind, name, node: target.start.parentNode });
this.measure();
const fragment = document.createDocumentFragment();
for (const node of nodes) fragment.append(this.build(node, computation, computation.scope));
replaceRange(target, fragment);
}
}
settleHoleText(computation, parsed) {
const nodes = answered(parsed);
const text = computation.target;
const value = loneText(nodes);
if (value !== null) {
if (computation.adopting) {
computation.adopting = false;
if (text.data !== value) {
this.stats.patches++;
this.notify("patch", { kind: "text", name: null, node: text });
text.data = value;
}
return true;
}
if (text.data === value) return true;
this.stats.patches++;
this.notify("patch", { kind: "text", name: null, node: text });
text.data = value;
return true;
}
const start = document.createComment("html");
const end = document.createComment("/html");
text.before(start);
text.after(end);
computation.target = { start, end };
computation.text = false;
computation.adopting = false;
return false;
}
failed(computation, failure) {
const memo = computation.kind === "memo" ? computation : failure.memo;
computation.scope.loading?.done(computation);
if (computation.kind === "memo") {
computation.state = "failed";
computation.error = failure.message;
computation.settle?.();
computation.settled = computation.settle = null;
for (const observer of computation.observers ?? NONE) this.schedule(observer);
return;
}
if (computation.kind === "reaction" && computation.onError) {
computation.failure = failure.message;
this.due.add(computation);
this.wake();
return;
}
if (computation.scope.errored) computation.scope.errored.fail(failure.message, memo);
else console.error(`rocx: ${failure.message} (no <Errored> around it)`);
}
drop(made) {
for (let i = made.children.length - 1; i >= 0; i--) this.dispose(made.children[i]);
this.cleanUp(made.cleanups);
for (const id of made.kept) {
this.stopTimer(id);
const ptr = this.kept.get(id);
this.kept.delete(id);
if (ptr) this.ex.release(ptr);
}
for (const id of made.signals ?? []) {
const signal = this.signals.get(id);
if (!signal) continue;
this.signals.delete(id);
this.releaseSignal(signal);
}
}
dispose(computation) {
if (!computation || computation.disposed) return;
computation.disposed = true;
this.readers.delete(computation);
this.revalidated(computation);
for (const source of computation.sources) {
source.observers?.delete(computation);
if (source.selector && !source.observers?.size) source.selector.keys.delete(source.key);
}
computation.scope.loading?.done(computation);
if (computation.kind === "leave") {
this.leaveListeners.delete(computation);
this.releaseKept(computation.runner);
this.guardUnload();
}
if (computation.kind === "reaction") {
this.due.delete(computation);
this.cleanUp(computation.cleanups);
this.ex.release(computation.runner);
}
this.drop(computation.made);
if (computation.part) this.dispose(computation.part);
if (computation.list) this.dropList(computation.list);
if (computation.kind === "selector") {
this.selectors.delete(computation.id);
this.ex.release(computation.runner);
}
if (computation.kind === "memo") {
this.memos.delete(computation.id);
if (computation.value) this.ex.release(computation.value);
if (computation.next) this.ex.release(computation.next);
this.ex.release(computation.runner);
}
}
schedule(computation) {
if (computation.disposed) return;
computation.recheck = false;
this.dirty.add(computation);
this.wake();
}
wake() {
if (!this.flushing) {
this.flushing = true;
queueMicrotask(() => this.flush());
}
}
flush() {
this.inFlush = true;
for (;;) {
if (this.dirty.size) this.run(this.dirty.take());
else if (this.due.size && !this.holdingEffects) this.applyReaction(this.due.take());
else break;
}
this.inFlush = false;
this.flushing = false;
if (this.measured) this.glide();
if (this.entering.length) this.playEntering();
if (this.titlesDirty) this.showTitle();
if (this.headsDirty) this.showHead();
if (this.calling.length) this.callEffects();
}
titleChanged() {
this.titlesDirty = true;
if (!this.flushing) {
this.flushing = true;
queueMicrotask(() => this.flush());
}
}
showTitle() {
this.titlesDirty = false;
if (typeof document === "undefined") return;
let top = null;
for (const entry of this.titles.values()) if (!top || entry.seq > top.seq) top = entry;
let element = document.head?.querySelector("title[data-rocx]") ?? null;
if (!top) return element?.remove();
if (!element) {
element = document.createElement("title");
element.setAttribute("data-rocx", "");
const head = document.head ?? document.documentElement;
head.insertBefore(element, head.querySelector("title"));
}
if (element.textContent !== top.title) element.textContent = top.title;
}
headChanged() {
this.headsDirty = true;
this.wake();
}
static headsOf(entries) {
const last = new Map();
for (const entry of entries) if (entry.key) last.set(entry.key, entry);
return entries.filter((entry) => !entry.key || last.get(entry.key) === entry);
}
showHead() {
this.headsDirty = false;
if (typeof document === "undefined" || !document.head) return;
const wanted = Runtime.headsOf([...this.heads.values()].sort((a, b) => a.seq - b.seq));
const have = [...document.head.children].filter((node) => node.hasAttribute("data-rocx") && node.localName !== "title" && node.localName !== "script");
const template = document.createElement("template");
wanted.forEach((entry, at) => {
template.innerHTML = entry.markup;
const made = template.content.firstElementChild;
if (!made) return;
const old = have[at];
if (old?.isEqualNode(made)) return;
if (old) old.replaceWith(made);
else document.head.append(made);
});
for (const extra of have.slice(wanted.length)) extra.remove();
}
static headed(markup, heads) {
const shown = Runtime.headsOf(heads);
const end = markup.indexOf("</head>");
if (!shown.length || end < 0) return markup;
return `${markup.slice(0, end)}${shown.map((entry) => entry.markup).join("")}${markup.slice(end)}`;
}
callEffects() {
const calls = this.calling;
this.calling = [];
for (const { effect: name, arg } of calls) {
this.notify("effect", { name, arg });
const effect = name.startsWith("rocx:") ? this.builtins[name] : (this.effects[name] ?? globalThis.rocxEffects?.[name]);
if (typeof effect !== "function") {
const plugin = /^([a-z0-9-]+)\.[^.]/.exec(name)?.[1];
const said = plugin ? `the ${plugin} plugin's script registers it: is the ${plugin} plugin in the app's plugins?` : `give the runtime one (Runtime.load(wasm, { effects: { ${name}(arg) {…} } }))`;
console.error(`rocx: no effect is called ${name}: ${said}`);
continue;
}
try {
effect(JSON.parse(arg), this.toEffects);
} catch (error) {
console.error(`rocx: the effect ${name} failed:`, error);
}
}
}
applyReaction(effect) {
if (effect.disposed) return;
const failure = effect.failure;
const box = failure !== null ? effect.onError : effect.apply;
if (!this.kept.has(box)) return;
effect.failure = null;
this.cleanUp(effect.cleanups);
this.notify("apply", { id: effect.id, failure });
this.handle(box, failure ?? "", effect.scope, { owner: effect, cleanups: effect.cleanups });
}
refresh(memo) {
memo.calls?.clear();
if (memo.state === "failed") {
memo.state = "pending";
memo.error = null;
}
this.schedule(memo);
}
ownWrite(handler, signal) {
const writes = handler.writes;
for (let at = writes.length - 1; at >= 0; at--) {
const write = writes[at];
if (write.signal === signal) return write.value;
if (write.optimistic?.signal === signal) return write.optimistic.value;
}
return undefined;
}
apply(writes) {
const transition = writes.some((write) => write.optimistic) ? this.openTransition() : null;
for (const write of writes) {
if (write.optimistic) this.hold(write.optimistic, transition);
else if (write.revalidate) this.revalidate(() => {}, write.revalidate);
else if (write.retried !== undefined) this.retrySubmission(write.retried, write.id);
else if (write.signal) {
const { signal, value } = write;
if (!this.signals.has(signal.id)) {
this.ex.release(value);
continue;
}
this.ex.release(signal.value);
signal.value = value;
for (const observer of signal.observers) this.schedule(observer);
} else if (write.refresh) this.refresh(write.refresh);
else if (write.retry) write.retry.retry();
else if (write.effect) {
this.calling.push(write);
if (!this.flushing) {
this.flushing = true;
queueMicrotask(() => this.flush());
}
} else if (write.cleared !== undefined) {
const source = this.submissionOf(write.cleared);
source.list.pop();
source.cleared = true;
this.submissionsChanged(source);
} else if (write.dropped !== undefined) {
const source = this.submissionOf(write.dropped);
source.list = source.list.filter((entry) => entry.id !== write.id);
this.submissionsChanged(source);
} else if (write.submit) this.sendAction(write.submit);
else if (write.navigate) this.navigate(write.navigate.to, write.navigate);
else if (write.leaveRetry) this.retryLeave(write.leaveRetry.id, write.leaveRetry.force);
}
}
handle(runner, event, scope = null, { owner = null, cleanups = null, done = null, again = true } = {}) {
const handler = { kind: "handler", runner, calls: new Map(), writes: [], own: 0, event, scope, owner, cleanups };
const go = () => {
const previous = this.current;
this.current = handler;
handler.writes = [];
handler.own = 0;
const mark = cleanups?.length ?? 0;
try {
this.enter(() => this.ex.run(this.kept.get(handler.runner)));
} catch (error) {
for (const write of handler.writes) {
if (write.signal) this.ex.release(write.value);
else if (write.optimistic) this.ex.release(write.optimistic.value);
}
if (cleanups) {
this.current = previous;
this.cleanUp(cleanups.splice(mark));
}
if (error instanceof NotReady || error instanceof Failed) this.reclaim(error);
if (error instanceof NotReady) {
this.stats.aborts++;
if (again) {
error.wait.then(() => this.kept.has(handler.runner) && go());
return;
}
if (this.app?.dev) console.warn("rocx: a Router.use_before_leave! listener waited for the server: the navigation couldn't wait for it, and went on unless it was stopped before. Decide from what the page has (a signal, a memo already in)");
done?.();
return;
}
if (error instanceof Failed) {
console.error(`rocx: a handler failed: ${error.message}`);
done?.();
return;
}
throw error;
} finally {
this.current = previous;
}
this.apply(handler.writes);
done?.();
};
go();
}
part(nodes, scope, range, adopting) {
const owner = new Computation(this, { kind: "boundary", owner: null, scope });
if (adopting) {
const cursor = new Cursor(range.start.nextSibling);
for (const node of nodes) this.adopt(node, owner, scope, cursor);
cursor.end(range.end);
} else {
const fragment = document.createDocumentFragment();
for (const node of nodes) fragment.append(this.build(node, owner, scope));
replaceRange(range, fragment);
}
return owner;
}
settleShow(computation, holds) {
if (computation.holds === holds) return;
const adopting = computation.adopting;
computation.adopting = false;
const first = computation.holds === undefined;
computation.holds = holds;
if (!first && !adopting) this.measure();
const { node, target, scope } = computation;
const outs = first || adopting ? [] : this.transitioned(target, "out");
if (outs.length) {
const going = { start: target.start, end: document.createComment("/leaving") };
target.start = document.createComment("show");
target.end.before(going.end, target.start);
this.keep(() => this.dispose(computation.part));
this.leave(going, outs);
} else this.dispose(computation.part);
const level = node.b ? scope : { ...scope, level: computation };
if (holds && node.with) {
const made = new Computation(this, { kind: "html", runner: this.kept.get(node.with), owner: null, scope: level, target });
made.adopting = adopting;
made.untracked = true;
made.choosing = Boolean(node.b);
computation.part = made;
this.run(made);
} else computation.part = this.part(holds ? node.c : [node.fallback], level, target, adopting);
if (!first && !adopting) this.entered(target);
if (!adopting && this.observer) this.notify("show", { holds, nodes: inside(target) });
}
settleFor(computation, entries) {
const list = computation.list;
const { target, scope, node } = computation;
const adopting = computation.adopting;
computation.adopting = false;
const later = computation.settled === true;
computation.settled = true;
if (later && !adopting && (entries.length !== list.rows.size || entries.some(({ k }, index) => list.indexes.get(k)?.value !== index || !list.rows.has(k)))) this.measure();
const cursor = adopting ? new Cursor(target.start.nextSibling) : null;
const kept = computation.making.kept;
if (kept !== NONE) {
const runners = new Set();
for (const { r } of entries) if (r) runners.add(r);
let left = 0;
for (const id of kept) if (!runners.has(id)) kept[left++] = id;
kept.length = left;
}
const rows = new Map();
const was = new Array(entries.length).fill(-1);
entries.forEach(({ k, r }, index) => {
let row = list.rows.get(k);
if (row) {
if (r) {
this.ex.release(this.kept.get(r));
this.kept.delete(r);
}
const at = list.indexes.get(k);
if (!detached(row.range)) was[index] = at.value;
if (at.value !== index) {
at.value = index;
for (const observer of at.observers ?? NONE) this.schedule(observer);
}
} else {
list.indexes.set(k, { value: index, observers: null });
const range = adopting ? { start: cursor.comment("row"), end: cursor.closing("row") } : makeRange("row");
row = { key: k, runner: r, range, fresh: !adopting };
row.computation = new Computation(this, { kind: "html", runner: this.kept.get(r), owner: null, scope, target: range });
row.computation.adopting = adopting;
row.computation.untracked = true;
this.run(row.computation);
if (later && !adopting) this.entered(range);
if (adopting) cursor.node = range.end.nextSibling;
}
rows.set(k, row);
});
const going = [];
for (const [key, row] of list.rows) if (!rows.has(key)) going.push(row);
if (!rows.size && going.length > 1 && !this.keeping && going.every((row) => !detached(row.range) && !this.transitioned(row.range, "out").length)) {
for (const row of going) this.dropRow(list, row, false, false);
clearRange(target);
} else for (const row of going) this.dropRow(list, row, true);
for (const [key, item] of list.items) {
if (!rows.has(key)) {
this.ex.release(item.value);
list.items.delete(key);
}
}
list.rows = rows;
if (adopting) {
if (!rows.size) {
computation.fallbackRange = { start: cursor.comment("fallback"), end: cursor.closing("fallback") };
computation.part = this.part([node.fallback], scope, computation.fallbackRange, true);
}
return;
}
if (rows.size) {
this.dispose(computation.part);
computation.part = null;
if (computation.fallbackRange) {
removeRange(computation.fallbackRange);
computation.fallbackRange = null;
}
} else if (!computation.fallbackRange) {
computation.fallbackRange = makeRange("fallback");
target.end.before(computation.fallbackRange.fragment);
computation.part = this.part([node.fallback], scope, computation.fallbackRange, false);
}
const order = [...rows.values()];
const stays = steady(was);
const placed = [];
let next = target.end;
for (let index = order.length - 1; index >= 0; index--) {
const row = order[index];
if (!stays[index]) {
next.before(detached(row.range) ? (row.range.fragment ?? collectRange(row.range)) : collectRange(row.range));
row.range.fragment = null;
this.stats.patches++;
placed.push(row);
}
next = row.range.start;
}
if (this.observer) {
for (let index = placed.length - 1; index >= 0; index--) {
const row = placed[index];
this.notify("row", { what: row.fresh ? "made" : "moved", key: row.key, nodes: inside(row.range) });
}
}
for (const row of order) row.fresh = false;
}
dropRow(list, row, animated = false, remove = true) {
this.notify("row", { what: "dropped", key: row.key, nodes: [] });
const outs = animated && !this.keeping ? this.transitioned(row.range, "out") : [];
if (outs.length) this.keep(() => this.dispose(row.computation));
else this.dispose(row.computation);
this.ex.release(this.kept.get(row.runner));
this.kept.delete(row.runner);
list.indexes.delete(row.key);
if (outs.length) this.leave(row.range, outs);
else if (!this.keeping && remove) removeRange(row.range);
}
dropList(list) {
for (const row of list.rows.values()) this.dropRow(list, row);
for (const item of list.items.values()) this.ex.release(item.value);
list.items.clear();
list.rows.clear();
}
setTransition(element, way, spec) {
let own = this.transitions.get(element);
if (!own) this.transitions.set(element, (own = { in: null, out: null, move: null }));
if (way === "move") {
own.move = spec;
this.gliders.add(element);
return;
}
if (way !== "out") own.in = spec;
if (way !== "in") own.out = spec;
this.animates = true;
}
transitioned(range, way) {
const found = [];
if (!this.animates) return found;
const visit = (first, end) => {
let depth = 0;
for (let node = first; node && node !== end; node = node.nextSibling) {
if (node.nodeType === 8) {
if (OWN_PARTS.has(node.data)) depth++;
else if (depth > 0 && OWN_PARTS.has(node.data.slice(1)) && node.data.startsWith("/")) depth--;
continue;
}
if (depth > 0 || node.nodeType !== 1) continue;
const spec = this.transitions.get(node)?.[way];
if (spec) found.push([node, spec]);
if (node.firstChild) visit(node.firstChild, null);
}
};
visit(range.start.nextSibling, range.end);
return found;
}
keep(release) {
const keeping = this.keeping;
this.keeping = true;
try {
release();
} finally {
this.keeping = keeping;
}
}
entered(range) {
for (const entry of this.transitioned(range, "in")) this.entering.push(entry);
}
playEntering() {
const entering = this.entering;
this.entering = [];
for (const [element, spec] of entering) if (element.isConnected) this.play(element, spec, "in");
}
leave(range, outs) {
range.start.data = "leaving";
range.end.data = "/leaving";
this.leaving.set(range.start, range);
for (const node of inside(range)) {
this.leavingNodes.set(node, range);
if (node.nodeType !== 1) continue;
node.setAttribute("inert", "");
node.setAttribute("aria-hidden", "true");
node.style?.setProperty("pointer-events", "none");
}
let gone = false;
const go = () => {
if (gone) return;
gone = true;
this.leaving.delete(range.start);
removeRange(range);
};
range.finish = () => {
for (const animation of playing) animation.cancel();
go();
};
const playing = outs.map(([element, spec]) => this.play(element, spec, "out")).filter(Boolean);
if (!playing.length) return go();
Promise.all(playing.map((animation) => animation.finished.catch(() => {}))).then(go);
setTimeout(go, Math.max(...outs.map(([, spec]) => spec.ms + spec.delay)) + 1000);
}
play(element, spec, way) {
if (typeof element.animate !== "function" || reducedMotion()) return null;
const fixed = {};
if (spec.origin) fixed.transformOrigin = spec.origin;
if (element.namespaceURI === SVG) fixed.transformBox = "fill-box";
const hidden = { ...fixed };
for (const [property, value] of spec.h) hidden[property.startsWith("--") ? property : camel(property)] = value;
try {
return element.animate([{ ...hidden, offset: 0 }, { ...fixed, offset: 1 }], {
duration: spec.ms,
delay: spec.delay,
easing: spec.easing || "ease-out",
direction: way === "out" ? "reverse" : "normal",
fill: way === "out" ? "forwards" : "backwards",
});
} catch {
return null;
}
}
measure() {
if (this.measured || !this.inFlush || !this.gliders.size || typeof document === "undefined") return;
const still = reducedMotion();
this.measured = new Map();
this.measuredIn = new Map();
for (const element of this.gliders) {
if (!element.isConnected) continue;
this.measured.set(element, still ? null : element.getBoundingClientRect());
this.measuredIn.set(element, this.lifted.has(element) ? null : element.parentElement);
}
}
leavingRangeOf(element) {
for (let node = element; node; node = node.parentNode) {
const range = this.leavingNodes.get(node);
if (range) return range;
}
return null;
}
glide() {
const before = this.measured;
const parents = this.measuredIn;
this.measured = this.measuredIn = null;
const still = reducedMotion();
const went = new Map();
for (const [element, box] of before) {
if (!box || (element.isConnected && !this.leavingRangeOf(element))) continue;
const key = this.keys.get(element);
if (key !== undefined) went.set(key, { element, box });
}
const moves = [];
const origins = new Map();
for (const element of this.gliders) {
if (!element.isConnected) {
if (element.getRootNode().nodeType !== 11) this.gliders.delete(element);
continue;
}
if (still || this.leavingRangeOf(element)) continue;
let box = before.get(element);
if (box === undefined) {
const key = this.keys.get(element);
const pair = key === undefined ? undefined : went.get(key);
if (!pair) continue;
went.delete(key);
box = pair.box;
origins.set(element, pair.element);
this.entering = this.entering.filter(([entering]) => entering !== element);
this.leavingRangeOf(pair.element)?.finish();
}
if (box) moves.push([element, box]);
}
if (!moves.length) return;
for (const [element] of moves) {
this.glides.get(element)?.cancel();
this.lifted.get(element)?.();
}
const boxes = moves.map(([element]) => element.getBoundingClientRect());
const moving = new Map();
moves.forEach(([element, box], index) => {
const to = boxes[index];
const dx = box.left - to.left;
const dy = box.top - to.top;
const resized = Math.abs(box.width - to.width) >= 0.5 || Math.abs(box.height - to.height) >= 0.5;
if (Math.abs(dx) >= 0.5 || Math.abs(dy) >= 0.5 || resized) moving.set(element, { dx, dy, resized, from: box, to });
});
const clips = new Map();
for (const [element, { dx, dy, resized, from, to }] of moving) {
let carried = false;
for (let parent = element.parentElement; parent && !carried; parent = parent.parentElement) carried = moving.has(parent);
if (carried || typeof element.animate !== "function") continue;
const spec = this.transitions.get(element)?.move ?? {};
const was = parents.get(origins.get(element) ?? element);
const lifted = this.crosses(element, from, was, clips) ? this.lift(element, to) : null;
try {
const animation = element.animate(this.glideFrames(element, from, to, resized, lifted ? { was, clips } : null), {
duration: spec.ms ?? 250,
delay: spec.delay ?? 0,
easing: spec.easing || "ease-out",
fill: "backwards",
});
this.glides.set(element, animation);
animation.finished.then(
() => {
lifted?.();
if (this.glides.get(element) === animation) this.glides.delete(element);
},
() => lifted?.(),
);
this.notify("glide", { node: element, dx, dy, width: from.width / (to.width || 1), height: from.height / (to.height || 1), key: this.keys.get(element), lifted: Boolean(lifted) });
} catch {
lifted?.();
}
}
}
glideFrames(element, from, to, resized, lifted) {
let sx = 1;
let sy = 1;
let ox = 0;
let oy = 0;
if (resized && to.width > 0 && to.height > 0) {
sx = from.width / to.width;
sy = from.height / to.height;
[ox, oy] = getComputedStyle(element).transformOrigin.split(" ").map((each) => parseFloat(each) || 0);
}
const tx = from.left - to.left - ox * (1 - sx);
const ty = from.top - to.top - oy * (1 - sy);
const first = { translate: `${tx}px ${ty}px` };
const last = { translate: "0px 0px" };
if (sx !== 1 || sy !== 1) {
first.scale = `${sx} ${sy}`;
last.scale = "1 1";
}
if (lifted) {
const shown = (box, clip, sx, sy) =>
clip ? [Math.max(0, clip.top - box.top) / sy, Math.max(0, box.right - clip.right) / sx, Math.max(0, box.bottom - clip.bottom) / sy, Math.max(0, clip.left - box.left) / sx] : [0, 0, 0, 0];
const before = shown(from, lifted.was?.isConnected ? this.clipping(lifted.was, lifted.clips)?.rect : null, sx, sy);
const after = shown(to, this.clipping(element.parentElement, lifted.clips)?.rect, 1, 1);
if ([...before, ...after].some((inset) => inset > 0)) {
first.clipPath = `inset(${before.map((inset) => `${inset}px`).join(" ")})`;
last.clipPath = `inset(${after.map((inset) => `${inset}px`).join(" ")})`;
}
}
return [first, last];
}
clipping(node, clips) {
if (!node || node.nodeType !== 1 || node === this.page.documentElement || node === this.page.body) return null;
if (clips.has(node)) return clips.get(node);
const outer = this.clipping(node.parentElement, clips);
const style = getComputedStyle(node);
let found = outer;
if (style.overflowX !== "visible" || style.overflowY !== "visible" || /paint|strict|content/.test(style.contain)) {
const own = node.getBoundingClientRect();
const rect = outer ? { left: Math.max(own.left, outer.rect.left), top: Math.max(own.top, outer.rect.top), right: Math.min(own.right, outer.rect.right), bottom: Math.min(own.bottom, outer.rect.bottom) } : own;
found = { box: node, rect };
}
clips.set(node, found);
return found;
}
crosses(element, from, was, clips) {
if (!(element instanceof HTMLElement)) return false;
const now = this.clipping(element.parentElement, clips);
if (!now) return false;
const { rect } = now;
if (from.left >= rect.left - 0.5 && from.top >= rect.top - 0.5 && from.right <= rect.right + 0.5 && from.bottom <= rect.bottom + 0.5) return false;
return !was?.isConnected || this.clipping(was, clips)?.box !== now.box;
}
lift(element, to) {
const style = getComputedStyle(element);
const width = element.offsetWidth;
const height = element.offsetHeight;
const holder = this.page.createElement(element.localName);
holder.setAttribute("aria-hidden", "true");
holder.setAttribute("data-rocx-lifted", "");
const display = style.display === "inline" ? "inline-block" : style.display;
holder.style.cssText = `display: ${display}; box-sizing: border-box; width: ${width}px; height: ${height}px; margin: ${style.marginTop} ${style.marginRight} ${style.marginBottom} ${style.marginLeft}; padding: 0; border: 0; flex: none; grid-area: ${style.gridArea}; visibility: hidden; list-style: none`;
element.before(holder);
const fixed = { position: "fixed", left: `${to.left}px`, top: `${to.top}px`, right: "auto", bottom: "auto", width: `${width}px`, height: `${height}px`, margin: "0px", "max-width": "none", "max-height": "none", "box-sizing": "border-box", "z-index": "2147483647" };
const layered = this.holdsFixed(element) && typeof element.showPopover === "function" && !element.hasAttribute("popover");
if (layered) for (const name of POPOVER_LOOK) fixed[name] = style.getPropertyValue(name);
const own = Object.keys(fixed).map((name) => [name, element.style.getPropertyValue(name), element.style.getPropertyPriority(name)]);
for (const [name, value] of Object.entries(fixed)) element.style.setProperty(name, value, "important");
if (layered) {
element.setAttribute("popover", "manual");
element.showPopover();
} else {
const seen = element.getBoundingClientRect();
if (Math.abs(seen.left - to.left) >= 0.5 || Math.abs(seen.top - to.top) >= 0.5) {
element.style.setProperty("left", `${2 * to.left - seen.left}px`, "important");
element.style.setProperty("top", `${2 * to.top - seen.top}px`, "important");
}
}
let back = false;
const putBack = () => {
if (back) return;
back = true;
if (this.lifted.get(element) === putBack) this.lifted.delete(element);
holder.remove();
if (layered) {
if (element.matches(":popover-open")) element.hidePopover();
element.removeAttribute("popover");
}
for (const [name, value, priority] of own) {
if (value) element.style.setProperty(name, value, priority);
else element.style.removeProperty(name);
}
};
this.lifted.set(element, putBack);
return putBack;
}
holdsFixed(element) {
for (let node = element.parentElement; node && node !== this.page.documentElement; node = node.parentElement) {
const style = getComputedStyle(node);
if (style.transform !== "none" || (style.translate && style.translate !== "none") || (style.scale && style.scale !== "none") || (style.rotate && style.rotate !== "none") || style.perspective !== "none") return true;
if (style.filter !== "none" || (style.backdropFilter && style.backdropFilter !== "none")) return true;
if (/layout|paint|strict|content/.test(style.contain) || (style.containerType && style.containerType !== "normal")) return true;
if (/transform|perspective|filter|translate|scale|rotate/.test(style.willChange)) return true;
}
return false;
}
build(node, owner, scope) {
switch (node.t) {
case "s":
case "raw":
return document.createTextNode(node.v);
case "doctype":
return document.createDocumentFragment();
case "x": {
const text = document.createTextNode("");
const computation = new Computation(this, { kind: "text", runner: this.kept.get(node.r), owner, scope, target: text });
computation.adopting = Boolean(scope.rcdata);
if (this.isStatic(computation, this.run(computation))) this.forget(computation, owner);
return text;
}
case "h":
case "l": {
const computation = new Computation(this, { kind: "html", runner: this.kept.get(node.r), owner, scope, target: null });
computation.peek = true;
const outcome = this.run(computation);
computation.peek = false;
const nodes = computation.peeked;
computation.peeked = null;
if (this.isStatic(computation, outcome)) {
const fragment = document.createDocumentFragment();
for (const child of nodes) fragment.append(this.build(child, computation, scope));
return fragment;
}
const range = makeRange(node.t === "h" ? "html" : "list");
computation.target = range;
if (nodes) {
this.stats.patches++;
this.notify("patch", { kind: "html", name: null, node: range.start.parentNode });
this.measure();
const fragment = document.createDocumentFragment();
for (const child of nodes) fragment.append(this.build(child, computation, scope));
range.end.before(fragment);
}
return range.fragment;
}
case "hx": {
const computation = new Computation(this, { kind: "html", runner: this.kept.get(node.r), owner, scope, target: null });
computation.hole = true;
computation.peek = true;
const outcome = this.run(computation);
computation.peek = false;
const nodes = computation.peeked;
computation.peeked = null;
const value = nodes ? loneText(nodes) : null;
if (this.isStatic(computation, outcome)) {
if (value !== null) {
const text = document.createTextNode("");
if (value !== "" && !scope.rcdata) {
this.stats.patches++;
this.notify("patch", { kind: "text", name: null, node: text });
}
text.data = value;
this.forget(computation, owner);
return text;
}
const fragment = document.createDocumentFragment();
for (const child of nodes) fragment.append(this.build(child, computation, scope));
return fragment;
}
if (value !== null) {
const text = document.createTextNode("");
computation.target = text;
computation.text = true;
if (value !== "" && !scope.rcdata) {
this.stats.patches++;
this.notify("patch", { kind: "text", name: null, node: text });
}
text.data = value;
return text;
}
const range = makeRange("html");
computation.target = range;
if (nodes) {
this.stats.patches++;
this.notify("patch", { kind: "html", name: null, node: range.start.parentNode });
this.measure();
const fragment = document.createDocumentFragment();
for (const child of nodes) fragment.append(this.build(child, computation, scope));
range.end.before(fragment);
}
return range.fragment;
}
case "f": {
const fragment = document.createDocumentFragment();
for (const child of node.c) fragment.append(this.build(child, owner, scope));
return fragment;
}
case "e":
return this.element(node, owner, scope);
case "tpl":
if (node.k) this.templates[node.s] = this.skeleton(node.k, scope);
return this.instantiate(this.templates[node.s], node.p, owner, scope);
case "loading": {
const loading = new Loading();
loading.range = makeRange("loading");
const inner = { ...scope, loading };
loading.children = document.createDocumentFragment();
for (const child of node.c) loading.children.append(this.build(child, owner, inner));
loading.built = true;
if (loading.waiting.size === 0) loading.reveal();
else replaceRange(loading.range, this.build(node.fallback, owner, scope));
return loading.range.fragment;
}
case "show":
case "for": {
const range = makeRange(node.t);
const computation = new Computation(this, { kind: node.t, runner: this.kept.get(node.r), owner, scope, target: range });
computation.node = node;
if (node.t === "for") computation.list = this.lists.get(node.id);
this.run(computation);
return range.fragment;
}
case "errored": {
const range = makeRange("errored");
const errored = new Errored(this, { runner: this.kept.get(node.r), nodes: node.c, owner, scope, range });
range.end.before(errored.build());
return range.fragment;
}
case "c": {
const { computation, nodes } = this.component(node, owner, scope);
const fragment = document.createDocumentFragment();
for (const child of nodes) fragment.append(this.build(child, computation, scope));
return fragment;
}
case "ctx": {
const fragment = document.createDocumentFragment();
for (const child of node.c) fragment.append(this.build(child, owner, provided(scope, node)));
return fragment;
}
case "nh":
return this.region();
case "listen":
this.listenOn(node, owner, scope);
return document.createDocumentFragment();
default:
throw new Error(`rocx: unknown node ${node.t}`);
}
}
region() {
const kept = this.keptRegions?.shift();
if (kept) return kept;
if (this.arriving) return makeRange("nohydration").fragment;
console.warn("rocx: a <NoHydration> the server didn't render here is empty: what is inside is the server's, and the browser has no copy of it");
return makeRange("nohydration").fragment;
}
keepingRegions(root, build) {
const outer = this.keptRegions;
this.keptRegions = serverRegions(root);
try {
return build();
} finally {
this.keptRegions = outer;
}
}
element(given, owner, scope) {
const node = writable(given, this);
if (!node) return document.createDocumentFragment();
const element = node.tag === "script" ? inertScript() : node.tag === "svg" || scope.svg ? document.createElementNS(SVG, node.tag) : document.createElement(node.tag);
const classes = [];
for (const [kind, name, value] of node.a) {
if (name === "class" && (kind === "v" || (kind === "o" && value !== ""))) classes.push(value);
else if (kind === "ci" && value) classes.push(name);
}
if (classes.length) element.setAttribute("class", classes.join(" "));
for (const [kind, name, value] of node.a) {
if (kind === "v" && name !== "class") element.setAttribute(name, this.written(name, value));
else if (kind === "o" && value !== "" && name !== "class") element.setAttribute(name, this.written(name, value));
else if (kind === "f") element.toggleAttribute(name, value);
else if (kind === "sv" && value) element.style.setProperty(name, value);
}
this.bind(element, node, owner, scope);
this.styled(element, node);
Runtime.inOrder(element, node);
if (node.tag === "a" && !ownsCurrent(node)) this.markLink(element);
const inside = within(node, scope);
for (const child of node.c) element.append(this.build(child, owner, inside));
return element;
}
skeleton(node, scope) {
const slots = [];
const links = [];
const root = this.skeletal(node, scope, [], slots, links);
return { root, slots, links };
}
skeletal(node, scope, path, slots, links) {
if (node.t === "s") return document.createTextNode(node.v);
if (node.t !== "e") {
slots.push({ path, svg: Boolean(scope.svg) });
return document.createComment("");
}
const element = node.tag === "svg" || scope.svg ? document.createElementNS(SVG, node.tag) : document.createElement(node.tag);
const written = { tag: node.tag, a: node.a.filter(([kind]) => kind !== "?"), c: [] };
const classes = [];
for (const [, name, value] of written.a) if (name === "class") classes.push(value);
if (classes.length) element.setAttribute("class", classes.join(" "));
for (const [, name, value] of written.a) if (name !== "class") element.setAttribute(name, this.written(name, value));
Runtime.inOrder(element, written);
if (written.a.length !== node.a.length) slots.push({ path, node });
if (node.tag === "a") links.push({ path, own: ownsCurrent(written), slot: written.a.length !== node.a.length ? slots.length - 1 : -1 });
const inside = within(node, scope);
node.c.forEach((child, index) => element.append(this.skeletal(child, inside, [...path, index], slots, links)));
return element;
}
instantiate(template, parts, owner, scope) {
const root = template.root.cloneNode(true);
const { slots, links } = template;
const find = (path) => {
let found = root;
for (const index of path) found = found.childNodes[index];
return found;
};
const nodes = new Array(slots.length);
for (let i = 0; i < slots.length; i++) nodes[i] = find(slots[i].path);
const linked = links.length ? links.map((link) => find(link.path)) : null;
const filled = links.length ? new Array(slots.length) : null;
let at = 0;
for (let i = 0; i < slots.length; i++) {
const slot = slots[i];
if (slot.node) {
let own = [];
const a = slot.node.a.map((attr) => (attr[0] === "?" ? (own[own.length] = parts[at++]) : attr));
const node = writable({ tag: slot.node.tag, a, c: [] }, this);
if (node.a !== a) own = own.filter((attr) => node.a.includes(attr));
this.fill(nodes[i], node, own, owner, scope);
if (filled) filled[i] = node;
} else {
nodes[i].replaceWith(this.build(parts[at++], owner, slot.svg && !scope.svg ? { ...scope, svg: true } : scope));
}
}
if (linked) links.forEach((link, i) => !link.own && !(link.slot >= 0 && ownsCurrent(filled[link.slot])) && this.markLink(linked[i]));
return root;
}
fill(element, node, own, owner, scope) {
if (own.some(([kind, name]) => kind === "ci" || ((kind === "v" || kind === "o") && name === "class"))) {
const classes = [];
for (const [kind, name, value] of node.a) {
if (name === "class" && (kind === "v" || (kind === "o" && value !== ""))) classes.push(value);
else if (kind === "ci" && value) classes.push(name);
}
if (classes.length) element.setAttribute("class", classes.join(" "));
}
for (const [kind, name, value] of own) {
if (kind === "v" && name !== "class") element.setAttribute(name, this.written(name, value));
else if (kind === "o" && value !== "" && name !== "class") element.setAttribute(name, this.written(name, value));
else if (kind === "f") element.toggleAttribute(name, value);
else if (kind === "sv" && value) element.style.setProperty(name, value);
}
this.bind(element, node, owner, scope);
this.styled(element, node);
Runtime.inOrder(element, node);
}
wholeClass(element, attrs, old = "") {
const toggles = this.classToggles.get(element);
const ordered = [];
const ours = new Set(words(old));
for (const [kind, name, value] of attrs) {
if (name === "class" && (kind === "v" || kind === "o" || kind === "vo" || kind === "oo")) {
const own = kind === "v" || kind === "o" ? value : (this.computedClasses.get(element) ?? "");
for (const word of words(own)) ours.add(word);
if (kind === "v" || kind === "vo" || own !== "") ordered.push(own);
} else if (kind === "ci" || kind === "co") {
ours.add(name);
if (kind === "ci" ? value : (toggles?.get(name) ?? element.classList.contains(name))) ordered.push(name);
}
}
return [...ordered, ...[...element.classList].filter((name) => !ours.has(name))].join(" ");
}
wholeStyle(element, attrs) {
const raw = this.rawStyles.get(element);
const parts = [];
for (const [kind, name, value] of attrs) {
if (kind === "v" && name === "style") parts.push(value);
else if (name === "style" && (kind === "o" || kind === "vo" || kind === "oo")) {
const own = kind === "o" ? value : (this.computedStyles.get(element) ?? "");
if (kind === "vo" || own !== "") parts.push(own);
} else if (kind === "sv" && value) parts.push(`${name}: ${value}`);
else if (kind === "so") {
const held = raw?.has(name) ? raw.get(name) : element.style.getPropertyValue(name).trim();
if (held) parts.push(`${name}: ${held}`);
}
}
return parts.join("; ");
}
writeWhole(element, attribute, whole, kind, name) {
if ((element.getAttribute(attribute) ?? "") === whole) return;
if (kind) {
this.stats.patches++;
this.notify("patch", { kind, name, node: element });
}
if (whole === "") element.removeAttribute(attribute);
else element.setAttribute(attribute, whole);
}
styled(element, node) {
if (node.a.some(([kind]) => kind === "co")) this.writeWhole(element, "class", this.wholeClass(element, node.a));
if (node.a.some(([kind]) => kind === "sv" || kind === "so")) this.writeWhole(element, "style", this.wholeStyle(element, node.a));
}
static inOrder(element, node) {
if (!node.a.some(([kind]) => kind === "vo" || kind === "oo" || kind === "fo" || kind === "so" || kind === "sv" || (kind === "v" && node.a.length > 1))) return;
const order = ["class"];
for (const [kind, name] of node.a) {
if ((kind === "v" || kind === "o" || kind === "oo" || kind === "f" || kind === "vo" || kind === "fo") && name !== "class" && name !== "style" && !order.includes(name)) order.push(name);
}
order.push("style");
const have = element.getAttributeNames().filter((name) => order.includes(name));
const wanted = order.filter((name) => have.includes(name));
if (have.every((name, at) => name === wanted[at])) return;
for (const name of wanted) {
const value = element.getAttribute(name);
element.removeAttribute(name);
element.setAttribute(name, value);
}
}
adoptText(element, node, owner, scope) {
const server = element.textContent;
const fragment = document.createDocumentFragment();
for (const child of node.c) fragment.append(this.build(child, owner, { ...scope, rcdata: true }));
element.replaceChildren(fragment);
if (element.textContent !== server) throw new Mismatch(`<${node.tag}> says ${JSON.stringify(server)}, not ${JSON.stringify(element.textContent)}`);
}
adopt(node, owner, scope, cursor) {
switch (node.t) {
case "s": {
if (!node.v) return;
if (cursor.top && blank(node.v) && !(cursor.node?.nodeType === 3 && cursor.node.data.startsWith(node.v))) return;
const text = cursor.take((found) => found.nodeType === 3 && found.data.startsWith(node.v), JSON.stringify(node.v));
if (text.data.length > node.v.length) cursor.node = text.splitText(node.v.length);
return;
}
case "raw":
if (cursor.node?.nodeType === 3) cursor.node = cursor.node.nextSibling;
return;
case "doctype":
if (cursor.node?.nodeType === 10) cursor.node = cursor.node.nextSibling;
return;
case "x": {
const computation = new Computation(this, { kind: "text", runner: this.kept.get(node.r), owner, scope, target: document.createTextNode("") });
computation.adopting = true;
const outcome = this.run(computation);
const value = computation.target.data;
if (this.isStatic(computation, outcome)) {
this.forget(computation, owner);
return this.adopt({ t: "s", v: value }, owner, scope, cursor);
}
cursor.comment("x");
let text = cursor.node?.nodeType === 3 ? cursor.take(() => true, "text") : null;
const end = cursor.comment("/x");
if (!text) end.before((text = document.createTextNode("")));
computation.target = text;
if (outcome !== "ok") return;
computation.adopting = false;
if (text.data !== value) {
this.stats.patches++;
this.notify("patch", { kind: "text", name: null, node: text });
text.data = value;
}
return;
}
case "h":
case "l": {
const label = node.t === "h" ? "html" : "list";
const computation = new Computation(this, { kind: "html", runner: this.kept.get(node.r), owner, scope, target: null });
computation.peek = true;
const outcome = this.run(computation);
computation.peek = false;
const nodes = computation.peeked;
computation.peeked = null;
if (this.isStatic(computation, outcome)) {
for (const child of nodes) this.adopt(child, computation, scope, cursor);
return;
}
const start = cursor.comment(label);
const end = cursor.closing(label);
computation.target = { start, end };
if (nodes) {
const inside = new Cursor(start.nextSibling);
for (const child of nodes) this.adopt(child, computation, scope, inside);
inside.end(end);
} else computation.adopting = true;
cursor.node = end.nextSibling;
return;
}
case "hx": {
const computation = new Computation(this, { kind: "html", runner: this.kept.get(node.r), owner, scope, target: null });
computation.hole = true;
computation.peek = true;
const outcome = this.run(computation);
computation.peek = false;
const nodes = computation.peeked;
computation.peeked = null;
if (this.isStatic(computation, outcome)) {
for (const child of nodes) this.adopt(child, computation, scope, cursor);
return;
}
if (cursor.node?.nodeType === 8 && cursor.node.data === "x") {
cursor.comment("x");
let text = cursor.node?.nodeType === 3 ? cursor.take(() => true, "text") : null;
const end = cursor.comment("/x");
if (!text) end.before((text = document.createTextNode("")));
computation.target = text;
computation.text = true;
computation.adopting = true;
if (nodes) this.settleHoleText(computation, nodes);
if (!computation.text) {
const fragment = document.createDocumentFragment();
for (const child of nodes) fragment.append(this.build(child, computation, scope));
replaceRange(computation.target, fragment);
}
return;
}
const start = cursor.comment("html");
const end = cursor.closing("html");
computation.target = { start, end };
if (nodes) {
const inside = new Cursor(start.nextSibling);
for (const child of nodes) this.adopt(child, computation, scope, inside);
inside.end(end);
} else computation.adopting = true;
cursor.node = end.nextSibling;
return;
}
case "f":
for (const child of node.c) this.adopt(child, owner, scope, cursor);
return;
case "e": {
node = writable(node, this);
if (!node) return;
if (node.tag === "body" && cursor.top && cursor.node?.localName === "head" && !cursor.node.firstChild) cursor.node = cursor.node.nextSibling;
const element = cursor.take((found) => found.nodeType === 1 && found.localName === node.tag, `<${node.tag}>`);
this.bind(element, node, owner, scope);
if (node.tag === "a" && !ownsCurrent(node)) this.markLink(element);
const inner = within(node, scope);
if (RCDATA.has(node.tag) && node.c.some((child) => child.t !== "s" && child.t !== "raw")) return this.adoptText(element, node, owner, inner);
if (cursor.rebuild && this.arriving && (node.tag === "html" || node.tag === "body")) Runtime.attributesFrom(element, node, node.tag === "html" ? this.arriving.documentElement : this.arriving.body);
if (cursor.rebuild && node.tag === "head") {
if (this.arriving?.head) this.reconcileHead(element, this.arriving.head);
return this.keepHead(element, node, owner, inner);
}
if (cursor.rebuild && node.tag === "body") return this.renderBody(element, node, owner, inner);
const inside = new Cursor(element.firstChild, element, cursor.rebuild && element === element.ownerDocument.documentElement);
for (const child of node.c) this.adopt(child, owner, inner, inside);
const left = inside.node && !inside.rebuild ? inside.left(node.tag === "body" && cursor.top) : null;
if (left) throw new Mismatch(`<${node.tag}> has more than the server's markup says: ${named(left)}${placed(element)}`, left);
return;
}
case "loading": {
const loading = new Loading();
loading.revealed = true;
const start = cursor.comment("loading");
const end = cursor.closing("loading");
loading.range = { start, end };
for (const child of node.c) this.adopt(child, owner, { ...scope, loading }, cursor);
cursor.end(end);
cursor.node = end.nextSibling;
return;
}
case "show":
case "for": {
if (node.t === "show" && !(cursor.node?.nodeType === 8 && cursor.node.data === "show")) {
const holds = JSON.parse(this.once(node.r, owner, scope));
if (!holds) return this.adopt(node.fallback, owner, scope, cursor);
if (!node.with) {
for (const child of node.c) this.adopt(child, owner, scope, cursor);
return;
}
const made = new Computation(this, { kind: "html", runner: this.kept.get(node.with), owner, scope, target: null });
made.untracked = true;
made.choosing = Boolean(node.b);
made.peek = true;
this.run(made);
made.peek = false;
const nodes = made.peeked ?? [];
made.peeked = null;
for (const child of nodes) this.adopt(child, made, scope, cursor);
return;
}
const start = cursor.comment(node.t);
const end = cursor.closing(node.t);
const computation = new Computation(this, { kind: node.t, runner: this.kept.get(node.r), owner, scope, target: { start, end } });
computation.node = node;
if (node.t === "for") computation.list = this.lists.get(node.id);
computation.adopting = true;
this.run(computation);
cursor.node = end.nextSibling;
return;
}
case "c": {
const { computation, nodes } = this.component(node, owner, scope);
for (const child of nodes) this.adopt(child, computation, scope, cursor);
return;
}
case "ctx":
for (const child of node.c) this.adopt(child, owner, provided(scope, node), cursor);
return;
case "nh":
cursor.take((at) => at.nodeType === 8 && isRegionStart(at.data), "<!--nohydration-->");
cursor.node = cursor.closing("nohydration").nextSibling;
return;
case "listen":
this.listenOn(node, owner, scope);
return;
case "errored": {
const failed = cursor.node?.nodeType === 8 && cursor.node.data === "errored:failed";
const start = cursor.comment(failed ? "errored:failed" : "errored");
const end = cursor.closing("errored");
const errored = new Errored(this, { runner: this.kept.get(node.r), nodes: node.c, owner, scope, range: { start, end } });
if (failed) replaceRange(errored.range, errored.build());
else {
errored.adopt(cursor);
cursor.end(end);
}
cursor.node = end.nextSibling;
return;
}
default:
throw new Mismatch(`unknown node ${node.t}`);
}
}
seed(page) {
const script = page.querySelector("script.rocx-answers");
for (const [name, input, answer] of script ? JSON.parse(script.textContent) : []) this.answers.set(`${name}\n${input}`, answer);
script?.remove();
const flash = page.querySelector("script.rocx-flash");
if (flash) this.flash = JSON.parse(flash.textContent);
flash?.remove();
}
hydrate(container, { strict = false } = {}) {
this.seed(container);
const seeded = new Map(this.answers);
const hydrating = (this.hydrating = { asked: [] });
const start = [...container.childNodes].find((node) => node.nodeType === 8 && node.data === "app");
const end = [...container.childNodes].find((node) => node.nodeType === 8 && node.data === "/app");
this.root = new Computation(this, { kind: "root", owner: null, scope: {}, target: { start, end } });
this.root.adopting = true;
foreignKept = !strict;
try {
if (!start || !end) throw new Mismatch("no <!--app--> in the page");
this.run(this.root);
} catch (error) {
if (!(error instanceof Mismatch)) throw error;
this.mismatched(error, "rendering it again");
this.dispose(this.root);
this.answers = seeded;
this.keepingRegions(container, () => {
container.replaceChildren();
this.mount(container);
});
}
this.answers.clear();
this.hydrating = null;
if (strict && hydrating.asked.length) throw Runtime.askedAgain(hydrating.asked);
}
mismatched(error, then) {
console.warn(`rocx: the page isn't what the app renders (${error.message}); ${then}`, ...(error.found ? [error.found] : []));
globalThis.document?.dispatchEvent(new CustomEvent("rocx:mismatch", { bubbles: true, detail: { message: error.message, node: error.found } }));
}
static askedAgain(asked) {
return new Error(`rocx: hydrating, the page asked the server again for ${asked.join(", ")}: the server didn't note it as it rendered the page`);
}
hydrateDocument(doc = document, { strict = false } = {}) {
this.page = doc;
this.strict = strict;
this.committed = this.here();
this.seed(doc);
const seeded = new Map(this.answers);
const root = () => new Computation(this, { kind: "root", owner: null, scope: {}, target: { document: doc } });
this.root = root();
this.root.adopting = true;
const hydrating = (this.hydrating = { asked: [] });
const askedAgain = () => Runtime.askedAgain(hydrating.asked);
foreignKept = !strict;
try {
this.run(this.root);
if (strict && hydrating.asked.length) throw askedAgain();
} catch (error) {
if (!(error instanceof Mismatch)) throw error;
this.dispose(this.root);
if (strict && hydrating.asked.length) throw askedAgain();
if (strict) throw new Error(`rocx: the page isn't what the app renders (${error.message})`);
this.mismatched(error, "rendering <body> again");
this.answers = seeded;
this.root = root();
try {
this.run(this.root);
} catch (again) {
if (again instanceof Mismatch) throw new Error(`rocx: the page can't be rendered again (${again.message})`);
throw again;
}
} finally {
this.answers.clear();
this.hydrating = null;
}
this.listenForNavigation();
}
settleDocument(computation, parsed) {
const rebuild = !computation.adopting;
computation.adopting = false;
const doc = computation.target.document;
const cursor = new Cursor(doc.firstChild, doc, rebuild);
for (const node of Array.isArray(parsed) ? parsed : [parsed]) this.adopt(node, computation, computation.scope, cursor);
}
keepHead(head, node, owner, scope) {
const part = new Computation(this, { kind: "boundary", owner, scope });
try {
const cursor = new Cursor(head.firstChild, head);
for (const child of node.c) this.adopt(child, part, scope, cursor);
const left = cursor.node && cursor.left(false);
if (left) throw new Mismatch(`<head> has more than the server's markup says: ${named(left)}`, left);
} catch (error) {
if (!(error instanceof Mismatch)) throw error;
console.warn(`rocx: <head> isn't what the app renders either (${error.message}); it stays as the server sent it`, ...(error.found ? [error.found] : []));
this.dispose(part);
const unseen = new Computation(this, { kind: "boundary", owner, scope });
const copy = document.createDocumentFragment();
for (const child of node.c) copy.append(this.build(child, unseen, scope));
}
}
renderBody(body, node, owner, scope) {
const fragment = this.keepingRegions(this.arriving?.body ?? body, () => {
const made = document.createDocumentFragment();
for (const child of node.c) made.append(this.build(child, owner, scope));
return made;
});
const children = [...body.childNodes];
const last = children.findLastIndex(hosts);
body.replaceChildren(fragment, ...children.filter((child, at) => hosts(child) || foreignNodes.has(child) || (last >= 0 && at > last && child.nodeType === 1)));
}
bind(element, node, owner, scope) {
let drag = null;
for (const [kind, name] of node.a) {
if (((kind === "on" || kind === "onp") && DRAG_EVENTS.has(name)) || kind === "dd" || kind === "ddo") {
drag ??= { drop: false, start: false, enter: [], leave: [], depth: 0 };
if (name === "drop") drag.drop = true;
if (name === "dragstart" || kind === "dd" || kind === "ddo") drag.start = true;
}
}
for (const [kind, name, value, wanted] of node.a) {
if (kind === "vo" || kind === "fo" || kind === "co" || kind === "oo" || kind === "so") {
const computed = { vo: "attr", fo: "flag", co: "class", oo: "optional", so: "style" }[kind];
const computation = new Computation(this, { kind: computed, runner: this.kept.get(value), owner, scope, target: element, name });
if (kind === "co" || ((kind === "vo" || kind === "oo") && joined(node.a, name))) computation.attrs = node.a;
if (this.isStatic(computation, this.run(computation))) this.forget(computation, owner);
} else if (kind === "on" || kind === "onp") {
const handler = this.listener(kind, name, value, wanted, scope, owner);
if (drag && name === "dragenter") drag.enter.push(handler);
else if (drag && name === "dragleave") drag.leave.push(handler);
else element.addEventListener(name, handler);
} else if (kind === "e") {
const written = new Set(node.a.filter(([named]) => NAMED.has(named)).map(([, attribute]) => attribute));
this.enhancedImages.set(element, ["srcset", "sizes", "width", "height"].filter((added) => !written.has(added)));
} else if (kind === "k") this.keys.set(element, name);
else if (kind === "ko") this.run(new Computation(this, { kind: "key", runner: this.kept.get(name), owner, scope, target: element }));
else if (kind === "onk") element.addEventListener(name, this.listener(kind, name, value, wanted, scope, owner));
else if (kind === "tr") this.setTransition(element, name, value);
else if (kind === "tro") this.run(new Computation(this, { kind: "transition", runner: this.kept.get(value), owner, scope, target: element, name }));
else if (kind === "frame") {
let last = performance.now();
let shown = false;
const tick = (now) => {
if (!this.kept.has(value) || (shown && !element.isConnected)) return;
const ms = Math.min(Math.max(now - last, 0), 100);
last = now;
if (element.isConnected) {
shown = true;
const started = performance.now();
const patches = this.stats.patches;
this.handle(value, String(Math.round(ms * 1000)), scope, { owner });
this.flush();
this.notify("frame", { node: element, ms: performance.now() - started, patches: this.stats.patches - patches });
}
requestAnimationFrame(tick);
};
requestAnimationFrame(tick);
} else if (kind === "view") this.viewport(element, value, scope, owner);
else if (kind === "pt") this.pointAt(element, name, value, scope, owner, () => element.getBoundingClientRect());
else if (kind === "dd") this.setDrag(element, name, value);
else if (kind === "ddo") {
const computation = new Computation(this, { kind: "drag", runner: this.kept.get(value), owner, scope, target: element, name });
if (this.isStatic(computation, this.run(computation))) this.forget(computation, owner);
}
}
if (drag) this.dragAndDrop(element, drag);
}
viewport(element, value, scope, owner) {
if (typeof requestAnimationFrame === "undefined") return;
let said = "";
let asked = 0;
const measure = () => {
asked = 0;
if (!this.kept.has(value) || !element.isConnected) return;
const now = `${Math.round(element.scrollTop)},${Math.round(element.scrollLeft)},${element.clientWidth},${element.clientHeight}`;
if (now === said) return;
said = now;
this.handle(value, now, scope, { owner });
};
const ask = () => {
asked ||= requestAnimationFrame(measure);
};
element.addEventListener("scroll", ask, { passive: true });
const observer = typeof ResizeObserver === "undefined" ? null : new ResizeObserver(ask);
observer?.observe(element);
ask();
const record = owner?.making ?? owner?.made;
const cleanups = record ? own(record, "cleanups") : undefined;
cleanups?.push(() => {
element.removeEventListener("scroll", ask);
observer?.disconnect();
if (asked) cancelAnimationFrame(asked);
});
}
listener(kind, name, value, wanted, scope, owner) {
if (kind === "onk")
return (event) => {
if (this.kept.has(value)) this.handle(value, wanted === "keys" ? keysOf(event) : (event.key ?? ""), scope, { owner });
};
const given = wanted?.startsWith(".") ? wanted : undefined;
const pressed = wanted === undefined || given ? null : keyCombo(wanted);
return (event) => {
if (pressed && !pressed(event)) return;
if (kind === "onp" || name === "submit" || pressed) event.preventDefault();
const target = event.target;
const input =
given === ".files"
? this.filesOf(event, owner)
: given === ".data"
? itemsOf(event.dataTransfer ?? event.clipboardData)
: event.type === "drop"
? (event.dataTransfer?.getData("text/plain") ?? "")
: event.type === "visibilitychange"
? String(this.page?.visibilityState !== "hidden")
: target?.type === "checkbox"
? String(target.checked)
: String(target?.value ?? "");
if (this.kept.has(value)) this.handle(value, input, scope, { owner });
};
}
listenOn(node, owner, scope) {
const target = node.to === "window" ? this.page?.defaultView : this.page;
if (!target?.addEventListener) return;
const record = owner?.making ?? owner?.made;
const cleanups = record ? own(record, "cleanups") : undefined;
for (const [kind, name, value, wanted] of node.a) {
if (kind === "pt") {
const view = this.page.defaultView;
this.pointAt(target, name, value, scope, owner, () => ({ left: 0, top: 0, width: view?.innerWidth ?? 0, height: view?.innerHeight ?? 0 }));
continue;
}
if (kind !== "on" && kind !== "onp" && kind !== "onk") continue;
const listener = this.listener(kind, name, value, wanted, scope, owner);
target.addEventListener(name, listener);
cleanups?.push(() => target.removeEventListener(name, listener));
}
}
dragAndDrop(element, drag) {
const left = (event) => {
drag.depth = 0;
this.overs.delete(drag);
for (const handler of drag.leave) handler(event);
};
drag.left = left;
if (drag.enter.length || drag.leave.length || drag.drop) {
element.addEventListener("dragenter", (event) => {
if (drag.drop) event.preventDefault();
if (drag.depth++ > 0) return;
this.overs.add(drag);
this.listenForDragEnds();
for (const handler of drag.enter) handler(event);
});
element.addEventListener("dragleave", (event) => {
if (drag.depth > 0 && --drag.depth === 0) left(event);
});
element.addEventListener("drop", (event) => {
if (drag.drop) event.preventDefault();
if (drag.depth > 0) left(event);
});
}
if (drag.drop)
element.addEventListener("dragover", (event) => {
event.preventDefault();
if (event.dataTransfer) event.dataTransfer.dropEffect = dropEffect(event.dataTransfer.effectAllowed);
});
if (drag.start) {
element.addEventListener("dragstart", (event) => {
const transfer = event.dataTransfer;
if (!transfer) return;
const own = this.dragged.get(element);
for (const [type, data] of own?.data ?? []) transfer.setData(type, data);
if (!transfer.types.length) transfer.setData("application/x-rocx", "rocx");
if (own?.image && !this.pointerDrag && typeof transfer.setDragImage === "function") {
const image = this.dragImage(element, own.image, event);
if (image) {
transfer.setDragImage(image.node, image.x, image.y);
setTimeout(() => image.node.remove(), 0);
}
}
});
element.addEventListener("pointerdown", (event) => this.pointerDown(element, event));
element.addEventListener(
"dragstart",
(event) => {
if (this.pointerDrag && !this.pointerDrag.firing) {
event.preventDefault();
event.stopImmediatePropagation();
}
},
true,
);
element.addEventListener(
"touchmove",
(event) => {
if (this.pointerDrag?.state === "dragging" && event.cancelable) event.preventDefault();
},
{ passive: false },
);
}
}
setDrag(element, name, value) {
let own = this.dragged.get(element);
if (!own) this.dragged.set(element, (own = { data: [], image: "" }));
if (name === "data") {
try {
own.data = JSON.parse(value);
} catch {
own.data = [];
}
} else own.image = String(value);
}
dragImage(element, id, event) {
const source = id ? this.page.getElementById(id) : element;
if (!source) return null;
const node = source.cloneNode(true);
node.removeAttribute("id");
node.removeAttribute("hidden");
for (const inside of node.querySelectorAll("[id]")) inside.removeAttribute("id");
node.setAttribute("aria-hidden", "true");
node.setAttribute("data-rocx-drag-image", "");
const own = source.getBoundingClientRect();
const fixed = { position: "fixed", left: "-100000px", top: "0px", right: "auto", bottom: "auto", margin: "0px", "pointer-events": "none", "z-index": "2147483647", "box-sizing": "border-box" };
if (!id) Object.assign(fixed, { width: `${own.width}px`, height: `${own.height}px` });
for (const [name, value] of Object.entries(fixed)) node.style.setProperty(name, value, "important");
source.after(node);
const box = node.getBoundingClientRect();
const from = element.getBoundingClientRect();
const share = (at, start, size) => (size > 0 ? Math.min(Math.max((at - start) / size, 0), 1) : 0.5);
return { node, x: Math.round(share(event.clientX, from.left, from.width) * box.width), y: Math.round(share(event.clientY, from.top, from.height) * box.height), width: box.width, height: box.height };
}
filesOf(event, owner) {
const list = event.dataTransfer?.files ?? event.clipboardData?.files ?? event.target?.files ?? [];
const record = owner?.making ?? owner?.made;
const cleanups = record ? own(record, "cleanups") : undefined;
const files = [];
for (const file of list) {
const url = typeof URL.createObjectURL === "function" ? URL.createObjectURL(file) : "";
if (url) {
this.files.set(url, file);
cleanups?.push(() => {
this.files.delete(url);
URL.revokeObjectURL(url);
});
}
files.push({ name: file.name ?? "", type: file.type ?? "", size: file.size ?? 0, url });
}
return JSON.stringify(files);
}
fileOf(url) {
return this.files.get(url) ?? null;
}
pointAt(target, name, value, scope, owner, box) {
let last = null;
let asked = 0;
const say = () => {
asked = 0;
if (!last || !this.kept.has(value)) return;
const rect = box();
const share = (at, start, size) => (size > 0 ? Math.round(Math.min(Math.max((at - start) / size, 0), 1) * 1000) : 0);
const point = `${share(last.x, rect.left, rect.width)},${share(last.y, rect.top, rect.height)}`;
last = null;
this.handle(value, point, scope, { owner });
};
const listener = (event) => {
const touch = event.touches?.[0] ?? event.changedTouches?.[0];
last = { x: touch?.clientX ?? event.clientX ?? 0, y: touch?.clientY ?? event.clientY ?? 0 };
if (!MOVES.has(name) || typeof requestAnimationFrame === "undefined") say();
else asked ||= requestAnimationFrame(say);
};
target.addEventListener(name, listener, { passive: true });
const record = owner?.making ?? owner?.made;
const cleanups = record ? own(record, "cleanups") : undefined;
cleanups?.push(() => {
target.removeEventListener(name, listener);
if (asked) cancelAnimationFrame(asked);
});
}
pointerDown(element, event) {
if (event.pointerType === "mouse" || !event.isPrimary || event.button > 0 || this.pointerDrag || !element.draggable) return;
if (event.target?.closest?.("input, textarea, select, [contenteditable]:not([contenteditable=false])") && element.contains(event.target)) return;
const page = this.page;
const drag = { element, id: event.pointerId, state: "held", from: { x: event.clientX, y: event.clientY }, at: { x: event.clientX, y: event.clientY }, firing: false, target: null, operation: "none", transfer: null, ghost: null, frame: 0, styles: [] };
this.pointerDrag = drag;
const quiet = ["-webkit-touch-callout", "-webkit-user-select", "user-select"];
for (const name of quiet) drag.styles.push([name, element.style.getPropertyValue(name), element.style.getPropertyPriority(name)]);
for (const name of quiet) element.style.setProperty(name, "none");
const ours = (event) => event.pointerId === drag.id;
const moved = (event) => {
if (!ours(event)) return;
drag.at = { x: event.clientX, y: event.clientY };
if (drag.state === "held") {
if (Math.hypot(drag.at.x - drag.from.x, drag.at.y - drag.from.y) > POINTER_DRAG.slop) this.pointerDragEnd(drag, { cancel: true });
} else if (drag.state === "dragging") {
this.placeGhost(drag);
drag.frame ||= requestAnimationFrame(() => this.pointerDragFrame(drag));
}
};
const up = (event) => ours(event) && this.pointerDragEnd(drag, { cancel: drag.state !== "dragging" });
const cancelled = (event) => ours(event) && this.pointerDragEnd(drag, { cancel: true });
const hush = (event) => event.preventDefault();
const timer = setTimeout(() => this.pointerDragStart(drag), POINTER_DRAG.hold);
drag.off = () => {
clearTimeout(timer);
page.removeEventListener("pointermove", moved, true);
page.removeEventListener("pointerup", up, true);
page.removeEventListener("pointercancel", cancelled, true);
page.removeEventListener("contextmenu", hush, true);
page.removeEventListener("selectstart", hush, true);
};
page.addEventListener("pointermove", moved, true);
page.addEventListener("pointerup", up, true);
page.addEventListener("pointercancel", cancelled, true);
page.addEventListener("contextmenu", hush, true);
page.addEventListener("selectstart", hush, true);
}
fireDrag(drag, type, target, { related = null, effect = "none" } = {}) {
const transfer = drag.transfer;
try {
transfer.dropEffect = type === "dragenter" || type === "dragover" ? dropEffect(transfer.effectAllowed) : effect;
} catch {}
const init = { bubbles: true, composed: true, cancelable: type !== "dragleave" && type !== "dragend", clientX: drag.at.x, clientY: drag.at.y, screenX: drag.at.x, screenY: drag.at.y, buttons: type === "drop" || type === "dragend" ? 0 : 1, relatedTarget: related, dataTransfer: transfer };
let event;
try {
event = new DragEvent(type, init);
} catch {
event = new MouseEvent(type, init);
}
if (event.dataTransfer !== transfer) Object.defineProperty(event, "dataTransfer", { value: transfer });
drag.firing = true;
try {
return !target.dispatchEvent(event);
} finally {
drag.firing = false;
}
}
pointerDragStart(drag) {
if (this.pointerDrag !== drag || drag.state !== "held" || !drag.element.isConnected) return this.pointerDragEnd(drag, { cancel: true });
drag.transfer = makeTransfer();
const image = this.dragImage(drag.element, this.dragged.get(drag.element)?.image ?? "", { clientX: drag.from.x, clientY: drag.from.y });
if (this.fireDrag(drag, "dragstart", drag.element)) {
image?.node.remove();
return this.pointerDragEnd(drag, { cancel: true });
}
drag.state = "dragging";
if (image) {
drag.ghost = image;
if (typeof image.node.showPopover === "function") {
const look = getComputedStyle(image.node);
for (const name of POPOVER_LOOK) image.node.style.setProperty(name, look.getPropertyValue(name), "important");
image.node.setAttribute("popover", "manual");
image.node.showPopover();
}
image.node.style.setProperty("left", "0px", "important");
image.node.style.setProperty("top", "0px", "important");
this.placeGhost(drag);
}
this.pointerDragFrame(drag);
}
placeGhost(drag) {
const ghost = drag.ghost;
if (ghost) ghost.node.style.setProperty("translate", `${drag.at.x - ghost.x}px ${drag.at.y - ghost.y}px`, "important");
}
pointerDragFrame(drag) {
drag.frame = 0;
if (this.pointerDrag !== drag || drag.state !== "dragging") return;
this.fireDrag(drag, "drag", drag.element);
const target = this.page.elementFromPoint(drag.at.x, drag.at.y) ?? this.page.body;
if (target !== drag.target) {
this.fireDrag(drag, "dragenter", target, { related: drag.target });
if (drag.target) this.fireDrag(drag, "dragleave", drag.target, { related: target });
drag.target = target;
}
drag.operation = this.fireDrag(drag, "dragover", target) ? drag.transfer.dropEffect || "move" : "none";
if (this.scrollNear(target, drag.at)) drag.frame = requestAnimationFrame(() => this.pointerDragFrame(drag));
}
scrollNear(node, at) {
const { edge, speed } = POINTER_DRAG;
const step = (near) => (near < edge ? Math.ceil(speed * (1 - Math.max(near, 0) / edge)) : 0);
const page = this.page.scrollingElement ?? this.page.documentElement;
for (let box = node?.nodeType === 1 ? node : node?.parentElement; box; box = box.parentElement) {
const whole = box === page || box === this.page.body;
const style = whole ? null : getComputedStyle(box);
const scrolls = (overflow) => whole || overflow === "auto" || overflow === "scroll";
const rect = whole ? { left: 0, top: 0, right: innerWidth, bottom: innerHeight } : box.getBoundingClientRect();
const target = whole ? page : box;
let dx = 0;
let dy = 0;
if (scrolls(style?.overflowX) && target.scrollWidth > target.clientWidth) {
if (target.scrollLeft > 0) dx -= step(at.x - rect.left);
if (target.scrollLeft + target.clientWidth < target.scrollWidth - 1) dx += step(rect.right - at.x);
}
if (scrolls(style?.overflowY) && target.scrollHeight > target.clientHeight) {
if (target.scrollTop > 0) dy -= step(at.y - rect.top);
if (target.scrollTop + target.clientHeight < target.scrollHeight - 1) dy += step(rect.bottom - at.y);
}
if (dx || dy) {
target.scrollBy(dx, dy);
return true;
}
if (whole) break;
}
return false;
}
pointerDragEnd(drag, { cancel = false } = {}) {
if (this.pointerDrag !== drag) return;
this.pointerDrag = null;
drag.off();
if (drag.frame) cancelAnimationFrame(drag.frame);
const started = drag.state === "dragging";
drag.state = "done";
drag.ghost?.node.remove();
for (const [name, value, priority] of drag.styles.toReversed()) {
if (value) drag.element.style.setProperty(name, value, priority);
else drag.element.style.removeProperty(name);
}
if (!started) return;
const dropped = !cancel && drag.operation !== "none" && drag.target;
if (dropped) this.fireDrag(drag, "drop", drag.target, { effect: drag.operation });
else if (drag.target) this.fireDrag(drag, "dragleave", drag.target);
this.fireDrag(drag, "dragend", drag.element, { effect: dropped ? drag.operation : "none" });
const page = this.page;
const click = (event) => {
event.preventDefault();
event.stopPropagation();
done();
};
const done = () => {
page.removeEventListener("click", click, true);
page.removeEventListener("pointerdown", done, true);
};
page.addEventListener("click", click, true);
page.addEventListener("pointerdown", done, true);
setTimeout(done, 400);
}
listenForDragEnds() {
if (this.dragEnds || typeof this.page?.addEventListener !== "function") return;
this.dragEnds = (event) => {
for (const drag of [...this.overs]) drag.left(event);
};
this.page.addEventListener("dragend", this.dragEnds);
this.page.addEventListener("drop", this.dragEnds);
}
once(runner, owner, scope, boundary = null) {
return this.onceInert(runner, owner, scope, boundary).out;
}
onceInert(runner, owner, scope, boundary = null) {
const computation = new Computation(this, { kind: "once", runner: this.kept.get(runner), owner, scope });
computation.boundary = boundary;
computation.making = making_();
const previous = this.current;
this.current = computation;
try {
const out = this.enter(() => this.ex.run(computation.runner));
return { out, inert: inert(computation.making) };
} finally {
this.current = previous;
computation.made = computation.making;
computation.making = null;
}
}
serverHtml(node, owner, scope) {
const all = (nodes) => nodes.map((child) => this.serverHtml(child, owner, scope)).join("");
const mark = (label, inner) => (scope.rcdata || scope.region ? inner : `<!--${label}-->${inner}<!--/${label}-->`);
switch (node.t) {
case "s":
return escape(node.v);
case "raw":
return node.v;
case "doctype":
return "<!doctype html>";
case "x": {
const { out, inert } = this.onceInert(node.r, owner, scope);
const text = escape(JSON.parse(out));
return inert ? text : mark("x", text);
}
case "h":
case "l": {
const label = node.t === "h" ? "html" : "list";
const { out, inert } = this.onceInert(node.r, owner, scope);
const parsed = JSON.parse(out);
const inner = (Array.isArray(parsed) ? parsed : [parsed]).map((child) => this.serverHtml(child, owner, scope)).join("");
return inert ? inner : mark(label, inner);
}
case "hx": {
const { out, inert } = this.onceInert(node.r, owner, scope);
const nodes = answered(JSON.parse(out));
const inner = nodes.map((child) => this.serverHtml(child, owner, scope)).join("");
return inert ? inner : mark(loneText(nodes) === null ? "html" : "x", inner);
}
case "f":
return all(node.c);
case "loading":
return mark("loading", all(node.c));
case "show": {
const { out, inert } = this.onceInert(node.r, owner, scope);
const holds = JSON.parse(out);
const shown = !holds ? this.serverHtml(node.fallback, owner, scope) : node.with ? this.serverHtml(JSON.parse(this.once(node.with, owner, scope)), owner, scope) : all(node.c);
return inert ? shown : mark("show", shown);
}
case "for": {
const list = this.lists.get(node.id);
const entries = JSON.parse(this.once(node.r, owner, scope));
const rows = entries.map(({ k, r }, index) => {
list.indexes.set(k, { value: index, observers: null });
return mark("row", this.serverHtml(JSON.parse(this.once(r, owner, scope)), owner, scope));
});
return mark("for", rows.length ? rows.join("") : mark("fallback", this.serverHtml(node.fallback, owner, scope)));
}
case "errored":
try {
return mark("errored", all(node.c));
} catch (error) {
if (!(error instanceof Failed)) throw error;
const fallback = JSON.parse(this.once(node.r, owner, scope, { id: 0, failed: error.message }));
const shown = this.serverHtml(fallback, owner, scope);
return scope.rcdata || scope.region ? shown : `<!--errored:failed-->${shown}<!--/errored-->`;
}
case "c":
return this.serverHtml(JSON.parse(this.once(node.r, owner, scope)), owner, scope);
case "nh": {
if (scope.region || scope.rcdata) return all(node.c);
if (this.regions) {
if (!this.regions.length) throw new Error("rocx: the app renders more <NoHydration>s than the page has");
const region = this.regions.shift();
const [mark, inside] = typeof region === "string" ? ["", region] : [region.read ? ":read" : "", region.html];
return `<!--nohydration${mark}-->${inside}<!--/nohydration-->`;
}
const inner = { ...scope, region: true };
return `<!--nohydration-->${node.c.map((child) => this.serverHtml(child, owner, inner)).join("")}<!--/nohydration-->`;
}
case "ctx":
return node.c.map((child) => this.serverHtml(child, owner, provided(scope, node))).join("");
case "listen":
if (scope.region && node.a.length) throw new Error(inRegion(node.to === "window" ? "Window" : "Document", node.a[0][1]));
return "";
case "e": {
node = writable(node, null);
if (!node) return "";
const classes = [];
const attributes = [];
const styles = [];
let href = null;
for (const [kind, name, value] of node.a) {
if (scope.region && (kind === "on" || kind === "onp" || kind === "onk" || kind === "frame" || kind === "view" || kind === "pt" || kind === "dd" || kind === "ddo")) throw new Error(inRegion(node.tag, name));
if (kind === "v" && name === "class") classes.push(value);
else if (kind === "v" && name === "style") styles.push(value);
else if ((name === "class" || name === "style") && (kind === "o" || kind === "vo" || kind === "oo")) {
const own = kind === "o" ? value : JSON.parse(this.once(value, owner, scope));
if (own !== "" || kind === "vo") (name === "class" ? classes : styles).push(own);
} else if (kind === "v") {
if (name === "href") href = value;
attributes.push(`${name}="${escape(value)}"`);
} else if (kind === "o" && value !== "") {
if (name === "href") href = value;
attributes.push(`${name}="${escape(value)}"`);
} else if (kind === "ci" && value) classes.push(name);
else if (kind === "f" && value) attributes.push(name);
else if (kind === "vo") {
const computed = JSON.parse(this.once(value, owner, scope));
if (name === "href") href = computed;
attributes.push(`${name}="${escape(computed)}"`);
} else if (kind === "oo") {
const optional = JSON.parse(this.once(value, owner, scope));
if (optional !== "") {
if (name === "href") href = optional;
attributes.push(`${name}="${escape(optional)}"`);
}
} else if (kind === "fo" && JSON.parse(this.once(value, owner, scope))) attributes.push(name);
else if (kind === "co" && JSON.parse(this.once(value, owner, scope))) classes.push(name);
else if (kind === "sv" && value) styles.push(`${name}: ${value}`);
else if (kind === "so") {
const styled = JSON.parse(this.once(value, owner, scope));
if (styled !== "") styles.push(`${name}: ${styled}`);
}
}
if (node.tag.toLowerCase() === "input" && node.a.some(([kind, name, value]) => kind === "v" && name === "type" && String(value).toLowerCase() === "password")) {
const named = node.a.find(([kind, name]) => kind === "v" && name === "name");
if (named && named[2] !== "") this.secrets.push(String(named[2]));
}
if (classes.length) attributes.unshift(`class="${escape(classes.join(" "))}"`);
if (styles.length) attributes.push(`style="${escape(styles.join("; "))}"`);
const mark = node.tag === "a" && !ownsCurrent(node) ? this.linkMark(href) : null;
if (mark) attributes.push(`aria-current="${mark}"`);
const open = `<${node.tag}${attributes.map((attribute) => ` ${attribute}`).join("")}>`;
const inner = RCDATA.has(node.tag) ? { ...scope, rcdata: true } : scope;
return VOID.has(node.tag) ? open : `${open}${node.c.map((child) => this.serverHtml(child, owner, inner)).join("")}</${node.tag}>`;
}
default:
throw new Error(`rocx: unknown node ${node.t}`);
}
}
renderToString({ path = "/", headers = [], answers = null, regions = null, scripts = [] } = {}, scope = {}) {
this.given = answers;
this.regions = regions && [...regions];
this.pageScripts = scripts;
try {
const rendered = this.renderPage(path, headers, scope);
if (this.regions?.length) throw new Error(`rocx: the page has ${this.regions.length} <NoHydration> more than the app renders`);
return rendered;
} finally {
this.given = null;
this.regions = null;
}
}
static regionsOf(html) {
return [...html.matchAll(/<!--nohydration(:read)?-->([\s\S]*?)<!--\/nohydration-->/g)].map((match) => (match[1] ? { read: true, html: match[2] } : match[2]));
}
renderPage(path, headers, scope) {
this.request = wire("GET", path, headers, "");
this.headers = headers;
this.recorded = [];
this.flashed = "";
this.secrets = [];
this.titled = null;
this.headed = [];
this.built = null;
this.status = 200;
const wasOnServer = this.onServer;
this.onServer = true;
const root = new Computation(this, { kind: "root", owner: null, scope });
root.making = making_();
this.current = root;
let out;
try {
out = this.enter(() => this.ex.mount());
} catch (error) {
this.onServer = wasOnServer;
throw error;
} finally {
this.current = null;
}
try {
const markup = this.serverHtml(JSON.parse(out), root, scope);
const html = DOCUMENT.test(markup) ? Runtime.documentOf(markup, this.recorded, Runtime.withoutSecrets(this.flashed, this.secrets), this.titled, this.pageScripts ?? [], this.headed, this.built) : `<!--app-->${markup}<!--/app-->`;
return { html, answers: this.recorded };
} finally {
this.onServer = wasOnServer;
root.made = root.making;
this.dispose(root);
for (const signal of this.signals.values()) this.releaseSignal(signal);
this.signals.clear();
for (const list of this.lists.values()) this.dropList(list);
this.lists.clear();
}
}
static titled(markup, title) {
const end = markup.indexOf("</head>");
if (end < 0) return markup;
const own = markup.slice(0, end).search(/<title[\s>]/);
const at = own >= 0 ? own : end;
return `${markup.slice(0, at)}<title data-rocx>${title.replace(/&/g, "&amp;").replace(/</g, "&lt;")}</title>${markup.slice(at)}`;
}
static answersScript(answers) {
return `<script type="application/json" class="rocx-answers">${JSON.stringify(answers).replace(/</g, "\\u003c")}</script>`;
}
static withoutSecrets(flash, secrets) {
if (!flash || !secrets.length) return flash;
let kept;
try {
kept = JSON.parse(flash);
} catch {
return flash;
}
if (typeof kept?.input !== "string") return flash;
const decoded = (name) => {
try {
return decodeURIComponent(name.replace(/\+/g, " "));
} catch {
return name;
}
};
const fields = kept.input.split("&").filter((field) => field !== "");
const left = fields.filter((field) => !secrets.includes(decoded(field.split("=")[0])));
if (left.length === fields.length) return flash;
return JSON.stringify({ ...kept, input: left.join("&") });
}
static flashScript(flash) {
return `<script type="application/json" class="rocx-flash">${JSON.stringify(flash).replace(/</g, "\\u003c")}</script>`;
}
static documentOf(markup, answers, flash = "", title = null, scripts = [], heads = [], build = null) {
if (title !== null) markup = Runtime.titled(markup, title);
markup = Runtime.headed(markup, heads);
const doctype = /^<!doctype/i.test(markup.trimStart()) ? "" : "<!doctype html>";
const before = `${flash ? Runtime.flashScript(flash) : ""}${Runtime.answersScript(answers)}${Runtime.scriptTags(scripts)}${startWith(build)}`;
const at = markup.lastIndexOf("</body>");
return at < 0 ? `${doctype}${markup}${before}` : `${doctype}${markup.slice(0, at)}${before}${markup.slice(at)}`;
}
static scriptTags(urls) {
return urls.map((url) => `<script type="module" data-rocx src="${url.replace(/&/g, "&amp;").replace(/"/g, "&quot;")}"></script>`).join("");
}
component(node, owner, scope) {
const computation = new Computation(this, { kind: "component", runner: this.kept.get(node.r), owner, scope });
computation.making = making_();
const previous = this.current;
const place = this.place;
this.current = computation;
this.place = null;
this.stats.runs++;
try {
return { computation, nodes: [JSON.parse(this.enter(() => this.ex.run(computation.runner)))] };
} catch (error) {
if (error instanceof NotReady) throw new Error("rocx: a component read a value that isn't in yet outside its markup: read it in a hole ({…}), which waits");
if (!(error instanceof Failed)) throw error;
this.failed(computation, error);
this.reclaim(error);
return { computation, nodes: [] };
} finally {
this.current = previous;
this.place = place;
computation.made = computation.making;
computation.making = null;
}
}
mount(container) {
const range = makeRange("app");
container.append(range.fragment);
this.root = new Computation(this, { kind: "root", owner: null, scope: {}, target: range });
this.run(this.root);
}
live() {
return Number(this.ex.live_allocations());
}
notes() {
return { kept: this.ex.notes_kept(), room: this.ex.notes_room() };
}
allocations() {
return Number(this.ex.allocations());
}
}
