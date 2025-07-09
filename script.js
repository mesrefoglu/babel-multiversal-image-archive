const g = (id) => document.getElementById(id);
const menu = g("menu"),
    banner = g("banner"),
    locFlow = g("loc-flow"),
    locLabel = g("loc-label"),
    locInput = g("loc-input"),
    locNext = g("loc-next");
const groupMap = g("group-map"),
    galaxyMap = g("galaxy-map"),
    armMap = g("arm-map"),
    planetMap = g("planet-map"),
    continentMap = g("continent-map"),
    countryMap = g("country-map"),
    libraryMap = g("library-map"),
    floorMap = g("floor-map"),
    sectionMap = g("section-map"),
    bookcaseMap = g("bookcase-map"),
    shelfMap = g("shelf-map"),
    bookMap = g("book-map"),
    chapterMap = g("chapter-map"),
    pageMap = g("page-map"),
    imageMenu = g("image-menu"),
    imgUpload = g("img-upload"),
    filePick = g("filePick");

const alphabet = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz?!";
let stage = -1,
    result = "";
const STAGE_TEXT = [
    "~9.4 x 10^1,806,179 multiverses",
    "~6.7 x 10^413,208 universes",
    "1,073,741,824 clusters",
    "64 galaxy groups",
    "64 galaxies",
    "64 arms",
    "68,719,476,736 billion stars",
    "64 planets",
    "64 continents",
    "64 countries",
    "64 libraries",
    "64 floors",
    "64 sections",
    "64 bookcases",
    "64 shelves",
    "64 books",
    "64 chapters",
    "64 pages",
];
function setBanner(i) {
    banner.textContent = STAGE_TEXT[i] || "";
}
function show(e) {
    e.classList.remove("hidden");
}
function hide(e) {
    e.classList.add("hidden");
}
function processIdInput(s) {
    return [...s].filter((ch) => alphabet.includes(ch)).join("");
}
function addResult(t) {
    result += t + " ";
}

const nPix = 307200,
    keyBytes = new Uint8Array(16),
    nonce = new Uint8Array(16),
    char2val = {};
[...alphabet].forEach((c, i) => (char2val[c] = i));
let keystream, perm, invPerm;
function mulberry32(a) {
    return () => {
        var t = (a += 0x6d2b79f5);
        t = (t ^= t >>> 15) * (t | 1);
        t ^= t + (t ^= t >>> 7) * (t | 61);
        return ((t ^= t >>> 14) >>> 0) / 4294967296;
    };
}
function genPerm() {
    perm = Array.from({ length: nPix }, (_, i) => i);
    const r = mulberry32(0xb00b1e5);
    for (let i = nPix - 1; i > 0; i--) {
        const j = Math.floor(r() * (i + 1));
        [perm[i], perm[j]] = [perm[j], perm[i]];
    }
    invPerm = new Uint32Array(nPix);
    perm.forEach((v, i) => (invPerm[v] = i));
}
async function initCrypto() {
    if (keystream) return;
    const key = await crypto.subtle.importKey("raw", keyBytes, "AES-CTR", !1, ["encrypt"]);
    const zero = new Uint8Array(921600);
    const ctr = { name: "AES-CTR", counter: nonce, length: 128 };
    keystream = new Uint8Array(await crypto.subtle.encrypt(ctr, key, zero));
    genPerm();
}

function codeStringToBytes(str) {
    const out = new Uint8Array(921600);
    let byte = 0,
        bits = 0,
        idx = 0;
    for (const ch of str) {
        const v = char2val[ch];
        for (let b = 5; b >= 0; b--) {
            byte = (byte << 1) | ((v >> b) & 1);
            if (++bits === 8) {
                out[idx++] = byte;
                byte = 0;
                bits = 0;
            }
        }
    }
    return out;
}
function bytesToCodeString(bytes) {
    let buf = 0,
        bits = 0,
        res = "";
    for (const b of bytes) {
        buf = (buf << 8) | b;
        bits += 8;
        while (bits >= 6) {
            bits -= 6;
            res += alphabet[(buf >> bits) & 63];
        }
    }
    return res;
}

const half = 460800,
    rot = (x, s) => ((x << s) | (x >> (8 - s))) & 255;
function permuteBytes(src) {
    let L = src.slice(0, half),
        R = src.slice(half),
        t = new Uint8Array(half);
    for (let r = 1; r <= 4; r++) {
        for (let i = 0; i < half; i++) t[i] = rot(R[i], r);
        const nL = R,
            nR = new Uint8Array(half);
        for (let i = 0; i < half; i++) nR[i] = L[i] ^ t[i];
        L = nL;
        R = nR;
    }
    return Uint8Array.from([...L, ...R]);
}
function unpermuteBytes(src) {
    let L = src.slice(0, half),
        R = src.slice(half),
        t = new Uint8Array(half);
    for (let r = 4; r >= 1; r--) {
        for (let i = 0; i < half; i++) t[i] = rot(L[i], r);
        const pR = L,
            pL = new Uint8Array(half);
        for (let i = 0; i < half; i++) pL[i] = R[i] ^ t[i];
        L = pL;
        R = pR;
    }
    return Uint8Array.from([...L, ...R]);
}
function diffuseBytes(src) {
    const dst = src.slice();
    for (let p = 0; p < 3; p++) {
        for (let i = 1; i < dst.length; i++) dst[i] ^= rot(dst[i - 1], (p + 1) & 7);
        for (let i = dst.length - 2; i >= 0; i--) dst[i] ^= rot(dst[i + 1], (p + 4) & 7);
    }
    return dst;
}
function undiffuseBytes(src) {
    const dst = src.slice();
    for (let p = 2; p >= 0; p--) {
        for (let i = 0; i < dst.length - 1; i++) dst[i] ^= rot(dst[i + 1], (p + 4) & 7);
        for (let i = dst.length - 1; i >= 1; i--) dst[i] ^= rot(dst[i - 1], (p + 1) & 7);
    }
    return dst;
}
function mixBytes(codeBytes) {
    const scrambled = diffuseBytes(codeBytes);
    const mixed = permuteBytes(scrambled);
    const tmp = new Uint8ClampedArray(921600);
    for (let i = 0; i < 921600; i++) tmp[i] = mixed[i] ^ keystream[i];
    const img = new Uint8ClampedArray(921600);
    for (let p = 0; p < nPix; p++) {
        const s = p * 3,
            d = perm[p] * 3;
        img[d] = tmp[s];
        img[d + 1] = tmp[s + 1];
        img[d + 2] = tmp[s + 2];
    }
    return img;
}
function unmixBytes(imgBytes) {
    const tmp = new Uint8ClampedArray(921600);
    for (let p = 0; p < nPix; p++) {
        const s = p * 3,
            d = invPerm[p] * 3;
        tmp[d] = imgBytes[s];
        tmp[d + 1] = imgBytes[s + 1];
        tmp[d + 2] = imgBytes[s + 2];
    }
    const raw = new Uint8Array(921600);
    for (let i = 0; i < 921600; i++) raw[i] = tmp[i] ^ keystream[i];
    const descrambled = unpermuteBytes(raw);
    return undiffuseBytes(descrambled);
}

const CHARSET = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz?!",
    VAL2CHAR = CHARSET.split(""),
    CHAR2VAL = Object.fromEntries(VAL2CHAR.map((c, i) => [c, i])),
    RK = [0xa3c9e7, 0x1f4b83, 0x5d26b9, 0x7e019d, 0x43ab55, 0x2cd37f];
function F(x, k) {
    return (((((x << 3) | (x >>> 21)) ^ k) + (x & 0x3f) * 0x45d9f3) & 0xffffff) >>> 0;
}
function pack4(a, o) {
    return ((a[o] << 18) | (a[o + 1] << 12) | (a[o + 2] << 6) | a[o + 3]) >>> 0;
}
function unpack4(v, out, o) {
    out[o + 3] = v & 63;
    out[o + 2] = (v >>> 6) & 63;
    out[o + 1] = (v >>> 12) & 63;
    out[o] = (v >>> 18) & 63;
}
function encBlock(L, R) {
    for (let k of RK) [L, R] = [R, (L ^ F(R, k)) & 0xffffff];
    return [L, R];
}
function decBlock(L, R) {
    [L, R] = [R, L];
    for (let i = 5; i >= 0; --i) [L, R] = [R, (L ^ F(R, RK[i])) & 0xffffff];
    return [R, L];
}
function encode(str) {
    if (str.length % 8) throw new Error("Length (" + str.length + ") must be multiple of 8");
    const v = Uint8Array.from(str, (c) => {
        const n = CHAR2VAL[c];
        if (n === undefined) throw new Error(`Illegal char "${c}"`);
        return n;
    });
    const tmp = new Uint32Array(v.length / 4);
    const out = new Uint8Array(v.length);
    let pL = 0,
        pR = 0;
    for (let i = 0, t = 0; i < v.length; i += 8, t += 2) {
        let L = pack4(v, i) ^ pL;
        let R = pack4(v, i + 4) ^ pR;
        [L, R] = encBlock(L, R);
        tmp[t] = L;
        tmp[t + 1] = R;
        pL = L;
        pR = R;
    }
    let nL = 0,
        nR = 0;
    for (let i = tmp.length - 2, o = v.length - 8; i >= 0; i -= 2, o -= 8) {
        let L = tmp[i] ^ nL;
        let R = tmp[i + 1] ^ nR;
        nL = L;
        nR = R;
        unpack4(L, out, o);
        unpack4(R, out, o + 4);
    }
    return Array.from(out, (n) => VAL2CHAR[n]).join("");
}
function decode(str) {
    if (str.length % 8) throw new Error("Length (" + str.length + ") must be multiple of 8");
    const v = Uint8Array.from(str, (c) => {
        const n = CHAR2VAL[c];
        if (n === undefined) throw new Error(`Illegal char "${c}"`);
        return n;
    });
    const tmp = new Uint32Array(v.length / 4);
    const out = new Uint8Array(v.length);
    let nL = 0,
        nR = 0;
    for (let i = v.length - 8, t = tmp.length - 2; i >= 0; i -= 8, t -= 2) {
        const cL = pack4(v, i),
            cR = pack4(v, i + 4);
        const L = cL ^ nL,
            R = cR ^ nR;
        nL = cL;
        nR = cR;
        tmp[t] = L;
        tmp[t + 1] = R;
    }
    let pL = 0,
        pR = 0;
    for (let i = 0, o = 0; i < tmp.length; i += 2, o += 8) {
        let [L, R] = decBlock(tmp[i], tmp[i + 1]);
        L ^= pL;
        R ^= pR;
        pL = tmp[i];
        pR = tmp[i + 1];
        unpack4(L, out, o);
        unpack4(R, out, o + 4);
    }
    return Array.from(out, (n) => VAL2CHAR[n]).join("");
}

document.getElementById("loc-btn").onclick = () => {
    hide(menu);
    show(banner);
    show(locFlow);
    stage = 0;
    setBanner(stage);
    locLabel.textContent = "Enter multiverse ID:";
    locInput.value = "";
    locInput.maxLength = 1e6;
    locInput.focus();
};
document.getElementById("img-btn").onclick = () => {
    hide(menu);
    hide(banner);
    show(imgUpload);
};
filePick.onchange = (e) => {
    const f = e.target.files[0];
    if (f) handleImageFile(f);
};

locNext.onclick = () => {
    const c = processIdInput(locInput.value);
    if (!c) return;
    addResult(c);
    if (stage === 0) {
        stage = 1;
        setBanner(stage);
        locLabel.textContent = "Enter universe ID:";
        locInput.value = "";
        locInput.maxLength = 228775;
        locInput.focus();
    } else if (stage === 1) {
        stage = 2;
        setBanner(stage);
        locLabel.textContent = "Enter cluster ID:";
        locInput.value = "";
        locInput.maxLength = 5;
        locInput.focus();
    } else if (stage === 2) {
        hide(locFlow);
        renderGroups();
    } else if (stage === 6) {
        hide(locFlow);
        renderPlanets();
    }
};

function gridSize() {
    const c = 8,
        r = 8;
    return { c, r, w: innerWidth / (c + 2), h: innerHeight / (r + 2) };
}
function placeGrid(p, cls, fn) {
    const { c, r, w, h } = gridSize();
    p.innerHTML = "";
    for (let y = 0; y < r; y++)
        for (let x = 0; x < c; x++) {
            const id = y * c + x,
                d = document.createElement("div");
            d.className = cls;
            d.textContent = alphabet[id];
            d.style.left = (x + 1) * w + (w - 64) / 2 + "px";
            d.style.top = (y + 1) * h + (h - 64) / 2 + "px";
            d.onclick = () => fn(id);
            p.appendChild(d);
        }
}
function renderGroups() {
    stage = 3;
    setBanner(stage);
    hide(locFlow);
    show(groupMap);
    placeGrid(groupMap, "group", (i) => {
        addResult(alphabet[i]);
        renderGalaxies();
    });
}
function renderGalaxies() {
    stage = 4;
    setBanner(stage);
    hide(groupMap);
    show(galaxyMap);
    placeGrid(galaxyMap, "galaxy", (i) => {
        addResult(alphabet[i]);
        renderArms();
    });
}
function renderArms() {
    stage = 5;
    setBanner(stage);
    hide(galaxyMap);
    show(armMap);
    armMap.innerHTML = "";
    for (let i = 0; i < 64; i++) {
        const a = (i * 360) / 64,
            d = document.createElement("div");
        d.className = "arm";
        d.style.transform = `rotate(${a}deg)`;
        const s = document.createElement("span");
        s.textContent = alphabet[i];
        s.style.transform = `rotate(${-a}deg)`;
        s.style.marginLeft = "5px";
        d.appendChild(s);
        d.onclick = () => {
            addResult(alphabet[i]);
            renderStarPrompt();
        };
        armMap.appendChild(d);
    }
}
function renderStarPrompt() {
    stage = 6;
    setBanner(stage);
    hide(armMap);
    show(locFlow);
    locLabel.textContent = "Enter star ID:";
    locInput.value = "";
    locInput.maxLength = 6;
    locInput.focus();
}
function renderPlanets() {
    stage = 7;
    setBanner(stage);
    hide(armMap);
    show(planetMap);
    placeGrid(planetMap, "planet", (i) => {
        addResult(alphabet[i]);
        renderContinents();
    });
}
function renderContinents() {
    stage = 8;
    setBanner(stage);
    hide(planetMap);
    show(continentMap);
    placeGrid(continentMap, "continent", (i) => {
        addResult(alphabet[i]);
        renderCountries();
    });
}
function renderCountries() {
    stage = 9;
    setBanner(stage);
    hide(continentMap);
    show(countryMap);
    placeGrid(countryMap, "country", (i) => {
        addResult(alphabet[i]);
        renderLibraries();
    });
}
function renderLibraries() {
    stage = 10;
    setBanner(stage);
    hide(countryMap);
    show(libraryMap);
    placeGrid(libraryMap, "library", (i) => {
        addResult(alphabet[i]);
        renderFloors();
    });
}
function renderFloors() {
    stage = 11;
    setBanner(stage);
    hide(libraryMap);
    show(floorMap);
    floorMap.innerHTML = "";
    for (let i = 63; i >= 0; i--) {
        const d = document.createElement("div");
        d.className = "floor " + (i % 2 ? "right" : "left");
        const s = document.createElement("span");
        s.textContent = alphabet[i];
        d.appendChild(s);
        d.onclick = () => {
            addResult(alphabet[i]);
            renderSections();
        };
        floorMap.appendChild(d);
    }
}
function renderSections() {
    stage = 12;
    setBanner(stage);
    hide(floorMap);
    show(sectionMap);
    placeGrid(sectionMap, "section", (i) => {
        addResult(alphabet[i]);
        renderBookcases();
    });
}
function renderBookcases() {
    stage = 13;
    setBanner(stage);
    hide(sectionMap);
    show(bookcaseMap);
    placeGrid(bookcaseMap, "bookcase", (i) => {
        addResult(alphabet[i]);
        renderShelves();
    });
}
function renderShelves() {
    stage = 14;
    setBanner(stage);
    hide(bookcaseMap);
    show(shelfMap);
    shelfMap.innerHTML = "";
    for (let i = 63; i >= 0; i--) {
        const d = document.createElement("div");
        d.className = "shelf " + (i % 2 ? "right" : "left");
        const s = document.createElement("span");
        s.textContent = alphabet[i];
        d.appendChild(s);
        d.onclick = () => {
            addResult(alphabet[i]);
            renderBooks();
        };
        shelfMap.appendChild(d);
    }
}
function renderBooks() {
    stage = 15;
    setBanner(stage);
    hide(shelfMap);
    show(bookMap);
    placeGrid(bookMap, "book", (i) => {
        addResult(alphabet[i]);
        renderChapters();
    });
}
function renderChapters() {
    stage = 16;
    setBanner(stage);
    hide(bookMap);
    show(chapterMap);
    placeGrid(chapterMap, "chapter", (i) => {
        addResult(alphabet[i]);
        renderPages();
    });
}
function renderPages() {
    stage = 17;
    setBanner(stage);
    hide(chapterMap);
    show(pageMap);
    placeGrid(pageMap, "page", (i) => {
        addResult(alphabet[i]);
        renderImage();
    });
}

function renderImage() {
    initCrypto().then(() => {
        hide(pageMap);
        hide(imgUpload);
        show(imageMenu);
        imageMenu.innerHTML = "";
        const labels = [
            "Multiverse ID",
            "Universe ID",
            "Cluster ID",
            "Galaxy group",
            "Galaxy",
            "Arm",
            "Star ID",
            "Planet",
            "Continent",
            "Country",
            "Library",
            "Floor",
            "Section",
            "Bookcase",
            "Shelf",
            "Book",
            "Chapter",
            "Page",
        ];
        const cvs = document.createElement("canvas");
        cvs.width = 640;
        cvs.height = 480;
        const ctx = cvs.getContext("2d"),
            rgba = ctx.createImageData(640, 480);
        imageMenu.appendChild(cvs);
        const rows = [document.createElement("div"), document.createElement("div"), document.createElement("div")];
        rows.forEach((r) => {
            r.className = "addr-row";
            imageMenu.appendChild(r);
        });
        const parts = result.trim().split(" ").slice(0, 18);
        while (parts.length < 18) parts.push("0");
        function rebuild() {
            const vals = [...document.querySelectorAll(".code-inp")].map((v) => processIdInput(v.value) || "0");
            const base =
                vals[0].padStart(1e6, "0") +
                vals[1].padStart(228775, "0") +
                vals[2].padStart(5, "0") +
                vals.slice(3, 6).join("") +
                vals[6].padStart(6, "0") +
                vals.slice(7).join("");
            const enc = encode(encode(base));
            const img = mixBytes(codeStringToBytes(enc));
            for (let i = 0, j = 0; i < img.length; i += 3, j += 4) {
                rgba.data[j] = img[i];
                rgba.data[j + 1] = img[i + 1];
                rgba.data[j + 2] = img[i + 2];
                rgba.data[j + 3] = 255;
            }
            ctx.putImageData(rgba, 0, 0);
            result = vals.map((v) => v.replace(/^0+/, "") || "0").join(" ") + " ";
        }
        parts.forEach((v, i) => {
            const w = document.createElement("div");
            w.className = "addr-item";
            const l = document.createElement("span");
            l.textContent = labels[i];
            const inp = document.createElement("input");
            inp.value = v;
            inp.className = "code-inp";
            inp.oninput = rebuild;
            if (i == 0) inp.maxLength = 1e7;
            else if (i == 1) inp.maxLength = 228775;
            else if (i == 2) inp.maxLength = 5;
            else if (i == 6) inp.maxLength = 6;
            else inp.maxLength = 1;
            w.append(l, inp);
            (i < 6 ? rows[0] : i < 12 ? rows[1] : rows[2]).appendChild(w);
        });
        rebuild();
        banner.textContent = "";
    });
}

async function handleImageFile(file) {
    await initCrypto();
    hide(imgUpload);
    show(banner);
    banner.textContent = "Decoding…";
    const url = URL.createObjectURL(file),
        img = new Image();
    img.src = url;
    await img.decode();
    const cvs = document.createElement("canvas");
    cvs.width = 640;
    cvs.height = 480;
    const ctx = cvs.getContext("2d");
    const s = Math.min(640 / img.width, 480 / img.height),
        nw = img.width * s,
        nh = img.height * s,
        ox = (640 - nw) / 2,
        oy = (480 - nh) / 2;
    ctx.fillStyle = "#000";
    ctx.fillRect(0, 0, 640, 480);
    ctx.drawImage(img, ox, oy, nw, nh);
    const rgba = ctx.getImageData(0, 0, 640, 480).data;
    const pix = new Uint8Array(921600);
    for (let i = 0, j = 0; i < rgba.length; i += 4) {
        pix[j++] = rgba[i];
        pix[j++] = rgba[i + 1];
        pix[j++] = rgba[i + 2];
    }
    const codeBytes = unmixBytes(pix);
    const encCode = bytesToCodeString(codeBytes);
    const codeStr = decode(decode(encCode));
    const ids = [];
    let p = 0;
    ids.push(codeStr.slice(p, p + 1e6).replace(/^0+/, "") || "0");
    p += 1e6;
    ids.push(codeStr.slice(p, p + 228775).replace(/^0+/, "") || "0");
    p += 228775;
    ids.push(codeStr.slice(p, p + 5).replace(/^0+/, "") || "0");
    p += 5;
    ids.push(codeStr[p++]);
    ids.push(codeStr[p++]);
    ids.push(codeStr[p++]);
    ids.push(codeStr.slice(p, p + 6).replace(/^0+/, "") || "0");
    p += 6;
    while (p < codeStr.length) ids.push(codeStr[p++]);
    result = ids.join(" ") + " ";
    renderImage();
}
