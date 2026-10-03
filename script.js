/* =========================================================
   VENTUS LOCAL-ONLY VERSION
   - No Supabase / no cloud / no external services
   - Automatic localStorage saving
   - Password protected product deletion and full reset
   - Monthly/yearly production & selling history
   - Product editing
   - JSON Backup / Restore
========================================================= */

const PRODUCTS_KEY = "ventusProducts";
const HISTORY_KEY = "ventusHistory";
const PASSWORD_KEY = "ventusPasswordHash";
const SESSION_KEY = "ventusLocalSession";
const VERSION_KEY = "ventusLocalVersion";
const CURRENT_VERSION = 5;
const DEFAULT_PASSWORD = "admin123";

let products = [];
let history = [];
let editingProductId = null;

const $ = id => document.getElementById(id);

function esc(v) { return String(v ?? "").replace(/[&<>'"]/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;","'":"&#39;","\"":"&quot;"}[c])); }
function setSyncStatus(text) { if ($("syncStatus")) $("syncStatus").textContent = text; }
function showAuthError(message) { const el=$("authError"); el.textContent=message||"Something went wrong."; el.style.display="block"; }
function clearAuthError() { const el=$("authError"); if(el) el.style.display="none"; }

function getMovementDate(item) {
  const d = new Date(item.timestamp || item.date || "");
  return isNaN(d.getTime()) ? null : d;
}

function movementRecord(product, type, quantity, movementDate=null) {
  const now = movementDate instanceof Date && !isNaN(movementDate.getTime()) ? movementDate : new Date();
  return {
    id: "m_" + Date.now() + "_" + Math.random().toString(36).slice(2,8),
    product: product.name,
    productId: String(product.id),
    type,
    quantity: Number(quantity) || 0,
    timestamp: now.toISOString(),
    date: now.toLocaleDateString("en-IN", {day:"2-digit", month:"short", year:"numeric"})
  };
}

/* Local-file-safe SHA-256 implementation.
   The previous version relied on crypto.subtle, which can be unavailable
   when an HTML file is opened directly with file:// in some browsers. */
function sha256(text) {
  function rotr(n,x){return (x>>>n)|(x<<(32-n));}
  const K=[
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
  ];
  let bytes=[];
  for(let i=0;i<text.length;i++){
    let c=text.charCodeAt(i);
    if(c<0x80) bytes.push(c);
    else if(c<0x800){bytes.push(0xc0|(c>>6),0x80|(c&63));}
    else if(c>=0xd800&&c<=0xdbff&&i+1<text.length){
      const d=text.charCodeAt(++i); const cp=0x10000+((c-0xd800)<<10)+(d-0xdc00);
      bytes.push(0xf0|(cp>>18),0x80|((cp>>12)&63),0x80|((cp>>6)&63),0x80|(cp&63));
    } else bytes.push(0xe0|(c>>12),0x80|((c>>6)&63),0x80|(c&63));
  }
  const bitLen=bytes.length*8; bytes.push(0x80);
  while((bytes.length%64)!==56) bytes.push(0);
  for(let i=7;i>=0;i--) bytes.push((bitLen/Math.pow(2,8*i))&255);
  let h0=0x6a09e667,h1=0xbb67ae85,h2=0x3c6ef372,h3=0xa54ff53a,h4=0x510e527f,h5=0x9b05688c,h6=0x1f83d9ab,h7=0x5be0cd19;
  for(let off=0;off<bytes.length;off+=64){
    const w=new Uint32Array(64);
    for(let i=0;i<16;i++){const j=off+i*4;w[i]=((bytes[j]<<24)|(bytes[j+1]<<16)|(bytes[j+2]<<8)|bytes[j+3])>>>0;}
    for(let i=16;i<64;i++){const x=w[i-15],y=w[i-2];const s0=(rotr(7,x)^rotr(18,x)^(x>>>3))>>>0;const s1=(rotr(17,y)^rotr(19,y)^(y>>>10))>>>0;w[i]=(w[i-16]+s0+w[i-7]+s1)>>>0;}
    let a=h0,b=h1,c=h2,d=h3,e=h4,f=h5,g=h6,h=h7;
    for(let i=0;i<64;i++){const S1=(rotr(6,e)^rotr(11,e)^rotr(25,e))>>>0;const ch=((e&f)^((~e)&g))>>>0;const t1=(h+S1+ch+K[i]+w[i])>>>0;const S0=(rotr(2,a)^rotr(13,a)^rotr(22,a))>>>0;const maj=((a&b)^(a&c)^(b&c))>>>0;const t2=(S0+maj)>>>0;h=g;g=f;f=e;e=(d+t1)>>>0;d=c;c=b;b=a;a=(t1+t2)>>>0;}
    h0=(h0+a)>>>0;h1=(h1+b)>>>0;h2=(h2+c)>>>0;h3=(h3+d)>>>0;h4=(h4+e)>>>0;h5=(h5+f)>>>0;h6=(h6+g)>>>0;h7=(h7+h)>>>0;
  }
  return [h0,h1,h2,h3,h4,h5,h6,h7].map(x=>x.toString(16).padStart(8,"0")).join("");
}

async function ensurePassword() {
  if (!localStorage.getItem(PASSWORD_KEY)) {
    localStorage.setItem(PASSWORD_KEY, sha256(DEFAULT_PASSWORD));
  }
}

function normalizeData() {
  if (!Array.isArray(products)) products=[];
  if (!Array.isArray(history)) history=[];
  products = products.map((p,i)=>({
    id:String(p.id ?? (Date.now()+i)),
    name:String(p.name ?? "Unnamed Product"),
    code:String(p.code ?? ("VP-"+(i+1).toString().padStart(4,"0"))),
    category:String(p.category ?? ""),
    size:String(p.size ?? ""),
    cartons:Number(p.cartons)||0,
    pieces:Number(p.pieces)||0,
    minimum:Number(p.minimum)||0,
    image:p.image||""
  }));
  history = history.map((h,i)=>{
    const d=getMovementDate(h)||new Date();
    return {
      id:String(h.id ?? ("m_"+i+"_"+Date.now())),
      product:String(h.product ?? "Unknown"),
      productId:h.productId!=null?String(h.productId):"",
      type:h.type==="out"?"out":"in",
      quantity:Number(h.quantity)||0,
      timestamp:(h.timestamp && !isNaN(new Date(h.timestamp).getTime())) ? new Date(h.timestamp).toISOString() : d.toISOString(),
      date:h.date||d.toLocaleDateString("en-IN",{day:"2-digit",month:"short",year:"numeric"})
    };
  });
}

function saveData(status="Saved locally") {
  try {
    normalizeData();
    localStorage.setItem(PRODUCTS_KEY, JSON.stringify(products));
    localStorage.setItem(HISTORY_KEY, JSON.stringify(history));
    localStorage.setItem(VERSION_KEY, String(CURRENT_VERSION));
    createAutoBackup();
    setSyncStatus(status);
    return true;
  } catch (e) {
    setSyncStatus("Save failed");
    alert("Could not save data in this browser. The browser storage may be full. Please create a Backup and remove unused data/images.");
    return false;
  }
}

function loadData() {
  try {
    products=JSON.parse(localStorage.getItem(PRODUCTS_KEY)||"[]");
    history=JSON.parse(localStorage.getItem(HISTORY_KEY)||"[]");
    normalizeData();
    saveData("Local data loaded");
  } catch(e) {
    products=[]; history=[]; saveData();
  }
}

function renderAll(){ renderProducts(); updateDashboard(); renderHistory(); renderProduction(); populateStockProducts(); populateReportYears(); renderReports(); }

function getAvailableReportYears() {
  const years = new Set();
  history.forEach(item=>{const d=getMovementDate(item); if(d) years.add(d.getFullYear());});
  years.add(new Date().getFullYear());
  years.add(2026);
  years.add(2027);
  return [...years].sort((a,b)=>b-a);
}

function populateReportYears() {
  const select=$("reportYear"); if(!select)return;
  const old=select.value;
  const years=getAvailableReportYears();
  select.innerHTML=years.map(y=>`<option value="${y}">${y}</option>`).join("");
  select.value=years.includes(Number(old))?old:String(years[0]);
}

function getReportMonths(year, monthValue="all") {
  const names=["January","February","March","April","May","June","July","August","September","October","November","December"];
  const months=monthValue==="all"?Array.from({length:12},(_,i)=>i):[Number(monthValue)];
  return months.map(month=>({year,month,name:names[month]}));
}

function movementForProductInPeriod(productId,year,month){
  let production=0,selling=0;
  history.forEach(item=>{
    if(String(item.productId)!==String(productId))return;
    const d=getMovementDate(item); if(!d||d.getFullYear()!==year||d.getMonth()!==month)return;
    if(item.type==="in")production+=Number(item.quantity)||0; else if(item.type==="out")selling+=Number(item.quantity)||0;
  });
  return {production,selling};
}

function closingStockForProduct(productId,year,month){
  const product=products.find(p=>String(p.id)===String(productId));
  if(!product)return 0;
  let closing=Number(product.cartons)||0;
  history.forEach(item=>{
    if(String(item.productId)!==String(productId))return;
    const d=getMovementDate(item); if(!d)return;
    const ym=d.getFullYear()*12+d.getMonth();
    const target=year*12+month;
    if(ym>target){
      const q=Number(item.quantity)||0;
      if(item.type==="in")closing-=q; else if(item.type==="out")closing+=q;
    }
  });
  return Math.max(0,closing);
}

function renderReports() {
  const yearEl=$('reportYear'), monthEl=$('reportMonth'), table=$('monthlyReportTable'), detail=$('productMonthlyReportTable');
  if(!yearEl||!monthEl||!table)return;
  const year=Number(yearEl.value), month=Number(monthEl.value);
  const names=['January','February','March','April','May','June','July','August','September','October','November','December'];
  if(Number.isNaN(year)||Number.isNaN(month))return;

  let production=0, selling=0;
  history.forEach(item=>{
    const d=getMovementDate(item);
    if(!d||d.getFullYear()!==year||d.getMonth()!==month)return;
    if(item.type==='in')production+=Number(item.quantity)||0;
    if(item.type==='out')selling+=Number(item.quantity)||0;
  });
  const net=production-selling;
  table.innerHTML=`<tr><td><strong>${names[month]} ${year}</strong></td><td>${production} boxes</td><td>${selling} boxes</td><td>${net>=0?'+':''}${net} boxes</td></tr>`;
  $('reportProduction').textContent=`${production} boxes`;
  $('reportSelling').textContent=`${selling} boxes`;
  $('reportNet').textContent=`${net>=0?'+':''}${net} boxes`;

  if(detail){
    let html='';
    products.forEach(product=>{
      const mv=movementForProductInPeriod(product.id,year,month);
      const remaining=closingStockForProduct(product.id,year,month);
      const opening=Math.max(0,remaining-mv.production+mv.selling);
      const produceRequired=Math.max(0,Number(product.minimum||0)-remaining);
      if(mv.production||mv.selling||remaining||opening||produceRequired){
        html+=`<tr><td>${names[month]} ${year}</td><td><strong>${esc(product.name)}</strong></td><td>${opening}</td><td>${mv.production}</td><td>${mv.selling}</td><td><strong>${remaining}</strong></td><td>${produceRequired}</td></tr>`;
      }
    });
    detail.innerHTML=html||`<tr><td colspan="7">No product movement or stock data for ${names[month]} ${year}.</td></tr>`;
  }
}

function printSelectedReport(){
  renderReports();
  document.body.classList.add('printing-report');
  setTimeout(()=>{
    window.print();
    document.body.classList.remove('printing-report');
  },50);
}
window.printSelectedReport=printSelectedReport;

function renderProducts(list=products) {
  const table=$("inventoryTable"); if(!table)return; table.innerHTML="";
  list.forEach(product=>{
    let status="In Stock",badge="badge-green";
    if(Number(product.cartons)<=0){status="Out of Stock";badge="badge-red";}else if(Number(product.cartons)<=Number(product.minimum)){status="Low Stock";badge="badge-yellow";}
    const imageHTML=product.image?`<img src="${product.image}" style="width:45px;height:45px;object-fit:cover;border-radius:8px">`:"📦";
    table.innerHTML+=`<tr><td><div class="product"><div class="product-img">${imageHTML}</div><div><div class="product-name">${esc(product.name)}</div><div class="product-code">${esc(product.code)}</div></div></div></td><td>${esc(product.category)}</td><td>${esc(product.size)}</td><td><strong>${Number(product.cartons)||0}</strong></td><td>${Number(product.pieces)||0}</td><td><span class="badge ${badge}">${status}</span></td><td><button class="btn-light" onclick="openEditProduct('${esc(product.id)}')">Edit</button> <button class="btn-light" onclick="quickStock('${esc(product.id)}','in')">+ IN</button> <button class="btn-light" onclick="quickStock('${esc(product.id)}','out')">− OUT</button> <button class="btn-danger" onclick="deleteProduct('${esc(product.id)}')">Delete</button></td></tr>`;
  });
}

function updateDashboard(){
  $("totalProducts").innerText=products.length;
  $("totalCartons").innerText=products.reduce((t,p)=>t+(Number(p.cartons)||0),0);
  $("lowStock").innerText=products.filter(p=>Number(p.cartons)<=Number(p.minimum)).length;
  $("productionRequired").innerText=products.reduce((t,p)=>t+Math.max(0,Number(p.minimum)-Number(p.cartons)),0);
}

function renderHistory(){
  const c=$("historyList");if(!c)return;c.innerHTML="";
  history.slice().sort((a,b)=>new Date(b.timestamp)-new Date(a.timestamp)).slice(0,6).forEach(item=>{c.innerHTML+=`<div class="history-item"><div><div class="history-name">${esc(item.product)}</div><div class="history-date">${esc(item.date)}</div></div><div class="${item.type==="in"?"stock-in":"stock-out"}">${item.type==="in"?"+":"-"} ${item.quantity} boxes</div></div>`;});
  if(!history.length)c.innerHTML=`<p style="color:var(--muted);">No stock movement yet.</p>`;
}

function renderProduction(){
  const c=$("productionList");if(!c)return;c.innerHTML="";
  const required=products.filter(p=>Number(p.cartons)<Number(p.minimum));
  if(!required.length){c.innerHTML=`<p style="color:#16a34a;">✓ No production required.</p>`;return;}
  required.forEach(p=>{const shortage=Number(p.minimum)-Number(p.cartons);c.innerHTML+=`<div class="history-item"><div><div class="history-name">${esc(p.name)}</div><div class="history-date">Available: ${p.cartons} boxes</div></div><div class="stock-out">Produce ${shortage} boxes</div></div>`;});
}

function populateStockProducts(){
  const select=$("stockProduct");if(!select)return;
  select.innerHTML=products.map(p=>`<option value="${esc(p.id)}">${esc(p.name)} — ${p.cartons} boxes</option>`).join("");
}

function prepareProductModal(product=null){
  editingProductId=product?String(product.id):null;
  $("productModalTitle").textContent=product?"Edit Product":"Add Product";
  $("productSaveBtn").textContent=product?"Save Changes":"Add Product";
  $("productName").value=product?.name||"";
  $("productCategory").value=product?.category||"";
  $("productSize").value=product?.size||"";
  $("productCartons").value=product?Number(product.cartons)||0:"";
  $("productCartons").readOnly=!!product;
  $("productCartons").title=product?"Stock changes should use IN/OUT so history remains accurate.":"";
  $("productPieces").value=product?Number(product.pieces)||0:"";
  $("productMinimum").value=product?Number(product.minimum)||0:"";
  $("productImage").value="";
}

function openEditProduct(id){
  const product=products.find(p=>String(p.id)===String(id));
  if(!product){alert("Product not found.");return;}
  prepareProductModal(product);$("productModal").classList.add("show");
}
window.openEditProduct=openEditProduct;

function addProductFromForm(e){
  e.preventDefault();
  const file=$("productImage").files[0];
  const save=image=>{
    const existing=editingProductId?products.find(p=>String(p.id)===String(editingProductId)):null;
    const product={
      id:editingProductId||Date.now().toString(),
      name:$("productName").value.trim(),
      code:existing?.code||("VP-"+Date.now().toString().slice(-5)),
      category:$("productCategory").value.trim(),
      size:$("productSize").value.trim(),
      cartons:existing?Number(existing.cartons)||0:Number($("productCartons").value)||0,
      pieces:Number($("productPieces").value)||0,
      minimum:Number($("productMinimum").value)||0,
      image:image||existing?.image||""
    };
    if(!product.name){alert("Enter a product name.");return;}
    if(editingProductId){const idx=products.findIndex(p=>String(p.id)===String(editingProductId));if(idx>=0)products[idx]=product;}else products.push(product);
    saveData();renderAll();
    $("productForm").reset();editingProductId=null;$("productModalTitle").textContent="Add Product";$("productSaveBtn").textContent="Add Product";$("productCartons").readOnly=false;$("productCartons").title="";closeProductModal();
  };
  if(file){const r=new FileReader();r.onload=ev=>save(ev.target.result);r.readAsDataURL(file);}else save("");
}

function openPasswordModal(){
  const modal=$("passwordModal");
  if(!modal)return;
  $("passwordForm").reset();
  modal.classList.add("show");
  setTimeout(()=>$("currentPassword")?.focus(),50);
}

function closePasswordModal(){
  const modal=$("passwordModal");
  if(modal)modal.classList.remove("show");
}

async function changePasswordFromForm(e){
  e.preventDefault();

  const current=$("currentPassword").value;
  const next=$("newPassword").value;
  const confirmNext=$("confirmPassword").value;
  const stored=localStorage.getItem(PASSWORD_KEY);

  if(!current || !next || !confirmNext){
    alert("Please fill in all password fields.");
    return;
  }

  if(sha256(current)!==stored){
    alert("Current password is incorrect.");
    $("currentPassword").focus();
    return;
  }

  if(next.length<4){
    alert("New password must be at least 4 characters.");
    $("newPassword").focus();
    return;
  }

  if(next!==confirmNext){
    alert("New password and confirmation do not match.");
    $("confirmPassword").focus();
    return;
  }

  if(next===current){
    alert("New password must be different from the current password.");
    $("newPassword").focus();
    return;
  }

  try{
    createAutoBackup();
    localStorage.setItem(PASSWORD_KEY,sha256(next));
    localStorage.setItem(VERSION_KEY,String(CURRENT_VERSION));
    setSyncStatus("Password changed");
    closePasswordModal();
    alert("Password changed successfully.");
  }catch(err){
    console.error(err);
    alert("Could not change the password. Please try again.");
  }
}

function deleteProduct(productId){
  const product=products.find(p=>String(p.id)===String(productId));
  if(!product){alert("Product not found.");return;}
  const password=prompt("Enter the protection password to delete this product:");
  if(password===null)return;
  if(sha256(password)!==localStorage.getItem(PASSWORD_KEY)){alert("Incorrect password. Product was not deleted.");return;}
  createAutoBackup(); if(!confirm(`Delete product "${product.name}"? Existing Production/Selling history will be kept.`))return;
  products=products.filter(p=>String(p.id)!==String(productId));
  saveData("Product deleted");
  renderAll();
  alert("Product deleted successfully.");
}
window.deleteProduct=deleteProduct;

function recordMovement(productId,type,quantity,movementDate=null,historyOnly=false){
  const product=products.find(p=>String(p.id)===String(productId));
  if(!product)throw new Error("Product not found.");
  const qty=Number(quantity)||0;
  if(qty<=0)throw new Error("Quantity must be greater than 0.");
  const dt=movementDate?new Date(movementDate+"T12:00:00"):new Date();
  if(isNaN(dt.getTime()))throw new Error("Invalid movement date.");
  if(!historyOnly && type==="out" && qty>Number(product.cartons||0))throw new Error(`Not enough stock. Available: ${product.cartons} boxes.`);
  if(!historyOnly){
    if(type==="in")product.cartons=Number(product.cartons||0)+qty;
    else product.cartons=Math.max(0,Number(product.cartons||0)-qty);
  }
  history.unshift(movementRecord(product,type,qty,dt));
  saveData();renderAll();
}

function quickStock(id,type){
  const quantity=prompt(type==="in"?"How many boxes are coming IN?":"How many boxes are going OUT?");
  if(quantity===null||quantity===""||Number(quantity)<=0)return;
  try{recordMovement(id,type,Number(quantity),null,false);}catch(e){alert(e.message);}
}
window.quickStock=quickStock;

function openStockModal(){populateStockProducts(); const d=new Date(); const local=new Date(d.getTime()-d.getTimezoneOffset()*60000).toISOString().slice(0,10); $("stockDate").value=local; $("historyOnlyMovement").checked=false; $("stockModal").classList.add("show");}
function closeStockModal(){$("stockModal").classList.remove("show");}
window.openStockModal=openStockModal;window.closeStockModal=closeStockModal;
function openProductModal(){prepareProductModal();$("productModal").classList.add("show");}
function closeProductModal(){editingProductId=null;$("productModal").classList.remove("show");}
window.openProductModal=openProductModal;window.closeProductModal=closeProductModal;

async function resetAllData(){
  const password=prompt("Enter your password to reset stock amounts and Production/Selling history:");
  if(password===null)return;
  const stored=localStorage.getItem(PASSWORD_KEY);
  if(sha256(password)!==stored){alert("Incorrect password. Nothing was reset.");return;}
  createAutoBackup(); if(!confirm("WARNING: This will set ALL current stock amounts to 0 and permanently delete ALL Production & Selling history. Product names/settings will remain. Continue?"))return;
  products.forEach(p=>p.cartons=0);
  history=[];
  saveData();renderAll();
  alert("Stock amounts and Production/Selling history have been reset. Nothing will reset automatically.");
}
window.resetAllData=resetAllData;

/* ================================================================
   LINKED BACKUP FILE
   Click Backup once to choose a JSON file. After that, every saved
   inventory change updates that same file automatically when the
   browser supports the File System Access API (Chrome/Edge).
   A localStorage snapshot is also kept as an emergency copy.
================================================================ */

const BACKUP_DB_NAME = "VentusBackupDB";
const BACKUP_DB_STORE = "handles";
const BACKUP_HANDLE_KEY = "backupFileHandle";

function buildBackupObject(type="automatic"){
  normalizeData();
  return {
    app:"THE VENTUS PACKING",
    version:CURRENT_VERSION,
    backupType:type,
    savedAt:new Date().toISOString(),
    products:JSON.parse(JSON.stringify(products)),
    history:JSON.parse(JSON.stringify(history))
  };
}

function createAutoBackup(){
  try {
    const snapshot=buildBackupObject("automatic");
    localStorage.setItem(AUTO_BACKUP_KEY,JSON.stringify(snapshot));
    localStorage.setItem(AUTO_BACKUP_TIME_KEY,snapshot.savedAt);
    updateLinkedBackup(snapshot);
  } catch(e) {
    console.warn("Automatic backup snapshot failed",e);
  }
}

function getAutoBackup(){
  try { return JSON.parse(localStorage.getItem(AUTO_BACKUP_KEY)||"null"); }
  catch(e) { return null; }
}

function openBackupDB(){
  return new Promise((resolve,reject)=>{
    if(!("indexedDB" in window)){resolve(null);return;}
    const req=indexedDB.open(BACKUP_DB_NAME,1);
    req.onupgradeneeded=()=>{ if(!req.result.objectStoreNames.contains(BACKUP_DB_STORE)) req.result.createObjectStore(BACKUP_DB_STORE); };
    req.onsuccess=()=>resolve(req.result);
    req.onerror=()=>reject(req.error);
  });
}

async function storeBackupHandle(handle){
  try{
    const db=await openBackupDB();
    if(!db)return false;
    await new Promise((resolve,reject)=>{
      const tx=db.transaction(BACKUP_DB_STORE,"readwrite");
      tx.objectStore(BACKUP_DB_STORE).put(handle,BACKUP_HANDLE_KEY);
      tx.oncomplete=resolve; tx.onerror=()=>reject(tx.error);
    });
    return true;
  }catch(e){console.warn("Could not store backup file handle",e);return false;}
}

async function getStoredBackupHandle(){
  try{
    const db=await openBackupDB();
    if(!db)return null;
    return await new Promise((resolve,reject)=>{
      const tx=db.transaction(BACKUP_DB_STORE,"readonly");
      const req=tx.objectStore(BACKUP_DB_STORE).get(BACKUP_HANDLE_KEY);
      req.onsuccess=()=>resolve(req.result||null);
      req.onerror=()=>reject(req.error);
    });
  }catch(e){return null;}
}

async function writeBackupFile(handle, backup){
  if(!handle || !handle.createWritable) return false;
  try{
    if(handle.queryPermission){
      const permission=await handle.queryPermission({mode:"readwrite"});
      if(permission!=="granted"){
        /* Do not request permission during normal auto-save because that
           would require a user gesture in some browsers. */
        return false;
      }
    }
    const writable=await handle.createWritable();
    await writable.write(JSON.stringify(backup,null,2));
    await writable.close();
    return true;
  }catch(e){
    console.warn("Linked backup update failed",e);
    return false;
  }
}

async function updateLinkedBackup(backup){
  const handle=await getStoredBackupHandle();
  if(!handle){
    updateBackupStatus("Backup not linked yet — click Backup once.");
    return false;
  }
  const ok=await writeBackupFile(handle,backup);
  if(ok){
    updateBackupStatus("✓ Backup file updated automatically • "+new Date(backup.savedAt).toLocaleString());
    return true;
  }
  updateBackupStatus("Backup file needs permission — click Backup to reconnect it.");
  return false;
}

function updateBackupStatus(message){
  const el=$("autoBackupStatus");
  if(el)el.textContent=message;
}

async function backupData(){
  const backup=buildBackupObject("linked");
  try{
    /* If a backup file was already linked, keep using that exact same file. */
    const existing=await getStoredBackupHandle();
    if(existing && window.showSaveFilePicker){
      const ok=await writeBackupFileWithPermission(existing,backup);
      if(ok){
        localStorage.setItem(AUTO_BACKUP_KEY,JSON.stringify(backup));
        localStorage.setItem(AUTO_BACKUP_TIME_KEY,backup.savedAt);
        updateBackupStatus("✓ Existing backup file updated.");
        setSyncStatus("Backup file updated");
        return;
      }
    }

    if(window.showSaveFilePicker){
      const handle=await window.showSaveFilePicker({
        suggestedName:"THE-VENTUS-PACKING-backup.json",
        types:[{
          description:"Ventus Packing Backup",
          accept:{"application/json":[".json"]}
        }]
      });
      const ok=await writeBackupFileWithPermission(handle,backup);
      if(!ok)throw new Error("The selected backup file could not be written.");
      await storeBackupHandle(handle);
      localStorage.setItem(AUTO_BACKUP_KEY,JSON.stringify(backup));
      localStorage.setItem(AUTO_BACKUP_TIME_KEY,backup.savedAt);
      updateBackupStatus("✓ Backup linked. This same file will update automatically after every change.");
      setSyncStatus("Backup linked and saved");
      return;
    }

    /* Fallback for browsers without File System Access API. */
    downloadBackupObject(backup,"THE-VENTUS-PACKING-backup");
    updateBackupStatus("Downloaded backup. This browser cannot automatically update the downloaded file.");
    setSyncStatus("Backup downloaded");
  }catch(e){
    if(e && e.name==="AbortError") return;
    alert("Backup could not be created: "+e.message);
  }
}
window.backupData=backupData;

async function writeBackupFileWithPermission(handle, backup){
  try{
    if(handle.requestPermission){
      const permission=await handle.requestPermission({mode:"readwrite"});
      if(permission!=="granted")return false;
    }
    const writable=await handle.createWritable();
    await writable.write(JSON.stringify(backup,null,2));
    await writable.close();
    return true;
  }catch(e){console.warn(e);return false;}
}

function downloadBackupObject(backup, filenamePrefix="ventus-backup"){
  if(!backup){alert("No backup is available yet.");return;}
  const blob=new Blob([JSON.stringify(backup,null,2)],{type:"application/json"});
  const url=URL.createObjectURL(blob);
  const a=document.createElement("a");
  a.href=url;
  a.download=`${filenamePrefix}-${new Date().toISOString().slice(0,19).replace(/[:T]/g,"-")}.json`;
  document.body.appendChild(a);a.click();a.remove();URL.revokeObjectURL(url);
}

function downloadAutoBackup(){
  const b=getAutoBackup();
  if(!b){alert("No automatic backup is available yet.");return;}
  downloadBackupObject(b,"THE-VENTUS-PACKING-auto-backup");
  setSyncStatus("Backup downloaded");
}
window.downloadAutoBackup=downloadAutoBackup;

function autoBackupStatus(){
  const t=localStorage.getItem(AUTO_BACKUP_TIME_KEY);
  return t ? `Automatic snapshot: ${new Date(t).toLocaleString()}` : "Automatic snapshot: not created yet";
}
window.autoBackupStatus=autoBackupStatus;

function openRestorePicker(){$("restoreFile").click();}
window.openRestorePicker=openRestorePicker;

function restoreFromObject(obj){
  if(!obj||!Array.isArray(obj.products)||!Array.isArray(obj.history))throw new Error("Invalid Ventus backup file.");
  products=obj.products;history=obj.history;normalizeData();saveData("Restored locally");renderAll();
}


function openPreviousMonthUpload(){
  const modal=$("previousMonthModal");
  if(!modal)return;
  const select=$("previousMonthProduct");
  select.innerHTML="";
  products.forEach(p=>{
    const opt=document.createElement("option");
    opt.value=p.id; opt.textContent=p.name; select.appendChild(opt);
  });
  $("previousMonthDate").value=new Date().toISOString().slice(0,10);
  $("previousMonthType").value="in";
  $("previousMonthBoxes").value="";
  modal.classList.add("show");
  setTimeout(()=>$('previousMonthDate')?.focus(),50);
}
window.openPreviousMonthUpload=openPreviousMonthUpload;
function closePreviousMonthUpload(){
  const modal=$("previousMonthModal");
  if(modal)modal.classList.remove("show");
}
window.closePreviousMonthUpload=closePreviousMonthUpload;
function addPreviousMonthRecord(e){
  e.preventDefault();
  const date=$("previousMonthDate").value;
  const productId=$("previousMonthProduct").value;
  const type=$("previousMonthType").value;
  const qty=Number($("previousMonthBoxes").value);
  const product=products.find(p=>String(p.id)===String(productId));
  if(!date||!product||!qty||qty<=0){alert("Please enter a valid date, product and boxes quantity.");return;}
  const dt=new Date(date+"T12:00:00");
  if(isNaN(dt.getTime())){alert("Please enter a valid date.");return;}
  history.unshift(movementRecord(product,type,qty,dt));
  saveData("Previous month data added");
  renderAll();
  alert(`Previous month data added for ${date}.`);
  $("previousMonthBoxes").value="";
  $("previousMonthDate").focus();
}

$("restoreFile").addEventListener("change",function(e){
  const file=e.target.files[0];if(!file)return;
  const reader=new FileReader();
  reader.onload=async ev=>{
    try{
      const obj=JSON.parse(ev.target.result);
      if(!confirm("Restore this backup? Your current local inventory and history will be replaced by the backup."))return;
      restoreFromObject(obj);alert("Backup restored successfully.");
    }catch(err){alert("Restore failed: "+err.message);}
    finally{e.target.value="";}
  };
  reader.readAsText(file);
});

function searchProducts(){const q=$("searchInput").value.toLowerCase();renderProducts(products.filter(p=>[p.name,p.code,p.category,p.size].some(v=>String(v||"").toLowerCase().includes(q))));}
function resetSearch(){$("searchInput").value="";renderProducts();}
window.searchProducts=searchProducts;window.resetSearch=resetSearch;

function setActiveNav(name){document.querySelectorAll(".nav-item[data-nav]").forEach(i=>i.classList.toggle("active",i.dataset.nav===name));}
function goToSection(name){
  setActiveNav(name);
  if(name==="dashboard")window.scrollTo({top:0,behavior:"smooth"});
  else if(name==="products")$("productsSection").scrollIntoView({behavior:"smooth",block:"start"});
  else if(name==="stock")openStockModal();
  else if(name==="production")$("productionSection").scrollIntoView({behavior:"smooth",block:"center"});
  else if(name==="history")$("historySection").scrollIntoView({behavior:"smooth",block:"center"});
  else if(name==="reports"){$("reportsSection").scrollIntoView({behavior:"smooth",block:"start"});renderReports();}
}
document.querySelectorAll(".nav-item[data-nav]").forEach(item=>item.addEventListener("click",()=>goToSection(item.dataset.nav)));

document.getElementById("productForm").addEventListener("submit", addProductFromForm);
document.getElementById("stockForm").addEventListener("submit", function(e){
  e.preventDefault();
  try{
    recordMovement($("stockProduct").value,$("stockType").value,Number($("stockQuantity").value),$("stockDate").value,$("historyOnlyMovement").checked);
    closeStockModal();
    alert("Stock movement saved successfully.");
  }catch(err){alert(err.message);}
});
document.getElementById("passwordForm").addEventListener("submit", changePasswordFromForm);

function showApp(){
  const nameEl=$("currentUserName"), emailEl=$("currentUserEmail"), avatarEl=$("currentUserAvatar");
  if(nameEl)nameEl.textContent="THE VENTUS PACKING";
  if(emailEl)emailEl.textContent="Local Inventory";
  if(avatarEl)avatarEl.textContent="V";
  setSyncStatus("Local saved");
  renderAll();
}

function a(){
  try {
    ensurePassword();
    loadData();
    showApp();
  } catch(e) {
    console.error(e);
    alert("Ventus could not start correctly. Please refresh the page.");
  }
}

a();
document.getElementById("previousMonthForm")?.addEventListener("submit", addPreviousMonthRecord);
