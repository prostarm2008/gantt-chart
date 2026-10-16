/* Task Tracker engine (browser). Business logic ported 1:1 from the original server.js.
   Data lives in ONE raw JSON payload stored in SharePoint through a single Power Automate flow.
   Flow operations: load | save | mail (see flow/FLOW_BUILD_GUIDE.md). */
(function(root){
"use strict";
const ROLES=["employee","vp","admin","promoter"],PROJECTS=[{id:"ARKIS",name:"ARKIS"},{id:"AVASA_VEDA",name:"AVASA & VEDA"}],PIDS=PROJECTS.map(p=>p.id);
const CFG={flowUrl:"",maxAge:120000,mail:true,baseUrl:""};
let DB=null,rev=0,loadedAt=0,curUser="",lastRem=0,queue=Promise.resolve();
// ---------- crypto (WebCrypto; works in browsers and Node 19+) ----------
const enc=s=>new TextEncoder().encode(s),hex=a=>[...new Uint8Array(a)].map(x=>x.toString(16).padStart(2,"0")).join("");
const rbytes=n=>crypto.getRandomValues(new Uint8Array(n)),rhex=n=>hex(rbytes(n)),rb64u=n=>btoa(String.fromCharCode(...rbytes(n))).replace(/\+/g,"-").replace(/\//g,"_").replace(/=+$/,"");
const ITER=210000,pbk=async(p,s)=>hex(await crypto.subtle.deriveBits({name:"PBKDF2",hash:"SHA-256",salt:enc(s),iterations:ITER},await crypto.subtle.importKey("raw",enc(p),"PBKDF2",false,["deriveBits"]),256));
const hash=async p=>{const s=rhex(16);return s+":"+await pbk(p,s)};
const check=async(p,h)=>{const[s,x]=String(h).split(":"),y=await pbk(p,s||"");let d=x.length^y.length;for(let i=0;i<y.length;i++)d|=x.charCodeAt(i)^y.charCodeAt(i);return d===0};
const sha=async t=>hex(await crypto.subtle.digest("SHA-256",enc(t)));
const sign=p=>btoa(encodeURIComponent(JSON.stringify(p))),verify=t=>{try{const p=JSON.parse(decodeURIComponent(atob(String(t))));if(!(p.exp>Date.now()/1e3))throw 0;return p}catch(e){throw 0}};
// ---------- zip / xlsx helpers ----------
const crcT=(()=>{const t=[];for(let n=0;n<256;n++){let c=n;for(let i=0;i<8;i++)c=c&1?0xEDB88320^(c>>>1):c>>>1;t[n]=c>>>0}return t})(),crc32=b=>{let c=0xFFFFFFFF;for(const x of b)c=crcT[(c^x)&255]^(c>>>8);return(c^0xFFFFFFFF)>>>0};
const mk=n=>{const a=new Uint8Array(n);return[a,new DataView(a.buffer)]},cat=l=>{const o=new Uint8Array(l.reduce((s,x)=>s+x.length,0));let p=0;for(const x of l){o.set(x,p);p+=x.length}return o};
const zip=files=>{const parts=[],cd=[];let off=0;for(const[name,data]of files){const nb=enc(name),db=enc(data),crc=crc32(db),[h,hv]=mk(30),[c,cv]=mk(46);
hv.setUint32(0,0x04034b50,true);hv.setUint16(4,20,true);hv.setUint16(12,0x21,true);hv.setUint32(14,crc,true);hv.setUint32(18,db.length,true);hv.setUint32(22,db.length,true);hv.setUint16(26,nb.length,true);parts.push(h,nb,db);
cv.setUint32(0,0x02014b50,true);cv.setUint16(4,20,true);cv.setUint16(6,20,true);cv.setUint16(14,0x21,true);cv.setUint32(16,crc,true);cv.setUint32(20,db.length,true);cv.setUint32(24,db.length,true);cv.setUint16(28,nb.length,true);cv.setUint32(42,off,true);cd.push(c,nb);off+=30+nb.length+db.length}
const cdb=cat(cd),[e,ev]=mk(22);ev.setUint32(0,0x06054b50,true);ev.setUint16(8,files.length,true);ev.setUint16(10,files.length,true);ev.setUint32(12,cdb.length,true);ev.setUint32(16,off,true);return cat([...parts,cdb,e])};
// ---------- storage: ONE Power Automate flow -> SharePoint ----------
const BASE=()=>CFG.baseUrl||(typeof location!=="undefined"?location.origin+location.pathname.replace(/[^/]*$/,""):"http://localhost/");
async function flow(payload){let r,t;try{r=await fetch(CFG.flowUrl,{method:"POST",headers:{"Content-Type":"text/plain"},body:JSON.stringify(payload)});t=await r.text()}catch(e){throw Object.assign(new Error("Cannot reach the company data service (Power Automate). Check internet and the connection link."),{s:503})}
let j=null;try{j=JSON.parse(t)}catch(e){}return{status:r.status,json:j}}
async function pull(){const r=await flow({op:"load"});if(r.status!==200||!r.json||typeof r.json!=="object")throw Object.assign(new Error("Cannot read the SharePoint data file (HTTP "+r.status+"). Check the Power Automate flow."),{s:502});DB=r.json;rev=DB.rev||0;norm();loadedAt=Date.now()}
const save=async()=>{DB.rev=rev+1;const r=await flow({op:"save",baseRev:rev,user:curUser,db:DB});if(r.status===200){rev=DB.rev;loadedAt=Date.now();return}
DB.rev=rev;if(r.status===409)throw Object.assign(new Error("conflict"),{conflict:true});throw Object.assign(new Error("The data service returned an error (HTTP "+r.status+"). Please try again."),{s:502})};
function norm(){DB.users=DB.users||[];DB.audit=DB.audit||[];DB.resets=DB.resets||[];DB.tasks=DB.tasks||[];DB.seq=DB.seq||0;["notes","outbox","delegates"].forEach(k=>DB[k]=DB[k]||[]);DB.sent=DB.sent||{};DB.nseq=DB.nseq||0;DB.oseq=DB.oseq||0;DB.tasks.forEach(t=>{t.state=t.state||"open"})}
// ======================= business logic (from server.js) =======================
const E=(s,m)=>{throw Object.assign(new Error(m),{s})},find=id=>DB.users.find(u=>u.id===id);
const log=(c,user,action,detail)=>{DB.audit.push({at:new Date().toISOString(),user,action,detail:detail||"",ip:c.ip});if(DB.audit.length>50000)DB.audit.splice(0,5000)};
const pub=u=>({id:u.id,empId:u.empId,name:u.name,department:u.department,designation:u.designation,role:u.role,managerId:u.managerId,projects:u.projects,active:u.active,isManager:DB.users.some(x=>x.active&&x.managerId===u.id)});
const canSee=(u,p)=>u.role==="admin"||u.role==="vp"||u.projects.includes(p); // used by task modules in later phases
const routes=[],R=(m,p,fn,mode)=>routes.push({m,re:new RegExp("^"+p+"$"),fn,mode});
const limit=(k,n)=>{const tries=DB.tries=DB.tries||{},now=Date.now();if(Object.keys(tries).length>2000)for(const x in tries)if(!tries[x].some(t=>now-t<6e5))delete tries[x];tries[k]=(tries[k]||[]).filter(t=>now-t<6e5);if(tries[k].length>=n)E(429,"Too many attempts. Wait 10 minutes.");return()=>tries[k].push(now)};
const temp=()=>rb64u(8);
const clean=(d,self)=>{const o={name:String(d.name||"").trim().slice(0,80),empId:String(d.empId||"").trim().slice(0,30),department:String(d.department||"").trim().slice(0,60),designation:String(d.designation||"").trim().slice(0,60),role:d.role,managerId:String(d.managerId||"").trim().toLowerCase(),projects:[...new Set(d.projects||[])]};
if(!o.name)E(400,"Name is required");if(!ROLES.includes(o.role))E(400,"Invalid role");
if(o.role==="admin"||o.role==="vp")o.projects=[...PIDS];else{if(o.projects.some(p=>!PIDS.includes(p)))E(400,"Unknown project");if(o.role==="promoter"&&o.projects.length!==1)E(400,"A promoter must have exactly one project");if(!o.projects.length)E(400,"Select at least one project")}
if(o.role==="promoter"||o.role==="admin")o.managerId="";
if(o.role==="employee"&&!o.managerId)E(400,"Reporting manager is required for employees");
if(o.managerId){const m=find(o.managerId);if(!m||!m.active)E(400,"Reporting manager not found");if(m.role==="promoter")E(400,"A promoter cannot be a manager");
if(self){let x=m;for(let i=0;x&&i<50;i++){if(x.id===self)E(400,"Reporting loop is not allowed");x=find(x.managerId)}}}return o};
const create=async(c,d)=>{const id=String(d.email||"").trim().toLowerCase();if(!/^\S+@\S+\.\S+$/.test(id))E(400,"Valid email is required");if(find(id))E(409,"User already exists");
const o=clean(d),t=temp();DB.users.push({id,...o,active:true,hash:await hash(t),must:true});log(c,c.user.id,"user_create",id+" as "+o.role);return{id,temp:t}};
R("POST","/api/login",async c=>{const email=String(c.body.email||"").trim().toLowerCase(),bad=limit(c.ip+email,8),u=find(email);
if(!u||!u.active||!(await check(String(c.body.password||""),u.hash))){bad();log(c,email,"login_failed");await save();E(401,"Wrong email or password")}
if(u.must){const np=c.body.newPassword;if(!np)return{mustChange:true};if(String(np).length<8)E(400,"New password must be 8+ characters");u.hash=await hash(String(np));u.must=false;u.tv=(u.tv||0)+1;log(c,email,"password_changed")}
log(c,email,"login");await save();return{token:sign({id:email,v:u.tv||0,exp:Math.floor(Date.now()/1e3)+8*3600})}});
R("POST","/api/forgot",async c=>{const email=String(c.body.email||"").trim().toLowerCase(),bad=limit("f"+c.ip,5);bad();const u=find(email);
if(u&&u.active){const t=rhex(24);DB.resets=DB.resets.filter(r=>r.exp>Date.now()&&r.id!==email);DB.resets.push({h:await sha(t),id:email,exp:Date.now()+36e5});log(c,email,"password_reset_requested");await save();
mail(email,"Reset your Task Tracker password","Open this link within 1 hour to choose a new password:\n"+BASE()+"?reset="+t+"\n\nIf you did not ask for this, ignore this email.")}return{ok:1}});
R("POST","/api/reset",async c=>{const pw=String(c.body.password||""),th=await sha(String(c.body.token||"")),r=DB.resets.find(r=>r.h===th&&r.exp>Date.now());if(!r)E(400,"This reset link is invalid or expired");if(pw.length<8)E(400,"Password must be 8+ characters");
const u=find(r.id);u.hash=await hash(pw);u.must=false;u.tv=(u.tv||0)+1;DB.resets=DB.resets.filter(x=>x!==r);log(c,u.id,"password_reset");await save();return{ok:1}});
R("POST","/api/change-password",async c=>{const pw=String(c.body.password||"");if(!(await check(String(c.body.current||""),c.user.hash)))E(400,"Current password is wrong");if(pw.length<8)E(400,"New password must be 8+ characters");c.user.hash=await hash(pw);c.user.tv=(c.user.tv||0)+1;log(c,c.user.id,"password_changed");await save();return{ok:1,token:sign({id:c.user.id,v:c.user.tv,exp:Math.floor(Date.now()/1e3)+8*3600})}},"auth");
R("GET","/api/me",async c=>{const m=find(c.user.managerId);return{me:{...pub(c.user),managerName:m?m.name:""},projects:PROJECTS.filter(p=>canSee(c.user,p.id))}},"auth");
R("GET","/api/users",async c=>{const u=c.user;if(u.role==="admin")return{users:DB.users.map(pub),delegates:DB.delegates};
return{users:DB.users.filter(x=>x.active&&(u.role==="vp"||x.role==="admin"||x.role==="vp"||x.projects.some(p=>u.projects.includes(p)))).map(x=>{const p=pub(x);return{id:p.id,name:p.name,role:p.role,projects:p.projects,isManager:p.isManager,inTeam:chain(x.id).includes(u.id),active:true}})}},"auth");
R("POST","/api/users",async c=>{const r=await create(c,c.body);await save();return r},"admin");
R("PATCH","/api/users/([^/]+)",async c=>{const id=decodeURIComponent(c.m[1]),u=find(id);if(!u)E(404,"No such user");const d=c.body;
if(id===c.user.id&&(d.role!==u.role||d.active===false))E(400,"You cannot change your own role or deactivate yourself");
Object.assign(u,clean({...u,...d},id));if(typeof d.active==="boolean"){u.active=d.active;u.tv=(u.tv||0)+1}
if(!u.active&&DB.users.some(x=>x.active&&x.managerId===id))E(400,"Reassign this person's direct reports before deactivating");
log(c,c.user.id,"user_update",id);await save();return{ok:1}},"admin");
R("POST","/api/users/([^/]+)/reset",async c=>{const id=decodeURIComponent(c.m[1]),u=find(id);if(!u)E(404,"No such user");const t=temp();u.hash=await hash(t);u.must=true;u.tv=(u.tv||0)+1;log(c,c.user.id,"admin_password_reset",id);await save();return{temp:t}},"admin");
R("POST","/api/users/bulk",async c=>{const rows=c.body.rows;if(!Array.isArray(rows)||rows.length>500)E(400,"Upload up to 500 rows");const pm=s=>String(s||"").split(/[|;]/).map(x=>x.trim().toUpperCase().replace(/[^A-Z]/g,"")).filter(Boolean).map(x=>x.startsWith("ARKIS")?"ARKIS":x.startsWith("AVASA")?"AVASA_VEDA":x);
let pend=rows.map((r,i)=>({i:i+2,r})),created=[],errors=[];
for(let pass=0;pass<4&&pend.length;pass++){const next=[];for(const{i,r}of pend){try{const x=await create(c,{...r,email:r.email,role:String(r.role||"employee").toLowerCase(),managerId:r.managerEmail,projects:pm(r.projects)});created.push({email:x.id,temp:x.temp})}catch(e){if(pass<3&&/manager not found/.test(e.message))next.push({i,r});else errors.push({row:i,email:r.email||"",error:e.s?e.message:"Invalid row"})}}pend=next}
await save();return{created,errors}},"admin");
const ist=at=>new Date(Date.parse(at)+19800000).toISOString(),afilt=q=>DB.audit.filter(r=>(!q.user||r.user===q.user)&&(!q.action||r.action===q.action)&&(!q.from||ist(r.at).slice(0,10)>=q.from)&&(!q.to||ist(r.at).slice(0,10)<=q.to)&&(!q.q||(r.user+" "+r.action+" "+r.detail).toLowerCase().includes(String(q.q).toLowerCase())));
R("GET","/api/audit",async c=>{const a=afilt(c.q);return{rows:a.slice(-500).reverse(),total:a.length,actions:[...new Set(DB.audit.map(r=>r.action))].sort(),users:[...new Set(DB.audit.map(r=>r.user))].sort()}},"admin");
R("POST","/api/audit/export",async c=>{const rows=[["When (IST)","User","Action","Detail","IP"],...afilt(c.body.filters||{}).reverse().map(r=>[ist(r.at).replace("T"," ").slice(0,16),r.user,r.action,r.detail,r.ip])];log(c,c.user.id,"audit_export",c.body.format+" "+(rows.length-1)+" rows");await save();
if(c.body.format==="xlsx")return{__raw:xlsx(rows),type:"application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",name:"activity-log-"+today()+".xlsx"};
if(c.body.format==="csv")return{__raw:enc("\ufeff"+rows.map(r=>r.map(csvv).join(",")).join("\r\n")),type:"text/csv; charset=utf-8",name:"activity-log-"+today()+".csv"};E(400,"Unknown format")},"admin");
// ---- Phase 2: tasks ----
const PRI={High:0,Medium:1,Low:2},DRE=/^\d{4}-\d{2}-\d{2}$/,today=()=>new Date(Date.now()+19800000).toISOString().slice(0,10),now=()=>new Date().toISOString();
const chain=id=>{const r=[];let u=find(id);for(let i=0;u&&u.managerId&&i<50;i++){r.push(u.managerId);u=find(u.managerId)}return r};
const seeT=(u,t)=>!!t&&(u.role==="admin"||u.role==="vp"||t.ownerId===u.id||t.deps.includes(u.id)||chain(t.ownerId).includes(u.id)||(!!t.pending&&apprs(t).includes(u.id))||(u.role==="promoter"&&u.projects.includes(t.project)));
const ST={comp_pending:"Completion Pending Approval",ext_pending:"Extension Pending Approval",del_pending:"Delete Pending Approval",deleted:"Deleted"},ord=n=>n===1?"1st":n===2?"2nd":n===3?"3rd":n+"th";
const dstat=t=>{if(ST[t.state])return ST[t.state];if(t.state==="done")return t.result;const d=today();if(t.end<d)return"Overdue";if(t.ext>0)return"WIP - "+ord(t.ext)+" Extension";return t.start>d?"Not Started":"WIP"};
const apr=t=>{const o=find(t.ownerId);return o&&o.managerId?o.managerId:(DB.users.find(x=>x.role==="admin"&&x.active)||{}).id};
const canDecide=(u,t)=>!!t.pending&&(u.role==="admin"||(t.pending.level==="vp"?u.role==="vp":u.id===apr(t)||delegatesOf(apr(t)).includes(u.id)));
const dd=x=>{const[y,m,d]=x.split("-");return d+"-"+["Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec"][m-1]+"-"+y};
const tsum=(u,t)=>({id:t.id,project:t.project,name:t.name,ownerId:t.ownerId,owner:(find(t.ownerId)||{}).name,priority:t.priority,start:t.start,end:t.end,originalEnd:t.originalEnd,status:dstat(t),late:!["done","deleted"].includes(t.state)&&t.end<today(),state:t.state,needsMe:canDecide(u,t),pt:t.pending?t.pending.type:"",ext:t.ext,mine:t.ownerId===u.id,myReq:!!t.pending&&t.pending.by===u.id,tagged:t.deps.includes(u.id),team:t.ownerId!==u.id&&chain(t.ownerId).includes(u.id)});
const tfull=(u,t)=>({...tsum(u,t),description:t.description,remarks:t.remarks,deps:t.deps.map(i=>({id:i,name:(find(i)||{}).name})),createdAt:t.createdAt,history:t.history,comments:t.comments,canEdit:(t.ownerId===u.id||u.role==="admin")&&t.state==="open",canRequest:(t.ownerId===u.id||u.role==="admin")&&t.state==="open",canDecide:canDecide(u,t),pending:t.pending?{...t.pending,byName:(find(t.pending.by)||{}).name,approver:t.pending.level==="vp"?"Vice President":(find(apr(t))||{}).name}:null,completedOn:t.completedOn||"",approvedOn:t.approvedOn||"",delReason:t.delReason||"",canComment:u.role!=="promoter"});
const tclean=(u,d,old)=>{const o={name:String(d.name??"").trim().slice(0,150),description:String(d.description??"").slice(0,4000),remarks:String(d.remarks??"").slice(0,2000),priority:d.priority,project:old?old.project:d.project,start:d.start,end:old?old.end:d.end};
if(!o.name)E(400,"Task name is required");if(!(o.priority in PRI))E(400,"Priority must be High, Medium or Low");if(!PIDS.includes(o.project))E(400,"Choose a project");
if(!old&&!canSee(u,o.project))E(403,"You are not part of this project");
if(!DRE.test(o.start)||!DRE.test(o.end||""))E(400,"Start and end dates are required");if(o.end<o.start)E(400,"End date cannot be before start date");
if(old&&d.end&&d.end!==old.end)E(400,"End date can only be changed through an extension request");
const owner=old?old.ownerId:u.id;o.deps=[...new Set((d.deps||[]).map(String))];
for(const i of o.deps){const x=find(i);if(!x||!x.active||x.role==="promoter")E(400,"Invalid dependency: "+i);if(!canSee(x,o.project))E(400,x.name+" is not part of this project");if(i===owner)E(400,"The task owner cannot be tagged as a dependency")}return o};
const getT=c=>{const t=DB.tasks.find(x=>x.id===c.m[1]);if(!seeT(c.user,t))E(404,"Task not found");return t};
// ---- Phase 4: notifications, email, reminders, delegates ----
const mgrOf=t=>{const o=find(t.ownerId);return o&&o.managerId},delegatesOf=id=>DB.delegates.filter(x=>x.managerId===id&&x.from<=today()&&today()<=x.to).map(x=>x.delegateId);
const apprs=t=>t.pending&&t.pending.level==="vp"?DB.users.filter(u=>u.role==="vp"&&u.active).map(u=>u.id):[apr(t),...delegatesOf(apr(t))];
// channels: in-app + email. WhatsApp/SMS can be added as another function called from notify().
const mail=(to,subject,text,taskId)=>{const m={id:++DB.oseq,to,at:now(),subject,status:"queued"};DB.outbox.push(m);if(DB.outbox.length>2000)DB.outbox.splice(0,500);
if(CFG.mail&&CFG.flowUrl){flow({op:"mail",user:curUser,to,subject,body:text+(taskId?"\n\nOpen: "+BASE()+"?task="+taskId:"")+"\n\n- Task Tracker"}).then(r=>{m.status=r.status===200?"sent":"failed: HTTP "+r.status},e=>{m.status="failed: "+e.message})}else m.status="not configured"};
const notify=(recips,title,body,taskId,actor)=>{const set=new Set((recips||[]).filter(Boolean));DB.users.forEach(a=>{if(a.role==="admin"&&a.active)set.add(a.id)});set.delete(actor);
for(const id of set){const u=find(id);if(!u||!u.active)continue;DB.notes.push({id:++DB.nseq,to:id,at:now(),read:false,title,body,taskId:taskId||""});mail(id,title,body,taskId)}if(DB.notes.length>20000)DB.notes.splice(0,5000)};
const runReminders=async force=>{if(force!==true&&new Date(Date.now()+19800000).getUTCHours()<9)return 0;const d=today(),d2=new Date(Date.parse(d)+2*864e5).toISOString().slice(0,10),old=new Date(Date.parse(d)-40*864e5).toISOString().slice(0,10);let n=0;const once=k=>{if(DB.sent[k])return false;DB.sent[k]=d;n++;return true};
for(const t of DB.tasks){if(["done","deleted"].includes(t.state))continue;const nm=t.id+" "+t.name;
if(t.state==="open"||t.state==="ext_pending"){if(t.end===d2&&once("d2:"+t.id+":"+t.end))notify([t.ownerId],"Due in 2 days: "+nm,"This task is due on "+dd(t.end)+".",t.id);if(t.end===d&&once("d0:"+t.id+":"+t.end))notify([t.ownerId],"Due today: "+nm,"This task is due today ("+dd(t.end)+").",t.id)}
if(t.end<d&&t.state!=="comp_pending"&&once("od:"+t.id+":"+d))notify([mgrOf(t),...delegatesOf(mgrOf(t))],"Overdue: "+nm,((find(t.ownerId)||{}).name||"The owner")+"'s task was due on "+dd(t.end)+" and is not completed yet.",t.id)}
for(const k in DB.sent)if(DB.sent[k]<old)delete DB.sent[k];await save();return n};
R("GET","/api/notifications",async c=>{const m=DB.notes.filter(n=>n.to===c.user.id);return{notes:m.slice(-60).reverse(),unread:m.filter(n=>!n.read).length}},"auth");
R("POST","/api/notifications/read",async c=>{DB.notes.forEach(n=>{if(n.to===c.user.id&&(c.body.all||n.id===c.body.id))n.read=true});await save();return{ok:1}},"auth");
R("POST","/api/admin/run-reminders",async c=>({sent:await runReminders(true)}),"admin");
R("GET","/api/outbox",async c=>({rows:DB.outbox.slice(-60).reverse()}),"admin");
R("PUT","/api/users/([^/]+)/delegate",async c=>{const id=decodeURIComponent(c.m[1]),b=c.body;if(!find(id))E(404,"No such user");DB.delegates=DB.delegates.filter(x=>x.managerId!==id);
if(b.delegateId){const x=find(b.delegateId);if(!x||!x.active||x.id===id||x.role==="promoter")E(400,"Invalid delegate");if(!DRE.test(b.from||"")||!DRE.test(b.to||"")||b.to<b.from)E(400,"Choose valid from and to dates");DB.delegates.push({managerId:id,delegateId:b.delegateId,from:b.from,to:b.to});log(c,c.user.id,"delegate_set",id+" -> "+b.delegateId+" "+b.from+".."+b.to)}else log(c,c.user.id,"delegate_clear",id);
await save();return{ok:1}},"admin");
R("GET","/api/tasks",async c=>({tasks:DB.tasks.filter(t=>seeT(c.user,t)).map(t=>tsum(c.user,t))}),"auth");
R("GET","/api/tasks/([^/]+)",async c=>({task:tfull(c.user,getT(c))}),"auth");
R("POST","/api/tasks",async c=>{const u=c.user;if(u.role==="promoter")E(403,"Promoters have view-only access");const o=tclean(u,c.body),at=now(),id="T-"+String(++DB.seq).padStart(4,"0");
DB.tasks.push({id,...o,ownerId:u.id,originalEnd:o.end,ext:0,state:"open",createdBy:u.id,createdAt:at,history:[{at,name:u.name,txt:"Task created"+(o.deps.length?" and tagged "+o.deps.map(i=>find(i).name).join(", "):"")}],comments:[]});log(c,u.id,"task_create",id);{const T=DB.tasks[DB.tasks.length-1];notify(T.deps,"Tagged on "+id+": "+T.name,u.name+" added you as a dependency on this task.",id,u.id)}await save();return{id}},"auth");
R("PATCH","/api/tasks/([^/]+)",async c=>{const u=c.user,t=getT(c);if(t.ownerId!==u.id&&u.role!=="admin")E(403,"Only the task owner can edit this task");if(t.state!=="open")E(400,"This task can no longer be edited");const o=tclean(u,c.body,t),at=now(),ch=[];
const nm=a=>a.map(i=>(find(i)||{}).name).join(", ")||"none";
for(const k of["name","priority","start","remarks"])if(o[k]!==t[k])ch.push(({name:"Task name",priority:"Priority",start:"Start date",remarks:"Remarks"})[k]+": "+(t[k]||"empty")+" → "+(o[k]||"empty"));
if(o.description!==t.description)ch.push("Description edited");if(JSON.stringify([...o.deps].sort())!==JSON.stringify([...t.deps].sort()))ch.push("Dependencies: "+nm(t.deps)+" → "+nm(o.deps));
if(!ch.length)return{ok:1,changed:0};Object.assign(t,o);t.updatedAt=at;ch.forEach(x=>t.history.push({at,name:u.name,txt:x}));log(c,u.id,"task_edit",t.id+": "+ch.join("; "));notify([...t.deps,mgrOf(t)],"Task updated: "+t.id+" "+t.name,u.name+" updated: "+ch.join("; "),t.id,u.id);await save();return{ok:1,changed:ch.length}},"auth");
R("POST","/api/tasks/([^/]+)/comments",async c=>{const u=c.user,t=getT(c),txt=String(c.body.text||"").trim().slice(0,1000);if(u.role==="promoter")E(403,"Promoters have view-only access");if(!txt)E(400,"Write a comment first");
t.comments.push({at:now(),by:u.id,name:u.name,txt});log(c,u.id,"task_comment",t.id);notify([t.ownerId,...t.deps,mgrOf(t)],"New comment on "+t.id+" "+t.name,u.name+": "+txt,t.id,u.id);await save();return{ok:1}},"auth");
R("POST","/api/tasks/([^/]+)/action",async c=>{const u=c.user,t=getT(c),b=c.body,a=b.action,why=String(b.reason||b.remark||"").trim().slice(0,1000),d=today(),own=t.ownerId===u.id||u.role==="admin";
const H=(x,obo)=>t.history.push({at:now(),name:u.name+(obo===true?" (on behalf)":obo?" ("+obo+")":""),txt:x});
if(["complete","extend","delete"].includes(a)){if(!own)E(403,"Only the task owner can do this");if(t.state!=="open")E(400,"This task already has a pending request or is closed");
if(a==="complete"){t.state="comp_pending";t.pending={type:"completion",by:u.id,at:now(),remark:why,on:d,level:"manager"};H("Marked as completed"+(why?" - "+why:"")+" (awaiting approval)")}
if(a==="extend"){const ne=String(b.newEnd||"");if(!DRE.test(ne)||ne<=t.end)E(400,"New end date must be after the current end date ("+dd(t.end)+")");if(!why)E(400,"A reason is required");const n=t.ext+1;t.state="ext_pending";t.pending={type:"extension",by:u.id,at:now(),reason:why,newEnd:ne,n,level:n>=3?"vp":"manager"};H("Requested "+ord(n)+" extension to "+dd(ne)+" - "+why)}
if(a==="delete"){if(!why)E(400,"A reason is required");t.prev=t.state;t.state="del_pending";t.pending={type:"delete",by:u.id,at:now(),reason:why,level:"manager"};H("Requested deletion - "+why)}
log(c,u.id,"task_"+a+"_request",t.id);{const q=t.pending,lb={completion:"Completion",extension:"Extension",delete:"Deletion"}[q.type];notify([...apprs(t),...(q.level==="vp"?[mgrOf(t)]:[])],lb+" approval needed: "+t.id+" "+t.name,u.name+" requested "+lb.toLowerCase()+(q.newEnd?" (new end date "+dd(q.newEnd)+")":"")+(q.reason||q.remark?" - "+(q.reason||q.remark):"")+(q.level==="vp"?" [3rd extension or later: Vice President approval]":""),t.id,u.id)}await save();return{ok:1}}
if(a==="approve"||a==="reject"){const p=t.pending;if(!p)E(400,"Nothing is waiting for approval");if(!canDecide(u,t))E(403,"You are not the approver for this request");if(a==="reject"&&!why)E(400,"A reason is required to reject");
const obo=u.role==="admin"&&(p.level==="vp"||u.id!==apr(t))?true:(p.level!=="vp"&&u.id!==apr(t)&&u.role!=="admin"?"delegate":false),yes=a==="approve",tail=why?" - "+why:"";t.pending=null;
if(p.type==="completion"){if(yes){t.result=p.on<t.end?"Pre-Achieved":p.on===t.end?"Completed":"Completed (Delayed)";t.state="done";t.completedOn=p.on;t.approvedOn=d;H("Completion approved: "+t.result+" (completed on "+dd(p.on)+", due "+dd(t.end)+")"+tail,obo)}else{t.state="open";H("Completion rejected"+tail,obo)}}
if(p.type==="extension"){t.state="open";if(yes){t.end=p.newEnd;t.ext=p.n;(t.extAt=t.extAt||[]).push(now());H(ord(p.n)+" extension approved: new end date "+dd(p.newEnd)+tail,obo)}else H(ord(p.n)+" extension rejected"+tail,obo)}
if(p.type==="delete"){if(yes){t.state="deleted";t.deletedAt=now();t.deletedBy=u.id;t.delReason=p.reason;H("Deletion approved"+tail,obo)}else{t.state=t.prev||"open";H("Deletion rejected"+tail,obo)}}
{const lb={completion:"Completion",extension:"Extension",delete:"Deletion"}[p.type];notify([p.by,...(p.level==="vp"?[mgrOf(t)]:[])],lb+" "+(yes?"approved":"rejected")+": "+t.id+" "+t.name,u.name+(obo===true?" (Admin, on behalf)":"")+" "+(yes?"approved":"rejected")+" the "+p.type+" request."+tail,t.id,u.id)}log(c,u.id,"task_"+p.type+"_"+a,t.id+(obo?" (on behalf)":""));await save();return{ok:1}}
E(400,"Unknown action")},"auth");
// ---- Phase 5: dashboards, exports ----
const csvv=v=>{v=String(v);if(/^[=+\-@\t\r]/.test(v))v="'"+v;return'"'+v.replace(/"/g,'""')+'"'}; // blocks spreadsheet formula injection
const late=t=>!["done","deleted"].includes(t.state)&&t.end<today();
const dscope=(u,t)=>u.role==="admin"||u.role==="vp"||u.role==="promoter"||t.ownerId===u.id||chain(t.ownerId).includes(u.id); // dashboards: own + team only, never tasks you were merely tagged on
const fq=(u,q)=>DB.tasks.filter(t=>seeT(u,t)&&dscope(u,t)&&(!q.project||t.project===q.project)&&(!q.employee||t.ownerId===q.employee)&&(!q.manager||chain(t.ownerId).includes(q.manager))&&(!q.priority||t.priority===q.priority)&&(!q.status||dstat(t)===q.status)&&(!q.from||t.end>=q.from)&&(!q.to||t.end<=q.to));
R("GET","/api/dashboard",async c=>{const all=fq(c.user,c.q),ts=all.filter(t=>t.state!=="deleted"),cnt=f=>ts.filter(f).length,by=f=>{const m={};ts.forEach(t=>{const k=f(t);m[k]=(m[k]||0)+1});return m};
const pp={};ts.forEach(t=>{const o=pp[t.ownerId]=pp[t.ownerId]||{name:(find(t.ownerId)||{}).name||t.ownerId,total:0,done:0,onTime:0,delayed:0,overdue:0};o.total++;if(t.state==="done"){o.done++;t.result==="Completed (Delayed)"?o.delayed++:o.onTime++}if(late(t))o.overdue++});
const mon={};ts.forEach(t=>(t.extAt||[]).forEach(a=>{const k=a.slice(0,7);mon[k]=(mon[k]||0)+1}));
const k={total:ts.length,wip:cnt(t=>dstat(t).startsWith("WIP")),overdue:cnt(late),ext1:cnt(t=>t.ext===1),ext2:cnt(t=>t.ext===2),ext3:cnt(t=>t.ext>=3),pre:cnt(t=>t.state==="done"&&t.result==="Pre-Achieved"),completed:cnt(t=>t.state==="done"&&t.result==="Completed"),delayed:cnt(t=>t.state==="done"&&t.result==="Completed (Delayed)"),pending:cnt(t=>/_pending$/.test(t.state)),deleted:all.length-ts.length};
return{kpi:k,status:by(dstat),priority:by(t=>t.priority),onTime:{"On time":k.pre+k.completed,"Delayed":k.delayed},people:Object.values(pp).sort((a,b)=>b.total-a.total),extTrend:Object.keys(mon).sort().slice(-6).map(m=>({l:m,v:mon[m]})),ids:ts.map(t=>t.id)}},"auth");
const xe=v=>String(v).replace(/[\x00-\x08\x0b\x0c\x0e-\x1f]/g,"").replace(/[&<>"]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c])),X='<?xml version="1.0" encoding="UTF-8" standalone="yes"?>',NS='xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main"',RT="http://schemas.openxmlformats.org/officeDocument/2006/relationships",RS='xmlns="http://schemas.openxmlformats.org/package/2006/relationships"';
const xlsx=rows=>zip([["[Content_Types].xml",X+'<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/><Default Extension="xml" ContentType="application/xml"/><Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/><Override PartName="/xl/worksheets/sheet1.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/><Override PartName="/xl/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"/></Types>'],
["_rels/.rels",X+`<Relationships ${RS}><Relationship Id="rId1" Type="${RT}/officeDocument" Target="xl/workbook.xml"/></Relationships>`],
["xl/workbook.xml",X+`<workbook ${NS} xmlns:r="${RT}"><sheets><sheet name="Tasks" sheetId="1" r:id="rId1"/></sheets></workbook>`],
["xl/_rels/workbook.xml.rels",X+`<Relationships ${RS}><Relationship Id="rId1" Type="${RT}/worksheet" Target="worksheets/sheet1.xml"/><Relationship Id="rId2" Type="${RT}/styles" Target="styles.xml"/></Relationships>`],
["xl/styles.xml",X+`<styleSheet ${NS}><fonts count="2"><font><sz val="11"/><name val="Calibri"/></font><font><b/><sz val="11"/><name val="Calibri"/></font></fonts><fills count="2"><fill><patternFill patternType="none"/></fill><fill><patternFill patternType="gray125"/></fill></fills><borders count="1"><border/></borders><cellStyleXfs count="1"><xf/></cellStyleXfs><cellXfs count="2"><xf/><xf fontId="1" applyFont="1"/></cellXfs><cellStyles count="1"><cellStyle name="Normal" xfId="0" builtinId="0"/></cellStyles></styleSheet>`],
["xl/worksheets/sheet1.xml",X+`<worksheet ${NS}><sheetViews><sheetView workbookViewId="0"><pane ySplit="1" topLeftCell="A2" activePane="bottomLeft" state="frozen"/></sheetView></sheetViews><cols>${rows[0].map((_,i)=>`<col min="${i+1}" max="${i+1}" width="${i===2||i===12||i===13?36:16}" customWidth="1"/>`).join("")}</cols><sheetData>${rows.map((r,y)=>`<row r="${y+1}">${r.map((v,x)=>`<c r="${String.fromCharCode(65+x)}${y+1}" t="inlineStr"${y?"":' s="1"'}><is><t>${xe(v)}</t></is></c>`).join("")}</row>`).join("")}</sheetData></worksheet>`]]);
const pdf=(title,rows)=>{const L=v=>String(v).replace(/[^\x20-\x7e]/g,"?").replace(/([\\()])/g,"\\$1"),cx=[30,82,250,325,425,475,535,600,745],cw=[8,38,14,22,8,11,11,34,3],pick=r=>[r[0],r[2],r[1],r[3],r[5],r[6],r[7],r[9],r[10]];
const body=rows.slice(1),per=30,pages=[];for(let i=0;i<Math.max(1,body.length);i+=per)pages.push(body.slice(i,i+per));
const objs=["<< /Type /Catalog /Pages 2 0 R >>","","<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>","<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica-Bold >>"],kids=[];
pages.forEach((p,n)=>{const ln=(r,y,f)=>pick(r).map((v,i)=>`BT /${f} 8 Tf ${cx[i]} ${y} Td (${L(String(v).slice(0,cw[i]))}) Tj ET`).join("\n");
let c=`BT /F2 12 Tf 30 560 Td (${L(title)}) Tj ET\nBT /F1 8 Tf 700 560 Td (Page ${n+1} of ${pages.length}) Tj ET\n${ln(rows[0],535,"F2")}\n`;p.forEach((r,i)=>{c+=ln(r,518-i*16,"F1")+"\n"});
objs.push(`<< /Type /Page /Parent 2 0 R /MediaBox [0 0 842 595] /Resources << /Font << /F1 3 0 R /F2 4 0 R >> >> /Contents ${6+n*2} 0 R >>`,`<< /Length ${c.length} >>\nstream\n${c}endstream`);kids.push(`${5+n*2} 0 R`)});
objs[1]=`<< /Type /Pages /Kids [${kids.join(" ")}] /Count ${pages.length} >>`;let out="%PDF-1.4\n";const off=[];objs.forEach((o,i)=>{off.push(out.length);out+=`${i+1} 0 obj\n${o}\nendobj\n`});const xr=out.length;
out+=`xref\n0 ${objs.length+1}\n0000000000 65535 f \n`+off.map(o=>String(o).padStart(10,"0")+" 00000 n \n").join("")+`trailer\n<< /Size ${objs.length+1} /Root 1 0 R >>\nstartxref\n${xr}\n%%EOF`;return Uint8Array.from(out,ch=>ch.charCodeAt(0)&255)};
const xrows=(u,ids)=>[["Task ID","Project","Task","Owner","Reporting manager","Priority","Start date","End date","Original end date","Status","Extensions","Completed on","Dependencies","Remarks"],...ids.map(i=>DB.tasks.find(t=>t.id===i)).filter(t=>seeT(u,t)).map(t=>{const o=find(t.ownerId)||{},m=find(o.managerId)||{};return[t.id,PROJECTS.find(p=>p.id===t.project).name,t.name,o.name||"",m.name||"",t.priority,dd(t.start),dd(t.end),dd(t.originalEnd),dstat(t),t.ext,t.completedOn?dd(t.completedOn):"",t.deps.map(i=>(find(i)||{}).name).join(", "),t.remarks||""]})];
R("POST","/api/export",async c=>{const f=c.body.format,rows=xrows(c.user,(Array.isArray(c.body.ids)?c.body.ids:[]).slice(0,5000).map(String)),st=today();log(c,c.user.id,"export",f+" "+(rows.length-1)+" tasks");await save();
if(f==="xlsx")return{__raw:xlsx(rows),type:"application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",name:"tasks-"+st+".xlsx"};
if(f==="pdf")return{__raw:pdf("Task report - "+dd(st),rows),type:"application/pdf",name:"tasks-"+st+".pdf"};
if(f==="csv")return{__raw:enc("\ufeff"+rows.map(r=>r.map(csvv).join(",")).join("\r\n")),type:"text/csv; charset=utf-8",name:"tasks-"+st+".csv"};E(400,"Unknown format")},"auth");
// ---- first-run setup (replaces the old default admin password) ----
R("GET","/api/status",async c=>({setup:DB.users.length===0}));
R("POST","/api/setup",async c=>{if(DB.users.length)E(400,"Already set up");const email=String(c.body.email||"").trim().toLowerCase(),pw=String(c.body.password||""),name=String(c.body.name||"").trim().slice(0,80)||"Main Admin";
if(!/^\S+@\S+\.\S+$/.test(email))E(400,"Valid email is required");if(pw.length<8)E(400,"Password must be 8+ characters");
DB.users.push({id:email,empId:"ADMIN",name,department:"",designation:"Administrator",role:"admin",managerId:"",projects:[...PIDS],active:true,hash:await hash(pw),must:false});log(c,email,"setup","Main Admin created");await save();return{ok:1}});
// ---- dispatcher: one request at a time, reload + retry on save conflict ----
async function run(method,url,body,token){try{const U=new URL(url,"http://x"),p=U.pathname,r=routes.find(r=>r.m===method&&r.re.test(p));if(!r)E(404,"Not found");
for(let attempt=0;;attempt++){try{if(!DB||attempt>0||Date.now()-loadedAt>CFG.maxAge)await pull();
const c={ip:"web",m:p.match(r.re),q:Object.fromEntries(U.searchParams),body:body||{}};curUser="";
if(r.mode){try{const tk=verify(token),u=find(tk.id);if(!u||!u.active||(u.tv||0)!==(tk.v||0))throw 0;c.user=u;curUser=u.id}catch(e){E(401,"Please sign in")}if(r.mode==="admin"&&c.user.role!=="admin")E(403,"Admin only")}
if(c.user&&Date.now()-lastRem>6e5){lastRem=Date.now();await runReminders()}
return[200,await r.fn(c)]}catch(e){if(e&&e.conflict&&attempt<3)continue;throw e}}}
catch(e){if(method!=="GET")loadedAt=0;return[e.s||(e&&e.conflict?409:400),{error:e.s?e.message:(e&&e.conflict?"Someone saved at the same moment. Please try again.":"Bad request")}]}}
const call=(m,u,b,t)=>(queue=queue.then(()=>run(m,u,b,t)));
const TT={call,config:o=>Object.assign(CFG,o),invalidate:()=>{loadedAt=0},reset:()=>{DB=null;rev=0;loadedAt=0;lastRem=0},
async api(m,u,b,t){const[s,j]=await call(m,"/api/"+u,b,t);if(s!==200)throw Object.assign(new Error(j.error||"Error"),{status:s});return j},
async raw(u,b,t){const[s,j]=await call("POST","/api/"+u,b,t);if(s!==200)throw Object.assign(new Error(j.error||"Export failed"),{status:s});return new Blob([j.__raw],{type:j.type})}};
if(typeof module!=="undefined"&&module.exports)module.exports=TT;else root.TT=TT;
})(typeof window!=="undefined"?window:globalThis);
