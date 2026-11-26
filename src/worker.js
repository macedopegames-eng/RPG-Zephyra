// Nexus Archives · API (Cloudflare Worker + D1). Segredos: MASTER_PASSWORD e SESSION_SECRET.
const AT=['for','des','con','int','sab','car'],enc=new TextEncoder();
const J=(o,s=200,h={})=>new Response(JSON.stringify(o),{status:s,headers:{'content-type':'application/json','cache-control':'no-store',...h}});
const hex=b=>[...new Uint8Array(b)].map(x=>x.toString(16).padStart(2,'0')).join('');
const unhex=h=>new Uint8Array(h.match(/../g).map(x=>parseInt(x,16)));
const eq=(a,b)=>{const x=enc.encode(a),y=enc.encode(b);return x.length==y.length&&crypto.subtle.timingSafeEqual(x,y)};
const pbk=async(pw,salt)=>hex(await crypto.subtle.deriveBits({name:'PBKDF2',hash:'SHA-256',salt,iterations:100000},await crypto.subtle.importKey('raw',enc.encode(pw),'PBKDF2',false,['deriveBits']),256));
const hashPw=async pw=>{const s=crypto.getRandomValues(new Uint8Array(16));return hex(s)+':'+await pbk(pw,s)};
const checkPw=async(pw,st)=>{const[s,h]=st.split(':');return eq(await pbk(pw,unhex(s)),h)};
const b64=s=>btoa(s).replace(/\+/g,'-').replace(/\//g,'_').replace(/=+$/,'');
const sign=async(env,p)=>b64(String.fromCharCode(...new Uint8Array(await crypto.subtle.sign('HMAC',await crypto.subtle.importKey('raw',enc.encode(env.SESSION_SECRET),{name:'HMAC',hash:'SHA-256'},false,['sign']),enc.encode(p)))));
const mk=async(env,role,id)=>{const p=`${role}|${id}|${Date.now()+6048e5}`;return b64(p)+'.'+await sign(env,p)};
async function who(req,env){const c=(req.headers.get('cookie')||'').match(/(?:^|; )s=([^;]+)/);if(!c)return null;
try{const[a,sg]=c[1].split('.'),p=atob(a.replace(/-/g,'+').replace(/_/g,'/'));if(!eq(await sign(env,p),sg))return null;const[role,id,exp]=p.split('|');return +exp>Date.now()?{role,id}:null}catch{return null}}
const str=(s,n)=>String(s??'').slice(0,n);
// REGRA DE 3 (Constituição -> PV, Destreza -> PE)
//   PV/PE máx. novo = PV/PE máx. atual × atributo novo ÷ atributo antigo
//   Ex.: PV máx. 20, CON 10 -> 12:  20 × 12 ÷ 10 = 24  (+4)
// ARREDONDAMENTO: ao inteiro mais próximo (0,5 sobe). Para "sempre para cima" ou "sempre para baixo",
// basta trocar Math.round por Math.ceil ou Math.floor na linha abaixo (o cliente tem a mesma constante, R3).
const ROUND=Math.round;
// devolve o GANHO (inteiro >= 0). Só há ganho quando o atributo sobe; limite de 9999 como no resto da ficha.
const regra3=(max,antes,depois)=>antes>0&&depois>antes?Math.max(0,Math.min(9999,ROUND(max*depois/antes))-max):0;
const num=(v,d=0,m=99)=>{v=Math.round(+v);return Number.isFinite(v)?Math.max(0,Math.min(m,v)):d};
const img=(s,n)=>{s=String(s??'');if(s.length>n)throw new RangeError('Imagem grande demais. Use uma menor.');return!s||/^(data:image\/|https:\/\/)/.test(s)?s:''};
function clean(b){const a=b.attrs||{},hm=num(b.hpMax,10,9999),pm=num(b.peMax,10,9999);return{name:str(b.name,80),level:str(b.level,40),cls:str(b.cls,120),quote:str(b.quote,300),img:img(b.img,500000),bio:str(b.bio,1500),lore:str(b.lore,20000),
credits:num(b.credits,0,1e9),points:num(b.points,0,999),hpMax:hm,hp:Math.min(num(b.hp,hm,9999),hm),peMax:pm,pe:Math.min(num(b.pe,pm,9999),pm),attrs:Object.fromEntries(AT.map(k=>[k,num(a[k],10)])),
powers:(b.powers||[]).slice(0,50).map(w=>({n:str(w.n,80),c:str(w.c,80),d:str(w.d,800)})),
items:(b.items||[]).slice(0,100).map(i=>({n:str(i.n,80),q:str(i.q,12),d:str(i.d,800)})),
gallery:(b.gallery||[]).slice(0,10).map(g=>img(g,120000)),avatar:img(b.avatar,150000)}}
let ready;const getDB=env=>ready??=env.DB.batch([env.DB.prepare('CREATE TABLE IF NOT EXISTS players(id TEXT PRIMARY KEY,user TEXT UNIQUE NOT NULL,pass TEXT NOT NULL,data TEXT NOT NULL)'),env.DB.prepare('CREATE TABLE IF NOT EXISTS events(name TEXT PRIMARY KEY,active INTEGER NOT NULL DEFAULT 0)'),
 env.DB.prepare('CREATE TABLE IF NOT EXISTS chat(id INTEGER PRIMARY KEY AUTOINCREMENT,who TEXT NOT NULL,name TEXT NOT NULL,role TEXT NOT NULL,text TEXT NOT NULL,ts INTEGER NOT NULL)'),
 env.DB.prepare("CREATE TABLE IF NOT EXISTS docs(id TEXT PRIMARY KEY,data TEXT NOT NULL,st TEXT NOT NULL DEFAULT 'hidden',ord INTEGER NOT NULL,upd INTEGER NOT NULL)"),env.DB.prepare('CREATE TABLE IF NOT EXISTS meta(k TEXT PRIMARY KEY,v TEXT)'),env.DB.prepare('CREATE TABLE IF NOT EXISTS rolls(id INTEGER PRIMARY KEY AUTOINCREMENT,pid TEXT,who TEXT,expr TEXT,detail TEXT,total INTEGER,ts INTEGER)')]).then(()=>env.DB);
const EV=['glitch'];
const out=r=>({id:r.id,user:r.user,hp:10,hpMax:10,pe:10,peMax:10,...JSON.parse(r.data)});
const lite=r=>{const{img,gallery,avatar,...o}=out(r);return{...o,sig:(img||'').length+(avatar||'').length+'.'+(gallery||[]).reduce((a,g)=>a+g.length,0)}};
const DS=['hidden','locked','open'];
const cleanDoc=b=>({title:str(b.title,120).trim(),kind:b.kind=='relato'?'relato':'oficial',cat:str(b.cat,60),author:str(b.author,120),date:str(b.date,60),body:str(b.body,20000),img:img(b.img,500000)});
// Jogadores só recebem o conteúdo de documentos ABERTOS; nos BLOQUEADOS só título/tipo; os OCULTOS nem aparecem.
const docOut=(r,master)=>{const d=JSON.parse(r.data),o={id:r.id,st:r.st,upd:r.upd,title:d.title,kind:d.kind,cat:d.cat};return master||r.st=='open'?{...d,...o}:o};
const mset=(D,k,v)=>D.prepare('INSERT INTO meta VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=excluded.v').bind(k,v);
export default{async fetch(req,env){const p=new URL(req.url).pathname,m=req.method;
if(!p.startsWith('/api/'))return env.ASSETS.fetch(req);
try{
if(!env.SESSION_SECRET||!env.MASTER_PASSWORD)return J({erro:'Servidor sem segredos: configure MASTER_PASSWORD e SESSION_SECRET no Cloudflare.'},500);
const D=await getDB(env);
if(p=='/api/login'&&m=='POST'){const b=await req.json(),u=str(b.user,40).trim().toLowerCase(),pw=str(b.pass,200);let s;
 if(u=='mestre'){if(!eq(pw,env.MASTER_PASSWORD))return J({erro:'Usuário ou senha inválidos.'},401);s={role:'master',id:'master'}}
 else{const r=await D.prepare('SELECT id,pass FROM players WHERE user=?').bind(u).first();if(!r||!await checkPw(pw,r.pass))return J({erro:'Usuário ou senha inválidos.'},401);s={role:'player',id:r.id}}
 return J(s,200,{'set-cookie':`s=${await mk(env,s.role,s.id)}; HttpOnly; Secure; SameSite=Strict; Path=/; Max-Age=604800`})}
if(p=='/api/logout')return J({ok:1},200,{'set-cookie':'s=; HttpOnly; Secure; SameSite=Strict; Path=/; Max-Age=0'});
const me=await who(req,env);if(!me)return J({erro:'Sessão expirada. Entre de novo.'},401);
if(p=='/api/me')return J(me);
const master=me.role=='master';
if(p=='/api/state'){const q=master?await D.prepare('SELECT * FROM players ORDER BY rowid').all():await D.prepare('SELECT * FROM players WHERE id=?').bind(me.id).all(),e=await D.prepare('SELECT name,active FROM events').all();
 const[mt,rl,cm,dq]=await Promise.all([D.prepare("SELECT k,v FROM meta WHERE k IN('stream','beat')").all(),master?D.prepare('SELECT who,expr,detail,total,ts FROM rolls ORDER BY id DESC LIMIT 30').all():D.prepare('SELECT who,expr,detail,total,ts FROM rolls WHERE pid=? ORDER BY id DESC LIMIT 10').bind(me.id).all(),D.prepare('SELECT MAX(id) m FROM chat').first(),D.prepare(master?'SELECT id,st,upd FROM docs':"SELECT id,st,upd FROM docs WHERE st!='hidden'").all()]);
 const M=Object.fromEntries(mt.results.map(x=>[x.k,x.v]));
 return J({stream:M.stream&&Date.now()-(+M.beat||0)<150000?M.stream:null,rolls:rl.results,players:q.results.map(lite),events:Object.fromEntries(e.results.map(x=>[x.name,!!x.active])),chat:cm&&cm.m||0,docs:dq.results.map(r=>r.id+r.st+r.upd).sort().join()})}
if(p=='/api/chat'){
 if(m=='GET'){const a=num(new URL(req.url).searchParams.get('after'),0,1e15),
  q=a?await D.prepare('SELECT id,who,name,role,text,ts FROM chat WHERE id>? ORDER BY id LIMIT 200').bind(a).all():await D.prepare('SELECT * FROM (SELECT id,who,name,role,text,ts FROM chat ORDER BY id DESC LIMIT 100) ORDER BY id').all();return J(q.results)}
 if(m=='POST'){const t=str((await req.json()).text,500).trim();if(!t)return J({erro:'Mensagem vazia.'},400);
  let name='Mestre';if(!master){const r=await D.prepare('SELECT data FROM players WHERE id=?').bind(me.id).first();if(!r)return J({erro:'Ficha não encontrada.'},404);name=JSON.parse(r.data).name||'Jogador'}
  const ts=Date.now(),r=await D.prepare('INSERT INTO chat(who,name,role,text,ts) VALUES(?,?,?,?,?)').bind(me.id,name,me.role,t,ts).run();
  await D.prepare('DELETE FROM chat WHERE id<=(SELECT MAX(id) FROM chat)-500').run();
  return J({id:r.meta.last_row_id,who:me.id,name,role:me.role,text:t,ts},201)}
 return J({erro:'Método não permitido.'},405)}
const dm=p.match(/^\/api\/docs(?:\/([\w-]+))?$/);
if(dm){const did=dm[1];
 if(!did&&m=='GET'){const q=await D.prepare(master?'SELECT * FROM docs ORDER BY ord DESC':"SELECT * FROM docs WHERE st!='hidden' ORDER BY ord DESC").all();return J(q.results.map(r=>docOut(r,master)))}
 if(!master)return J({erro:'Sem permissão.'},403);
 if(!did&&m=='POST'){const b=await req.json(),d=cleanDoc(b);if(!d.title)return J({erro:'Dê um título ao documento.'},400);const nid=crypto.randomUUID().slice(0,8),now=Date.now();
  await D.prepare('INSERT INTO docs(id,data,st,ord,upd) VALUES(?,?,?,?,?)').bind(nid,JSON.stringify(d),DS.includes(b.st)?b.st:'hidden',now,now).run();return J({id:nid},201)}
 if(did){if(!await D.prepare('SELECT id FROM docs WHERE id=?').bind(did).first())return J({erro:'Documento não encontrado.'},404);
  if(m=='PUT'){const d=cleanDoc(await req.json());if(!d.title)return J({erro:'Dê um título ao documento.'},400);await D.prepare('UPDATE docs SET data=?,upd=? WHERE id=?').bind(JSON.stringify(d),Date.now(),did).run();return J({ok:1})}
  if(m=='PATCH'){const b=await req.json();if(!DS.includes(b.st))return J({erro:'Estado inválido.'},400);await D.prepare('UPDATE docs SET st=?,upd=? WHERE id=?').bind(b.st,Date.now(),did).run();return J({ok:1})}
  if(m=='DELETE'){await D.prepare('DELETE FROM docs WHERE id=?').bind(did).run();return J({ok:1})}}
 return J({erro:'Método não permitido.'},405)}
if(p=='/api/roll'&&m=='POST'){const b=await req.json(),x=String(b.expr||'').replace(/\s/g,'').toLowerCase().match(/^(\d{0,2})d(\d{1,3})([+-]\d{1,4})?$/);
 if(!x)return J({erro:'Fórmula inválida. Exemplos: d20, 2d6+3.'},400);
 const n=+x[1]||1,s=+x[2],k=+(x[3]||0);if(s<2||n>20)return J({erro:'Use de 1 a 20 dados de 2 a 999 lados.'},400);
 const rs=[...crypto.getRandomValues(new Uint32Array(n))].map(v=>v%s+1),tot=rs.reduce((a,v)=>a+v,0)+k,sn=k?(k>0?'+':'')+k:'';
 let who='Mestre';if(!master){const r=await D.prepare('SELECT data FROM players WHERE id=?').bind(me.id).first();if(!r)return J({erro:'Ficha não encontrada.'},404);who=JSON.parse(r.data).name||'Jogador'}
 const ts=Date.now(),expr=`${n}d${s}${sn}`,detail=`[${rs.join(', ')}]${k?' '+sn:''}`;
 await D.batch([D.prepare('INSERT INTO rolls(pid,who,expr,detail,total,ts) VALUES(?,?,?,?,?,?)').bind(me.id,who,expr,detail,tot,ts),D.prepare('DELETE FROM rolls WHERE id<=(SELECT MAX(id) FROM rolls)-200')]);
 return J({who,expr,detail,total:tot,ts})}
if(p=='/api/stream'&&m=='PUT'){if(!master)return J({erro:'Sem permissão.'},403);const b=await req.json();
 if(b.peer)await D.batch([mset(D,'stream',str(b.peer,40)),mset(D,'beat',String(Date.now()))]);else await D.prepare("DELETE FROM meta WHERE k IN('stream','beat','frame')").run();return J({ok:1})}
if(p=='/api/stream/frame'){if(m=='PUT'){if(!master)return J({erro:'Sem permissão.'},403);const f=String((await req.json()).f||'');
  if(!f.startsWith('data:image/jpeg')||f.length>400000)return J({erro:'Quadro inválido.'},400);await D.batch([mset(D,'frame',f),mset(D,'beat',String(Date.now()))]);return J({ok:1})}
 const r=await D.prepare("SELECT v FROM meta WHERE k='frame'").first();return J({f:r?r.v:null})}
const em=p.match(/^\/api\/events\/(\w+)$/);
if(em){if(!master||m!='PUT'||!EV.includes(em[1]))return J({erro:'Sem permissão.'},403);const b=await req.json();
 await D.prepare('INSERT INTO events VALUES(?,?) ON CONFLICT(name) DO UPDATE SET active=excluded.active').bind(em[1],b.on?1:0).run();return J({ok:1})}
const mm=p.match(/^\/api\/players(?:\/([\w-]+))?$/);if(!mm)return J({erro:'Não encontrado.'},404);
const id=mm[1];
if(!id){
 if(m=='GET'){const q=master?await D.prepare('SELECT * FROM players ORDER BY rowid').all():await D.prepare('SELECT * FROM players WHERE id=?').bind(me.id).all();return J(q.results.map(out))}
 if(m=='POST'&&master){const b=await req.json(),u=str(b.user,40).trim().toLowerCase();if(!u||!b.pass||u=='mestre')return J({erro:'Usuário e senha são obrigatórios.'},400);
  const nid=crypto.randomUUID().slice(0,8);
  try{await D.prepare('INSERT INTO players VALUES(?,?,?,?)').bind(nid,u,await hashPw(str(b.pass,200)),JSON.stringify(clean(b))).run()}catch(e){if(e instanceof RangeError)throw e;return J({erro:'Esse usuário já existe.'},409)}
  return J({id:nid},201)}
}else{
 if(!master&&id!=me.id)return J({erro:'Sem permissão.'},403);
 const r=await D.prepare('SELECT * FROM players WHERE id=?').bind(id).first();if(!r)return J({erro:'Ficha não encontrada.'},404);
 if(m=='PUT'&&master){const b=await req.json(),u=str(b.user,40).trim().toLowerCase();if(!u||u=='mestre')return J({erro:'Usuário inválido.'},400);
  const data=JSON.stringify(clean(b));
  try{await D.prepare('UPDATE players SET user=?,pass=?,data=? WHERE id=?').bind(u,b.pass?await hashPw(str(b.pass,200)):r.pass,data,id).run()}catch{return J({erro:'Esse usuário já existe.'},409)}
  return J({ok:1})}
 if(m=='DELETE'&&master){await D.prepare('DELETE FROM players WHERE id=?').bind(id).run();return J({ok:1})}
 if(m=='PATCH'){const b=await req.json(),d={hp:10,hpMax:10,pe:10,peMax:10,...JSON.parse(r.data)};for(const k of['hp','pe'])if(k in b)d[k]=num(b[k],d[k],d[k+'Max']);if('avatar' in b)d.avatar=img(b.avatar,150000);
  if(b.gallery)d.gallery=clean({gallery:b.gallery}).gallery;
  if(b.spend){let pts=d.points;const a0={...d.attrs};for(const k of AT){const n=num(b.spend[k],0,999);if(n>pts)return J({erro:'Pontos insuficientes.'},400);pts-=n;d.attrs[k]=Math.min(99,d.attrs[k]+n)}d.points=pts
   // aplica a regra de 3: sobe o máximo E o valor atual no mesmo tanto (o atual nunca passa do máximo)
   for(const[at,cur,mx]of[['con','hp','hpMax'],['des','pe','peMax']]){const g=regra3(d[mx],a0[at],d.attrs[at]);if(g>0){d[mx]+=g;d[cur]=Math.min(d[mx],d[cur]+g)}}}
  const data=JSON.stringify(d);await D.prepare('UPDATE players SET data=? WHERE id=?').bind(data,id).run();return J(out({...r,data}))}
}
return J({erro:'Método não permitido.'},405)
}catch(e){return J({erro:e.message||'Erro no servidor.'},e instanceof RangeError?400:500)}}}
