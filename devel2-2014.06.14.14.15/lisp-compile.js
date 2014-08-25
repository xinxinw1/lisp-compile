/***** Lisp to JS Compiler Devel *****/

/* require tools >= 3.1 */
/* require lisp-tools */
/* require lisp-parse */ // cmps uses this
/* require lisp-exec */

(function (win, udf){
  ////// Import //////
  
  var rp = L.rp;
  
  var nilp = L.nilp;
  var lisp = L.lisp;
  var atmp = L.atmp;
  var nump = L.nump;
  var symp = L.symp;
  var objp = L.objp;
  var rgxp = L.rgxp;
  var udfp = L.udfp;
  var strp = L.strp;
  var arrp = L.arrp;
  
  var iso = L.iso;
  var inp = L.inp;
  
  var dsj = L.dsj;
  
  var dyn = $.dyn;
  
  var al = L.al;
  
  var las = L.las;
  
  var map = L.map;
  var rem = L.rem;
  var reme = L.reme;
  var rpl = L.rpl;
  
  var len = L.len;
  
  var sli = L.sli;
  
  var joi = L.joi;
  var app = L.app;
  
  var beg = L.beg;
  
  var car = L.car;
  var cdr = L.cdr;
  var cons = L.cons;
  
  var caar = L.caar;
  var cadr = L.cadr;
  var cdar = L.cdar;
  var cddr = L.cddr;
  
  var lis = L.lis;
  var nth = L.nth;
  var ncdr = L.ncdr;
  var nrev = L.nrev;
  
  var prs = L.prs;
  var evl = L.evl;
  var apl = L.apl;
  
  var jn = L.jn;
  var bol = L.bol;
  
  var do1 = $.do1;
  var err = L.err;
  
  ////// Processing //////
  
  function jvarp(a){
    return $.strp(a) && $.has(/^[a-zA-Z$_][a-zA-Z0-9$_]*$/, a);
  }
  
  function varp(a){
    return $.strp(a) && $.has(/^[a-zA-Z$_][a-zA-Z0-9$_?-]*$/, a);
  }
  
  function jvar(a){
    if (jvarp(a))return a;
    if (varp(a)){
      var s = "";
      for (var i = 0; i < $.len(a); i++){
        if (a[i] == "-"){
          if (i+1 == $.len(a))break;
          s += $.upp(a[i+1]);
          i++;
        } else if (a[i] == "?"){
          s += "p";
        } else {
          s += a[i];
        }
      }
      return s;
    }
    err(jvar, "Can't coerce a = $1 to jvar", a);
  }
  
  function onep(a){
    return udfp(a.b) || !a.b;
  }
  
  function exip(a){
    return !udfp(a.r) && a.r;
  }
  
  function brkp(a){
    return exip(a) || !udfp(a.k) && a.k;
  }
  
  // precedence
  var prec = [
    ["bot", "forbeg"],
    "doln", "dolnend",
    "setab",
    "iflnyes",
    "inln",
    "set", "setend",
    ["iflntest", "iflnno"],
    "ifln",
    "or",
    "and",
    "is", "isend",
    "cpar", "cparend",
    "add",
    "sub", "subend",
    "mul",
    "div", "divend",
    "mod", "modend",
    ["unaitm", "addunaitm", "subunaitm"],
    ["una", "adduna", "subuna"],
    ["inc", "dec"],
    ["incitm", "decitm"],
    ["fn", "obj"],
    "refee",
    // fn less than refee cause this doesn't work in global: function (){}()
    "atm"
  ];
  
  function haspri(a, b){
    if ($.beg(a, "inc", "addun") && $.beg(b, "inc", "addun"))return false;
    if ($.beg(a, "dec", "subun") && $.beg(b, "dec", "subun"))return false;
    return pri(a) >= pri(b);
  }
  
  function pri(a){
    var n = posm(a, prec);
    if (n == -1)err(pri, "Can't get pri of a = $1", a);
    return n;
  }
  
  function posm(x, a){
    for (var i = 0; i < $.len(a); i++){
      if ($.arrp(a[i])){
        if ($.has(x, a[i]))return i;
      } else {
        if (x === a[i])return i;
      }
    }
    return -1;
  }
  
  var blks = [
    "do", "dolas",
    "lop", "loplas",
    "fnc", "fnclas",
    "if",
    "swt", "swtlas",
    "cas",
    "try", "catch", "fin",
    "ret", "thr", "nrt"
  ];
  function isblk(a){
    if (nilp(a))return true;
    return $.has(a, blks);
  }
  
  var rets = ["fnclas", "ret"];
  var ends = ["dolas", "fnclas", "if", "swtlas", "cas", "try", "catch"];
  function isret(a){
    if ($.has(a, rets))return true;
    if (!$.has(a, ends))return false;
    return rtp;
  }
  
  function isthr(a){
    if (a === "thr")return true;
    if (!$.has(a, ends))return false;
    return thp;
  }
  
  function blkp(){
    return blk;
  }
  
  function retp(){
    return ret;
  }
  
  function thrp(){
    return thr;
  }
  
  // associative http://en.wikipedia.org/wiki/Associative_property
  var asc = ["or", "and", "add", "mul"];
  function ascp(a){
    return $.has(a, asc);
  }
  
  // left-associative
  var ltr = [
    "doln",
    "is",
    "cpar",
    "sub",
    "div", "mod"
  ];
  function ltrp(a){
    return $.has(a, ltr);
  }
  
  // right-associative
  var rtl = ["set"];
  function rtlp(a){
    return $.has(a, rtl);
  }
  
  function jjoi(a, x){
    return rp(joi(a, x));
  }
  
  function chkpar(a){
    if (nilp(a))return ";\n";
    if (onep(a))return a.t;
    return "{\n" + a.t + "}\n";
  }
  
  ////// Lisp compiler //////
  
  var rts, rt, blk, rtp, thp;
  function cmp(a, ret){
    if (udfp(ret)){
      rts = [];
      rt = [];
      blk = true;
      rtp = false;
      thp = false;
      return cmp1(a).t;
    }
    $.L.psh(ret, rts);
    var lrt = rt; rt = ret;
    var lblk = blk; blk = isblk(rt);
    var lrtp = rtp; rtp = isret(rt);
    var lthp = thp; thp = isthr(rt);
    var r = cmp1(a);
    rtp = lrtp;
    blk = lblk;
    rt = lrt;
    thp = lthp;
    $.L.pop(rts);
    return r;
  }
  
  function cmp1(a){
    if (atmp(a)){
      if (nilp(a))return chkrt("[]", "atm");
      if (nump(a))return chkrt(a, "atm");
      if (symp(a)){
        if (smacp(a))return cmp1(smget(a));
        //if (a == "nil")return cmp1([]);
        return chkrt(jvar(a), "atm");
      }
      if (strp(a))return chkrt($.dsp(rp(a)), "atm");
      if (rgxp(a))return chkrt($.str(a), "atm");
      return cmp1([]);
    }
    var o = car(a);
    if (strp(o) || nump(o) || rgxp(o)){
      // idref == index ref
      return chkrt(cmp(o, "refee") + "[" + cmp(cadr(a), "bot") + "]", "atm");
    }
    if (symp(o))return cprc(o, cdr(a));
    if (lisp(o)){
      if (car(o) == "dtfn")return cdtfn(cdr(o), cdr(a));
      var exp = cmcx1(o);
      if (!iso(o, exp))return cmp1(cons(exp, cdr(a)));
      //if (car(o) == "qt")return ccal(cadr(o), cdr(a));
    }
    return ccal(o, cdr(a));
  }
  
  function cprc(o, a){
    if (macp(o))return cmp1(apl(mget(o), a));
    if (beg(o, "js-")){
      switch (sli(o, 3)){
        case "+": return cubin(a, "+", "add");
        case "-": return cubin(a, "-", "sub");
        case "*": return cbin(a, "*", "mul");
        case "/": return cbin(a, "/", "div");
        case "%": return cbin(a, " % ", "mod");
        case "++": return cuna(a, "++", "inc");
        case "--": return cuna(a, "--", "dec");
        case "and": return cbin(a, " && ", "and");
        case "or": return cbin(a, " || ", "or");
        case "not": return cuna(a, "!", "una");
        case "del": return cuna(a, "delete ", "una");
        case "=": return cbin(a, " = ", "set");
        case "+=": return cbin(a, " += ", "set");
        case "-=": return cbin(a, " -= ", "set");
        case "*=": return cbin(a, " *= ", "set");
        case "/=": return cbin(a, " /= ", "set");
        case "%=": return cbin(a, " %= ", "set");
        case "<": return cbin(a, " < ", "cpar");
        case ">": return cbin(a, " > ", "cpar");
        case ">=": return cbin(a, " >= ", "cpar");
        case "<=": return cbin(a, " <= ", "cpar");
        case "inst": return cbin(a, " instanceof ", "cpar");
        case "is": return cbin(a, " === ", "is");
        case "isn": return cbin(a, " !== ", "is");
        case "arr": return carr(a);
        case "obj": return cobj(a);
        case ".": return cmths(a);
        case "#": return cref(a);
        case "cal": return ccal(car(a), cdr(a));
        case "var": return cvar(a);
        case "fn": return cfn(a);
        case "rfn": return crfn(a);
        case "def": return cdef(a);
        case "new": return cnew(a);
        case "if": return cif(a);
        case "do": return cdo(a);
        case "loop": return clop(a);
        case "while": return cwhi(a);
        case "foi": return cfoi(a);
        case "swit": return cswt(a);
        case "case": return ccas(a);
        case "brk": return cbrk(a);
        case "cont": return ccont(a);
        case "ret": return cret(a);
        case "thr": return cthr(a);
        case "nret": return cnrt(a);
        case "try": return ctry(a);
        case "mac": return cmac(a);
        case "dmac": return cdmac(a);
        case "rmac": return crmac(a);
        case "mblk": return cmblk(a);
        case "smac": return csmac(a);
        case "dsmac": return cdsmac(a);
        case "rsmac": return crsmac(a);
        case "smblk": return csmblk(a);
        case "exe": return cexe(a);
        case "qt": return cqt(car(a));
        default: err(cprc, "Unknown o = $1", o);
      }
    }
    return ccal(o, a);
  }
  
  function ccal(o, a){
    return chkrt(cmp(o, "refee") + mpar(a), "atm");
  }
  
  //// Compile all ////
  
  function cpa(a, ret){
    return map(function (x){
      return cmp(x, ret);
    }, a);
  }
  
  function cpalas(a, ret){
    if (nilp(a))return [];
    if (atmp(a))err(cpalas, "Can't cmp improper list a = $1", a);
    if (nilp(cdr(a)))return lis(cmp(car(a), ret+"las"));
    return cons(cmp(car(a), ret), cpalas(cdr(a), ret));
  }
  
  function cpaltr(a, ret){
    if (nilp(a))return [];
    if (atmp(a))err(cpaltr, "Can't cmp improper list a = $1", a);
    if (nilp(cdr(a)))return lis(cmp(car(a), ret+"end"));
    return cons(cmp(car(a), ret), cpaltr(cdr(a), ret));
  }
  
  function cpartl(a, ret){
    if (nilp(a))return [];
    return cons(cmp(car(a), ret+"end"), cpa(cdr(a), ret));
  }
  
  //// Blocks ////
  
  function mblk(a, ret, l){
    if (udfp(l))l = [];
    if (nilp(a))return [];
    if (atmp(a))err(mblk, "Can't cmp improper list a = $1", a);
    if (nilp(cdr(a))){
      var c = cmp(car(a), ret+"las");
      if (nilp(l))return c;
      return {t: jjoi(ts(nrev(cons(c, l)))), r: c.r, k: c.k, b: true};
    }
    var c = cmp(car(a), ret);
    return mblk(cdr(a), ret, cons(c, l));
  }
  
  function ts(a){
    return map(function (x){
      return x.t;
    }, a);
  }
  
  function mpar(a){
    return "(" + jjoi(cpa(a, "inln"), ", ") + ")";
  }
  
  //// Return ////
  
  function chkrt(a, cr){
    if (blk){
      if (thp)return {t: "throw " + a + ";\n", r: true};
      if (rtp)return {t: "return " + a + ";\n", r: true};
      return {t: blkbrc(a, cr) + ";\n"};
    }
    return brc(a, cr);
  }
  
  function blkbrc(a, cr){
    if (inp(cr, "fn", "rfn", "obj"))return "(" + a + ")";
    return a;
  }
  
  function brc(a, cr){
    if (jvarp(a))return a;
    if (!haspri(cr, rt))return "(" + a + ")";
    return a;
  }
  
  //// Procedures ////
  
  function cubin(a, o, n){
    if (nilp(cdr(a)))return cuna(a, o, n+"una");
    return cbin(a, o, n);
  }
  
  function cuna(a, o, n){
    return chkrt(o + cmp(car(a), n+"itm"), n);
  }
  
  function cbin(a, o, n){
    if (nilp(a))err(cbin, "Can't cmp binary o = $1, n = $2 with no args", o, n);
    if (nilp(cdr(a)))return cmp(car(a), rt);
    var f;
    if (ascp(n))f = cpa;
    else if (ltrp(n))f = cpaltr;
    else if (rtlp(n))f = cpartl;
    else err(cbin, "What? a = $1 | o = $2 | n = $3", a, o, n);
    return chkrt(jjoi(f(a, n), o), n);
  }
  
  function carr(a){
    return chkrt("[" + jjoi(cpa(a, "inln"), ", ") + "]", "atm");
  }
  
  function cobj(a){
    return chkrt("{" + cobj2(a) + "}", "obj");
  }
  
  function cobj2(a){
    if (nilp(a))return "";
    return cprop(car(a)) + ": " + cmp(cadr(a), "inln")
           + cobj3(cddr(a));
  }
  
  function cobj3(a){
    if (nilp(a))return "";
    return ", " + cprop(car(a)) + ": " + cmp(cadr(a), "inln")
           + cobj3(cddr(a));
  }
  
  function cprop(a){
    if (symp(a) || nump(a)){
      if (!varp(a))return $.dsp(a);
      return jvar(a);
    }
    if (strp(a))return cprop(rp(a));
    err(cprop, "Invalid obj property name a = $1", a);
  }
  
  function clis(a){
    return chkrt(clis2(a), "atm");
  }
  
  function clis2(a){
    if (atmp(a))return cmp(a, "inln");
    return "[" + cmp(car(a), "inln") + ", " + clis2(cdr(a)) + "]";
  }
  
  function cdtfn(o, a){
    /*
    orig a = ((dtfn a b c) x 1 2 3)
    o = (a b c)
    a = (x 1 2 3)
    (cmp `((. ,(car a) ,@o) ,@(cdr a)))
    */
    return cmp1(cons(app(lis(".", car(a)), o), cdr(a)));
  }
  
  /*function cmths(a){
    return chkrt(cmp(car(a), "refee") + "."
                 + jjoi(cpa(cdr(a), "inln"), "."), "atm");
  }*/
  function cmths(a){
    return chkrt(cmp(car(a), "refee") + "." 
                 + jjoi(map(cprop, cdr(a)), "."), "atm");
  }
  
  function cref(a){
    return chkrt(cmp(car(a), "refee")
                 + "[" + jjoi(cpa(cdr(a), "bot"), "][") + "]", "atm");
  }
  
  function cvar(a){
    if (rt == "forbeg")return cvar2(a);
    if (!blk)err(cvar, "var a = $1 must be in block", a);
    return {t: cvar2(a) + ";\n"};
  }
  
  function cvar2(a){
    if (nilp(a))return cmp1([]);
    return "var " + cmp(car(a), "setab") + " = "
           + cmp(cadr(a), "set") + cvar3(cddr(a));
  }
  
  function cvar3(a){
    if (nilp(a))return "";
    return ", " + cmp(car(a), "setab") + " = "
           + cmp(cadr(a), "set") + cvar3(cddr(a));
  }
  
  function cfn(a){
    var s = "function " + mpar(car(a)) + "{";
    var bd = mblk(cdr(a), "fnc");
    if (nilp(bd))return chkrt(s + "}", "fn");
    return chkrt(s + "\n" + bd.t + "}", "fn");
  }
  
  function crfn(a){
    if (!lisp(cadr(a)))err(crfn, "cadr(a) = $1 must be a list", cadr(a));
    var s = "function " + jvar(car(a)) + mpar(cadr(a)) + "{";
    var bd = mblk(cddr(a), "fnc");
    if (nilp(bd))return chkrt(s + "}", "fn");
    return chkrt(s + "\n" + bd.t + "}", "fn");
  }
  
  function cdef(a){
    if (!blk)err(cdef, "def a = $1 must be in block", a);
    if (!lisp(cadr(a)))err(cdef, "cadr(a) = $1 must be a list", cadr(a));
    var s = "function " + jvar(car(a)) + mpar(cadr(a)) + "{";
    var bd = mblk(cddr(a), "fnc");
    if (nilp(bd))return {t: s + "}\n", b: true};
    return {t: s + "\n" + bd.t + "}\n", b: true};
  }
  
  function cnew(a){
    return chkrt("new " + cmp(car(a), "refee") + mpar(cdr(a)), "atm");
  }
  
  function cif(a){
    if (!blk)return cifln(a);
    return cifbl(a);
  }
  
  /*
  (ret (if a b c d e)) -> {t: "if (a)return b;\nif (c)return d;\nreturn e;\n", r: true, b: true}
  (ret (if a b c)) -> {t: "if (a)return b;\nreturn c;\n", r: true, b: true}
  (if a b c) -> {t: "if (a)b;\nelse c;\n", r: false, b: true}
  (if) -> {t: "", r: false, b: false
  */
  
  function cifbl(a){
    if (nilp(a))return cmp([], "if");
    if (nilp(cdr(a)))return cmp(car(a), "if");
    var ifpt = cmp(car(a), "bot");
    var yes = cmp(cadr(a), "if");
    var s = "if (" + ifpt + ")";
    if (nilp(yes))return {t: s + ";\n" + celifbl(cddr(a)), b: true};
    if (onep(yes)){
      s += yes.t;
      if (brkp(yes)){
        var n = cifbl(cddr(a));
        if (nilp(n))return {t: s, b: true};
        return {t: s + n.t, r: n.r, b: true};
      }
      return {t: s + celifbl(cddr(a)), b: true};
    }
    s += "{\n" + yes.t + "}";
    if (brkp(yes)){
      s += "\n";
      var n = cifbl(cddr(a));
      if (nilp(n))return {t: s, b: true};
      return {t: s + n.t, r: n.r, b: true};
    }
    if (nilp(cddr(a)))return {t: s + "\n", b: true};
    return {t: s + " " + celifbl(cddr(a)), b: true};
  }
  
  function celifbl(a){
    if (nilp(a))return "";
    if (nilp(cdr(a)))return "else " + chkpar(cmp(car(a), "if"));
    var ifpt = cmp(car(a), "bot");
    var yes = cmp(cadr(a), "if");
    var s = "else if (" + ifpt + ")";
    if (nilp(yes))return s + ";\n" + celifbl(cddr(a));
    if (onep(yes))return s + yes.t + celifbl(cddr(a));
    s += "{\n" + yes.t + "}";
    if (nilp(cddr(a)))return s + "\n";
    return s + " " + celifbl(cddr(a));
  }
  
  function cifln(a){
    if (nilp(cdr(a)))return cmp1(car(a));
    return cifln2(a);
  }
  
  function cifln2(a){
    var ifpt = cmp(car(a), "iflntest");
    var yes = cmp(cadr(a), "iflnyes");
    var s = ifpt + "?" + yes + ":";
    return chkrt(s + celifln(cddr(a)), "ifln");
  }
  
  function celifln(a){
    if (nilp(cdr(a)))return cmp(car(a), "iflnno");
    return cifln2(a);
  }
  
  function cdo(a){
    if (blk){
      var bd = mblk(a, "do");
      if (nilp(bd))return cmp1(bd);
      return bd;
    }
    return cbin(a, ", ", "doln");
  }
  
  function clop(a){
    var s = "for (";
    s += cmp(car(a), "forbeg") + "; ";
    s += cmp(cadr(a), "bot") + "; ";
    s += cmp(nth("2", a), "bot") + ")";
    return {t: s + chkpar(mblk(ncdr("3", a), "lop")), b: true};
  }
  
  function cwhi(a){
    var s = "while (" + cmp(car(a), "bot") + ")";
    return {t: s + chkpar(mblk(cdr(a), "lop")), b: true};
  }
  
  function cfoi(a){
    var s = "for (";
    s += cmp(car(a), "forbeg");
    s += " in ";
    s += cmp(cadr(a), "bot") + ")";
    return {t: s + chkpar(mblk(cddr(a), "lop")), b: true};
  }
  
  function cswt(a){
    var s = "switch (" + cmp(car(a), "bot") + "){";
    var n = cswt2(cdr(a));
    return {t: s + "\n" + n[0] + "}\n", r: n[1], b: true};
  }
  
  function cswt2(a){
    if (nilp(a))return ["", false];
    var c = car(a);
    if (car(c) == "def"){
      var s = "default: ";
      var bd = mblk(cdr(c), "swt");
      if (nilp(bd))return ["", false];
      if (onep(bd))return [s + bd.t, exip(bd)];
      return [s + "\n" + bd.t, exip(bd)];
    }
    var s = "case " + cmp(car(c), "bot") + ": ";
    var bd = mblk(cdr(c), "swt");
    var n = cswt2(cdr(a));
    if (nilp(bd))return [s + "\n" + n[0], n[1]];
    if (onep(bd)){
      s += bd.t;
      if (exip(bd))return [s + n[0], n[1]];
      return [s + n[0], false];
    }
    s += "\n" + bd.t;
    if (exip(bd))return [s + n[0], n[1]];
    return [s + n[0], false];
  }
  
  function ccas(a){
    var s = "switch (" + cmp(car(a), "bot") + "){";
    var n = ccas2(cdr(a));
    return {t: s + "\n" + n[0] + "}\n", r: n[1], b: true};
  }
  
  function ccas2(a){
    if (nilp(a))return ccas2(lis([]));
    if (nilp(cdr(a))){
      var s = "default: ";
      var bd = cmp(car(a), "cas");
      if (nilp(bd))return [s + "break;\n", false];
      if (onep(bd)){
        if (exip(bd))return [s + bd.t, true];
        if (brkp(bd))return [s + bd.t, false];
        return [s + $.but(bd.t) + " break;\n", false]; // cut off \n
      }
      s += "\n" + bd.t;
      if (exip(bd))return [s, true];
      return [s + "break;\n", false];
    }
    var s = "case " + cmp(car(a), "bot") + ": ";
    var bd = cmp(cadr(a), "cas");
    var n = ccas2(cddr(a));
    if (nilp(bd))return [s + "break;\n" + n[0], false];
    if (onep(bd)){
      if (exip(bd))return [s + bd.t + n[0], n[1]];
      if (brkp(bd))return [s + bd.t + n[0], false];
      return [s + $.but(bd.t) + " break;\n" + n[0], false];
    }
    s += "\n" + bd.t;
    if (exip(bd))return [s + n[0], n[1]];
    if (brkp(bd))return [s + n[0], false];
    return [s + "break;\n" + n[0], false];
  }
  
  function cbrk(a){
    if (!blk)err(cbrk, "brk a = $1 must be in block", a);
    return {t: "break;\n", k: true};
  }
  
  function ccont(a){
    if (!blk)err(ccont, "cont a = $1 must be in block", a);
    return {t: "continue;\n", k: true};
  }
  
  function cret(a){
    if (!blk)err(cret, "ret a = $1 must be in block", a);
    return cmp(car(a), "ret");
  }
  
  function cthr(a){
    if (!blk)err(cthr, "thr a = $1 must be in block", a);
    return cmp(car(a), "thr");
  }
  
  function cnrt(a){
    if (!blk)err(cnrt, "nrt a = $1 must be in block", a);
    return cmp(car(a), "nrt");
  }
  
  /*
  (try a b c (catch e a b c))
  */
  
  
  function ctry(a){
    if (!blk)err(ctry, "try a = $1 must be in block", a);
    var t = cmp(car(a), "try");
    var e = cmp(cadr(a), "bot");
    var c = cmp(nth("2", a), "catch");
    var s = "try {\n" + t.t + "}";
    s += " catch (" + e + ")";
    s += "{\n" + c.t + "}";
    if (!nilp(ncdr("3", a))){
      var f = cmp(nth("3", a), "fin");
      s += " finally {\n" + f.t + "}";
    }
    s += "\n";
    return {t: s, r: t.r && c.r, b: true};
  }
  
  function cmac(a){
    mput(car(a), evl(cons("fn", cdr(a))));
    return cmp1([]);
  }
  
  function cdmac(a){
    mput(car(a), udf);
    return cmp1([]);
  }
  
  function crmac(a){
    mput(cadr(a), mget(car(a)));
    mput(car(a), udf);
    return cmp1([]);
  }
  
  function cmblk(a){
    mlay();
    var ret = cmp1(cons("js-do", a));
    mpeel();
    return ret;
  }
  
  // (smac nil #[])
  function csmac(a){
    smput(car(a), cadr(a));
    return cmp1([]);
  }
  
  function cdsmac(a){
    smput(car(a), udf);
    return cmp1([]);
  }
  
  function crsmac(a){
    smput(cadr(a), smget(car(a)));
    smput(car(a), udf);
    return cmp1([]);
  }
  
  function csmblk(a){
    smlay();
    var ret = cmp1(cons("js-do", a));
    smpeel();
    return ret;
  }
  
  /*function cmlet(a){
    var mc = car(a);
    var nm = car(mc);
    var bef = mget(nm);
    mput(nm, evl(cons("fn", cdr(mc))));
    var ret = cmp1(cons("js-do", cdr(a)));
    mput(nm, bef);
    return ret;
  }*/
  
  function cexe(a){
    return cmp1(evl(cons("do", a)));
  }
  
  function cqt(a){
    if (nump(a))return chkrt(a, "atm");
    if (nilp(a))return cmp1([]);
    if (symp(a))return chkrt($.dsp(a), "atm");
    if (strp(a))return chkrt($.dsp(rp(a)), "atm");
    if (rgxp(a))return chkrt($.str(a), "atm");
    if (lisp(a))return chkrt(cqlis(a), "atm");
    return cmp1([]);
  }
  
  function cqlis(a){
    if (atmp(a))return cmp(aqt(a), "inln");
    return "[" + cmp(aqt(car(a)), "inln") + ", "
               + cqlis(cdr(a)) + "]";
  }
  
  function aqt(a){
    return lis("qt", a);
  }
  
  //// Macros ////
  
  function get(a, env){
    if (env === udf)return udf;
    if (env[a] === udf)return get(a, env[0]);
    return env[a];
  }
  
  function put(a, x, env){
    return env[a] = x;
  }
  
  var macs = {};
  
  function mget(a){
    return get(a, macs);
  }
  
  function mput(a, x){
    return put(a, x, macs);
  }
  
  function macp(a){
    return !udfp(mget(a));
  }
  
  function mlay(){
    return macs = {0: macs};
  }
  
  function mpeel(){
    return macs = macs[0];
  }
  
  var smacs = {};
  
  function smget(a){
    return get(a, smacs);
  }
  
  function smput(a, x){
    return put(a, x, smacs);
  }
  
  function smacp(a){
    return !udfp(smget(a));
  }
  
  function smlay(){
    return smacs = {0: smacs};
  }
  
  function smpeel(){
    return smacs = smacs[0];
  }
  
  //// Functions ////
  
  function cmcx1(a){
    if (lisp(a) && macp(car(a))){
      return apl(mget(car(a)), cdr(a));
    }
    return a;
  }
  
  function cmcx(a){
    if (lisp(a)){
      if (macp(car(a)))return cmcx(apl(mget(car(a)), cdr(a)));
      return map(cmcx, a);
    }
    return a;
  }
  
  //// Compile from str ////
  
  function cmps(a){
    return cmp(prs(a));
  }
  
  cmps("(js-mac do a `(js-do ,@a))");
  
  ////// JS functions //////
  
  jn({
    cmcx1: cmcx1,
    cmcx: cmcx
  });
  
  bol({
    "blk?": blkp,
    "ret?": retp,
    "thr?": thrp
  });
  
  ////// Object exposure //////
  
  $.att({
    cmp: cmp,
    cmps: cmps,
    
    cmcx: cmcx,
    
    blkp: blkp,
    retp: retp,
    thrp: thrp
  }, L);
  
  ////// Testing //////
  
  
  
})(window);
