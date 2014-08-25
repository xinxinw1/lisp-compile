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
  
  var inp = L.inp;
  
  var las = L.las;
  
  var map = L.map;
  
  var len = L.len;
  
  var joi = L.joi;
  var app = L.app;
  
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
  
  var prs = L.prs;
  var evl = L.evl;
  var apl = L.apl;
  
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
    return !lisp(a);
  }
  
  function exip(a){
    if (onep(a))return $.beg(a, "return", "throw", "break");
    return $.beg(las(a), "return", "throw", "break");
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
    "ret", "thr"
  ];
  function blkp(a){
    if (nilp(a))return true;
    return $.has(a, blks);
  }
  
  var rets = ["fnclas", "ret"];
  var ends = ["dolas", "fnclas", "if", "swtlas", "cas"];
  function retp(a){
    if ($.has(a, rets))return true;
    if (!$.has(a, ends))return false;
    return rtp;
  }
  
  function thrp(a){
    if (a === "thr")return true;
    return thp;
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
  
  var macs = {};
  function macp(a){
    return !udfp(macs[a]);
  }
  
  function jjoi(a, x){
    return rp(joi(a, x));
  }
  
  function chkpar(a){
    if (onep(a))return a;
    return "{\n" + jjoi(a) + "}\n";
  }
  
  ////// Lisp compiler //////
  
  var rts = [];
  var rt = [];
  var blk = true;
  var rtp = false;
  var thp = false;
  function cmp(a, ret){
    if (udfp(ret)){
      var b = cmp1(a);
      if (onep(b))return b;
      return jjoi(b);
    }
    $.L.psh(ret, rts);
    var lrt = rt; rt = ret;
    var lblk = blk; blk = blkp(rt);
    var lrtp = rtp; rtp = retp(rt);
    var lthp = thp; thp = thrp(rt);
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
      if (nilp(a))return chkrt("", "atm");
      if (symp(a)){
        if (a == "nil")return cmp1([]);
        return chkrt(jvar(a), "atm");
      }
      if (strp(a))return chkrt($.dsp(rp(a)), "atm");
      if (nump(a))return chkrt(a, "atm");
      if (rgxp(a))return chkrt($.str(a), "atm");
      err(cmp1, "What? a = $1", a);
    }
    var o = car(a);
    if (strp(o) || nump(o) || rgxp(o)){
      // idref == index ref
      return chkrt(cmp(o, "refee") + "[" + cmp(cadr(a), "bot") + "]", "atm");
    }
    if (symp(o))return cprc(o, cdr(a));
    if (lisp(o)){
      if (car(o) == "dtfn")return cdtfn(cdr(o), cdr(a));
      if (car(o) == "qt")return ccal(cadr(o), cdr(a));
    }
    return ccal(o, cdr(a));
  }
  
  function cprc(o, a){
    if (macp(o))return cmp1(apl(macs[o], a));
    switch (o){
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
      case "lis": return clis(a);
      case ".": return cmths(a);
      case "#": return cref(a);
      case "var": return cvar(a);
      case "fn": return cfn(a);
      case "rfn": return crfn(a);
      case "def": return cdef(a);
      case "new": return cnew(a);
      case "if": return cif(a);
      case "do": return cdo(a);
      case "lop": return clop(a);
      case "whi": return cwhi(a);
      case "foi": return cfoi(a);
      case "swt": return cswt(a);
      case "cas": return ccas(a);
      case "brk": return cbrk(a);
      case "ret": return cret(a);
      case "thr": return cthr(a);
      case "mac": return cmac(a);
      case "exe": return cexe(a);
    }
    return ccal(o, a);
  }
  
  function ccal(o, a){
    return chkrt(cmp(o, "refee") + mpar(a), "atm");
  }
  
  //// Compile all ////
  
  function cpa(a, ret){
    if (nilp(a))return [];
    if (atmp(a))err(cpa, "Can't cmp improper list a = $1", a);
    var c = cmp(car(a), ret);
    if (lisp(c))return app(c, cpa(cdr(a), ret));
    return cons(c, cpa(cdr(a), ret));
  }
  
  function cpalas(a, ret){
    if (nilp(a))return [];
    if (atmp(a))err(cpalas, "Can't cmp improper list a = $1", a);
    if (nilp(cdr(a))){
      var c = cmp(car(a), ret+"las");
      if (lisp(c))return c;
      return lis(c);
    }
    var c = cmp(car(a), ret);
    if (lisp(c))return app(c, cpalas(cdr(a), ret));
    return cons(c, cpalas(cdr(a), ret));
  }
  
  function cpaltr(a, ret){
    if (nilp(a))return [];
    if (atmp(a))err(cpaltr, "Can't cmp improper list a = $1", a);
    if (nilp(cdr(a))){
      var c = cmp(car(a), ret+"end");
      if (lisp(c))return c;
      return lis(c);
    }
    var c = cmp(car(a), ret);
    if (lisp(c))return app(c, cpaltr(cdr(a), ret));
    return cons(c, cpaltr(cdr(a), ret));
  }
  
  function cpartl(a, ret){
    if (nilp(a))return [];
    var c = cmp(car(a), ret+"end");
    if (lisp(c))return app(c, cpa(cdr(a), ret));
    return cons(c, cpa(cdr(a), ret));
  }
  
  //// Blocks ////
  
  function mblk(a, ret){
    if (nilp(a))err(mblk, "What? ret = $1", ret);
    return cpalas(a, ret);
  }
  
  function mpar(a){
    return "(" + jjoi(cpa(a, "inln"), ", ") + ")";
  }
  
  //// Return ////
  
  function chkrt(a, cr){
    if (blk){
      if (thp){
        if (a == "")return "throw;\n";
        return "throw " + a + ";\n";
      }
      if (rtp){
        if (a == "")return "return;\n";
        return "return " + a + ";\n";
      }
      if (a == "")return ";\n";
      return blkbrc(a, cr) + ";\n";
    }
    if (a == "")return "undefined";
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
    if (nilp(cdr(a)))return cprop(car(a)) + ": undefined";
    var s = cprop(car(a)) + ": " + cmp(cadr(a), "inln");
    if (nilp(cddr(a)))return s;
    return s + ", " + cobj2(cddr(a));
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
    if (nilp(a))return "[]";
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
  
  function cmths(a){
    return chkrt(cmp(car(a), "refee") + "."
                 + jjoi(cpa(cdr(a), "inln"), "."), "atm");
  }
  
  function cref(a){
    return chkrt(cmp(car(a), "refee")
                 + "[" + jjoi(cpa(cdr(a), "bot"), "][") + "]", "atm");
  }
  
  function cvar(a){
    if (rt == "forbeg")return cvar2(a);
    if (!blk)err(cvar, "var a = $1 must be in block", a);
    return cvar2(a) + ";\n";
  }
  
  function cvar2(a){
    if (nilp(cdr(a)))return "var " + cmp(car(a), "setab");
    return "var " + cmp(car(a), "setab") + " = " + cmp(cadr(a), "set")
           + cvar3(cddr(a));
  }
  
  function cvar3(a){
    if (nilp(a))return "";
    if (nilp(cdr(a)))return ", " + cmp(car(a), "setab");
    return ", " + cmp(car(a), "setab") + " = " + cmp(cadr(a), "set")
           + cvar3(cddr(a));
  }
  
  function cfn(a){
    var s = "function " + mpar(car(a)) + "{";
    if (nilp(cdr(a)))return chkrt(s + "}", "fn");
    return chkrt(s + "\n" + jjoi(mblk(cdr(a), "fnc")) + "}", "fn");
  }
  
  function crfn(a){
    if (!lisp(cadr(a)))err(crfn, "cadr(a) = $1 must be a list", cadr(a));
    var s = "function " + jvar(car(a)) + mpar(cadr(a)) + "{";
    if (nilp(cddr(a)))return chkrt(s + "}", "fn");
    return chkrt(s + "\n" + jjoi(mblk(cddr(a), "fnc")) + "}", "fn");
  }
  
  function cdef(a){
    if (!blk)err(cdef, "def a = $1 must be in block", a);
    if (!lisp(cadr(a)))err(cdef, "cadr(a) = $1 must be a list", cadr(a));
    var s = "function " + jvar(car(a)) + mpar(cadr(a)) + "{";
    if (nilp(cddr(a)))return s + "}\n";
    return s + "\n" + jjoi(mblk(cddr(a), "fnc")) + "}\n";
  }
  
  function cnew(a){
    return chkrt("new " + cmp(car(a), "refee") + mpar(cdr(a)), "atm");
  }
  
  function cif(a){
    if (!blk)return cifln(a);
    if (nilp(cdr(a)))return cmp1(car(a));
    return cifbl(a);
  }
  
  function cifbl(a){
    var ifpt = cmp(car(a), "bot");
    var yes = cmp(cadr(a), "if");
    var s = "if (" + ifpt + ")";
    if (onep(yes)){
      s += yes;
      if (nilp(cddr(a)))return s;
      if (exip(yes))return s + cifbl2(cddr(a));
      return s + celifbl(cddr(a));
    }
    s += "{\n" + jjoi(yes) + "}";
    if (nilp(cddr(a)))return s + "\n";
    if (exip(yes))return s + "\n" + cifbl2(cddr(a));
    return s + " " + celifbl(cddr(a));
  }
  
  function cifbl2(a){
    if (nilp(cdr(a))){
      var no = cmp(car(a), "if");
      if (onep(no))return no;
      return jjoi(no);
    }
    return cifbl(a);
  }
  
  function celifbl(a){
    if (nilp(cdr(a))){
      var no = cmp(car(a), "if");
      return "else " + chkpar(no);
    }
    return "else " + cifbl2(a);
  }
  
  function cifln(a){
    if (nilp(cdr(a)))return cmp1(car(a));
    return cifln2(a);
  }
  
  function cifln2(a){
    var ifpt = cmp(car(a), "iflntest");
    var yes = cmp(cadr(a), "iflnyes");
    var s = ifpt + "?" + yes + ":";
    if (nilp(cddr(a)))return chkrt(s + "false", "ifln");
    return chkrt(s + celifln(cddr(a)), "ifln");
  }
  
  function celifln(a){
    if (nilp(cdr(a)))return cmp(car(a), "iflnno");
    return cifln2(a);
  }
  
  function cdo(a){
    if (blk)return mblk(a, "do");
    return cbin(a, ", ", "doln");
  }
  
  function clop(a){
    var s = "for (";
    s += cmp(car(a), "forbeg") + "; ";
    s += cmp(cadr(a), "bot") + "; ";
    s += cmp(nth("2", a), "bot") + ")";
    return s + chkpar(mblk(ncdr("3", a), "lop"));
  }
  
  function cwhi(a){
    var s = "while (" + cmp(car(a), "bot") + ")";
    return s + chkpar(mblk(cdr(a), "lop"));
  }
  
  function cfoi(a){
    var s = "for (";
    s += cmp(car(a), "forbeg");
    s += " in ";
    s += cmp(cadr(a), "bot") + ")";
    return s + chkpar(mblk(cddr(a), "lop"));
  }
  
  function cswt(a){
    var s = "switch (" + cmp(car(a), "bot") + "){";
    if (nilp(cdr(a)))return s + "}\n";
    return s + "\n" + cswt2(cdr(a));
  }
  
  function cswt2(a){
    if (nilp(a))return "";
    var c = car(a);
    var s = "";
    if (car(c) == "def")s += "default: ";
    else s += "case " + cmp(car(c), "bot") + ": ";
    if (nilp(cdr(c)))return s + "\n" + cswt2(cdr(a));
    var bd = mblk(cdr(c), "swt");
    if (len(bd) == "1")return s + car(bd) + cswt2(cdr(a));
    return s + "\n" + jjoi(bd) + cswt2(cdr(a));
  }
  
  function ccas(a){
    var s = "switch (" + cmp(car(a), "bot") + "){";
    if (nilp(cdr(a)))return s + "}\n";
    return s + "\n" + ccas2(cdr(a));
  }
  
  function ccas2(a){
    if (nilp(a))return "";
    if (nilp(cdr(a))){
      var s = "default: ";
      var bd = cmp(car(a), "cas");
      if (onep(bd)){
        if (exip(bd))return s + bd;
        return s + $.but(bd) + " break;\n"; // cut off \n
      }
      s += "\n" + jjoi(bd);
      if (exip(bd))return s;
      return s + "break;\n";
    }
    var s = "case " + cmp(car(a), "bot") + ": ";
    var bd = cmp(cadr(a), "cas");
    if (onep(bd)){
      if (exip(bd))return s + bd + ccas2(cddr(a));
      return s + $.but(bd) + " break;\n" + ccas2(cddr(a));
    }
    s += "\n" + jjoi(bd);
    if (exip(bd))return s + ccas2(cddr(a));
    return s + "break;\n" + ccas2(cddr(a));
  }
  
  function cbrk(a){
    if (!blk)err(cbrk, "brk a = $1 must be in block", a);
    return "break;\n";
  }
  
  function cret(a){
    if (!blk)err(cret, "ret a = $1 must be in block", a);
    return cmp(car(a), "ret");
  }
  
  function cthr(a){
    if (!blk)err(cthr, "thr a = $1 must be in block", a);
    return cmp(car(a), "thr");
  }
  
  function cmac(a){
    macs[car(a)] = evl(cons("fn", cdr(a)));
    return [];
  }
  
  function cexe(a){
    return cmp1(evl(cons("do", a)));
  }
  
  //// Compile from str ////
  
  function cmps(a){
    return cmp(prs(a));
  }
  
  ////// Object exposure //////
  
  $.att({
    cmp: cmp,
    cmps: cmps
  }, L);
  
  ////// Testing //////
  
  
  
})(window);
