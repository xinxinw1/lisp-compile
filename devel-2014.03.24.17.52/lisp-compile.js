/***** Lisp to JS Compiler Devel *****/

/* require tools >= 3.1 */
/* require lisp-tools */
/* require lisp-parse */ // cmps uses this
/* require lisp-exec */

(function (win, udf){
  ////// Import //////
  
  var rp = L.rp;
  
  var lisp = L.lisp;
  var atmp = L.atmp;
  var nilp = L.nilp;
  var nump = L.nump;
  var objp = L.objp;
  var rgxp = L.rgxp;
  var udfp = L.udfp;
  var strp = L.strp;
  var arrp = L.arrp;
  var symp = L.symp;
  
  var is = L.is;
  var inp = L.inp;
  
  var dyn = L.dyn;
  
  var map = L.map;
  var joi = L.joi;
  
  var app = L.app;
  
  var psh = L.psh;
  var pop = L.pop;
  
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
  
  ////// Lisp compiler //////
  
  var rts = [];
  var rt = [];
  var blk = true;
  var rtp = false;
  function cmp(a, ret){
    if (udfp(ret))return cmp1(a);
    psh(ret, rts);
    var lrt = rt; rt = ret;
    var lblk = blk; blk = blkp(rt);
    var lrtp = rtp; rtp = retp(rt);
    var r = cmp1(a);
    rtp = lrtp;
    blk = lblk;
    rt = lrt;
    pop(rts);
    return r;
  }
  
  function cmp1(a){
    if (atmp(a)){
      //if (nilp(a))return "undefined";
      if (symp(a))return jvar(a);
      if (strp(a))return $.dsp(rp(a));
      if (nump(a))return a;
      if (rgxp(a))return $.str(a);
      return "";
      //err(cmp1, "Unexpected atom a = $1", a);
    }
    var o = car(a);
    if (strp(o) || nump(o) || rgxp(o)){
      return cmp(o, "refee") + "[" + cmp(cadr(a), "index") + "]";
    }
    if (symp(o))return ccal(o, cdr(a));
    if (lisp(o)){
      if (car(o) == "dtfn")return cdtfn(cdr(o), cdr(a));
    }
    return cmp(o, "fnref") + mbrac(cdr(a));
  }
  
  /*
  .a -> (fn (x . args) (apl (. x a) args))
  .a.b -> (fn (x . args) (apl (. x a b) args))
  
  /*
  todo:
  macros
  argument destructuring
  fn numbered args
  indenting
  */
  
  function cdtfn(o, a){
    /*
    orig a = ((dtfn a b c) x 1 2 3)
    o = (a b c)
    a = (x 1 2 3)
    (cmp `((. ,(car a) ,@o) ,@(cdr a)))
    */
    return cmp1(cons(app(lis(".", car(a)), o), cdr(a)));
  }
  
  // a = args
  function ccal(o, a){
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
      case ".": return cmths(a);
      case "#": return cref(a);
      case "var": return cvar(a);
      case "fn": return cfn(a);
      case "rfn": return crfn(a);
      case "if": return cif(a);
      case "do": return cdo(a);
      case "def": return cdef(a);
      case "loop": return clop(a);
      case "whi": return cwhi(a);
      case "ret": return cret(a);
      case "new": return cnew(a);
      case "swit": return cswit(a);
      case "cas": return ccas(a);
      case "brk": return cbrk(a);
      case "foi": return cfoi(a);
      case "thr": return cthr(a);
      case "arr": return carr(a);
      case "obj": return cobj(a);
      case "lis": return clis(a);
      case "qt": return cqt(a);
      case "mac": return cmac(a);
      case "exe": return cexe(a);
    }
    return cmp(o, "fnref") + mbrac(a);
  }
  
  function mbrac(a){
    return "(" + rp(joi(cpa(a, "inln"), ", ")) + ")";
  }
  
  function cpa(a, ret){
    if (nilp(a))return [];
    if (atmp(a))err(cpa, "Can't cmp improper list a = $1", a);
    if (nilp(car(a)))return cpa(cdr(a), ret);
    return cons(cmp(car(a), ret), cpa(cdr(a), ret));
  }
  
  function cpalas(a, ret){
    if (nilp(a))return [];
    if (atmp(a))err(cpalas, "Can't cmp improper list a = $1", a);
    if (nilp(car(a)))return cpalas(cdr(a), ret);
    if (nilp(cdr(a)))return lis(cmp(car(a), ret+"last"));
    return cons(cmp(car(a), ret), cpalas(cdr(a), ret));
  }
  
  function cpaltr(a, ret){
    if (nilp(a))return [];
    if (atmp(a))err(cpaltr, "Can't cmp improper list a = $1", a);
    if (nilp(car(a)))return cpaltr(cdr(a), ret);
    return cons(cmp(car(a), ret), cpa(cdr(a), ret+"end"));
  }
  
  function cpartl(a, ret){
    if (nilp(a))return [];
    if (atmp(a))err(cpartl, "Can't cmp improper list a = $1", a);
    if (nilp(car(a)))return cpartl(cdr(a), ret);
    if (nilp(cdr(a)))return lis(cmp(car(a), ret));
    return cons(cmp(car(a), ret+"end"), cpartl(cdr(a), ret));
  }
  
  function cubin(a, o, n){
    if (nilp(cdr(a)))return cuna(a, o, n + "una");
    return cbin(a, o, n);
  }
  
  function cuna(a, o, n){
    return brac(o + cmp(car(a), n + "item"), n);
  }
  
  function cbin(a, o, n){
    if (nilp(a))err(cbin, "Can't cmp binary o = $1, n = $2 with no args", o, n);
    if (nilp(cdr(a)))return cmp(car(a), rt);
    var f;
    if (ascp(n))f = cpa;
    else if (ltrp(n))f = cpaltr;
    else if (rtlp(n))f = cpartl;
    else err(cbin, "What? a = $1 | o = $2 | n = $3", a, o, n);
    return brac(rp(joi(f(a, n), o)), n);
  }
  
  /*function sgn(a){
    switch (a){
      case "add": return "+";
      case "sub": return "-";
      case "mul": return "*";
      case "div": return "/";
      case "mod": return " % ";
      case "lt": return " < ";
      case "gt": return " > ";
      case "le": return " <= ";
      case "ge": return " >= ";
      case "and": return " && ";
      case "or": return " || ";
      case "is": return " === ";
      case "isn": return " !== ";
      case "pp": return "++";
      case "mm": return "--";
      case "del": return "delete ";
      default: err(sgn, "Unknown sign a = $1", a);
    }
  }*/
  
  function cmths(a){
    return brac(cmp(car(a), "mthclass") + "." + rp(joi(cpa(cdr(a), "inln"), ".")), "mth");
  }
  
  function cnew(a){
    return brac("new " + cmp(car(a), "newtyp") + mbrac(cdr(a)), "new");
  }
  
  function cref(a){
    return brac(cmp(car(a), "refee") + "[" + rp(joi(cpa(cdr(a), "index"), "][")) + "]", "ref");
  }
  
  function cvar(a){
    if (!blk && rt != "forbeg"){
      err(cvar, "var must be in block in a = $1", a);
    }
    if (nilp(cdr(a)))return "var " + cmp(car(a), "setable");
    return "var " + cmp(car(a), "setable") + " = " + cmp(cadr(a), "set");
  }
  
  /*function cset(o, a){
    return brac(cmp(car(a), "setable") + " " + o + " " + cmp(cadr(a), "setval"), "set");
  }*/
  
  function cdef(a){
    if (!blk)err(cdef, "def must be in block position in a = $1", a);
    if (!lisp(cadr(a)))err(cdef, "cadr(a) = $1 must be a list", cadr(a));
    var s = "function " + jvar(car(a)) + mbrac(cadr(a)) + "{";
    var body = mblk(ncdr("2", a), "fn");
    if (body != ""){
      s += "\n";
      if (onep(body))s += body + ";\n";
      else s += body;
    }
    return s + "}\n";
  }
  
  function cfn(a){
    var s = "function " + mbrac(car(a)) + "{";
    var body = mblk(ncdr("1", a), "fn");
    if (body != ""){
      s += "\n";
      if (onep(body))s += body + ";\n";
      else s += body;
    }
    return brac(s + "}", "lambda"); // no \n because fn is inline
  }
  
  function crfn(a){
    if (!lisp(cadr(a)))err(crfn, "cadr(a) = $1 must be a list", cadr(a));
    var s = "function " + jvar(car(a)) + mbrac(cadr(a)) + "{";
    var body = mblk(ncdr("2", a), "fn");
    if (body != ""){
      s += "\n";
      if (onep(body))s += body + ";\n";
      else s += body;
    }
    return brac(s + "}", "lambda"); // no \n because fn is inline
  }
  
  function cif(a){
    if (blk)return cif2(a);
    var ifpt = cmp(car(a), "iflntest");
    var yespt = cmp(cadr(a), "iflnans");
    var nopt = cmp(nth("2", a), "iflnans");
    if (nopt == "")nopt = "false";
    return brac(ifpt + "?" + yespt + ":" + nopt, "ifln");
  }
  
  function cif2(a){
    if (nilp(cdr(a))){
      var nopt = cmp(car(a), "if");
      if (rtp && canret(nopt)){
        if (onep(nopt))return "return " + nopt + ";\n";
        return nopt;
      }
      if (onep(nopt))return nopt + ";\n";
      return "{\n" + nopt + "}\n";
    }
    var ifpt = cmp(car(a), "bractest");
    var yespt = cmp(cadr(a), "if");
    var s = "if (" + ifpt + ")";
    if (onep(yespt)){
      if (rtp && canret(yespt))s += "return ";
      s += yespt + ";\n";
    } else s += "{\n" + yespt + "}\n";
    if (nilp(cddr(a)))return s;
    if (!rtp)s += "else ";
    return s + cif2(cddr(a));
  }
  
  function cdo(a){
    if (blk)return mblk(a, "do");
    return cbin(a, ", ", "doln");
  }
  
  function clop(a){
    var s = "for (";
    s += cmp(car(a), "forbeg") + "; ";
    s += cmp(cadr(a), "fortest") + "; ";
    s += cmp(nth("2", a), "forend") + ")";
    var body = mblk(ncdr("3", a), "loop");
    if (onep(body))return s + body + ";\n";
    return s + "{\n" + body + "}\n";
  }
  
  function cwhi(a){
    var s = "while (";
    s += cmp(car(a), "bractest") + ")";
    var body = mblk(cdr(a), "loop");
    if (onep(body))return s + body + ";\n";
    return s + "{\n" + body + "}\n";
  }
  
  function cret(a){
    if (!blk)err(cret, "return must be in block position in a = $1", a);
    var body = cmp(car(a), "return");
    if (!canret(body))err(cret, "can't return body = $1", body);
    //if (rtp)return body;
    if (body == "")return "return";
    return "return " + body;
  }
  
  function cswit(a){
    var test = cmp(car(a), "bractest");
    var s = "switch (" + test + "){";
    if (!nilp(cdr(a))){
      s += "\n" + cswit2(cdr(a));
    }
    return s + "}\n";
  }
  
  function cswit2(a){
    var curr = car(a);
    var ifpt = cmp(car(curr), "casif");
    var s = "";
    if (ifpt == "def")s += "default: ";
    else s += "case " + ifpt + ": ";
    var body = mblk(cdr(curr), "switch");
    if (onep(body) && body != "")s += body + ";\n";
    else s += "\n" + body;
    if (nilp(cdr(a)))return s;
    return s + cswit2(cdr(a));
  }
  
  function ccas(a){
    var test = cmp(car(a), "bractest");
    var s = "switch (" + test + "){";
    if (!nilp(cdr(a))){
      s += "\n" + ccas2(cdr(a));
    }
    return s + "}\n";
  }
  
  function ccas2(a){
    if (nilp(cdr(a))){
      var s = "default: ";
      var body = cmp(car(a), "cas");
      if (onep(body)){
        if (rtp && canret(body))s += "return " + body + ";\n";
        else {
          s += body + ";";
          if (canbreak(body))s += " break;";
          s += "\n";
        }
      } else {
        s += "\n" + body;
        if (!rtp && canbreak(body))s += "break;\n";
      }
      return s;
    }
    var s = "case " + cmp(car(a), "casif") + ": ";
    var body = cmp(cadr(a), "cas");
    if (body != ""){
      if (onep(body)){
        if (rtp && canret(body))s += "return " + body + ";\n";
        else {
          s += body + ";";
          if (canbreak(body))s += " break;";
          s += "\n";
        }
      } else {
        s += "\n" + body;
        if (!rtp && canbreak(body))s += "break;\n";
      }
    } else {
      if (rtp)s += "return;\n";
      else s += "break;\n";
    }
    if (nilp(cddr(a)))return s;
    return s + ccas2(cddr(a));
  }
  
  function cbrk(a){
    return rtp?"":"break";
  }
  
  function cfoi(a){
    var name = cmp(car(a), "setable");
    var s = "for (";
    if (jvarp(name))s += "var ";
    s += name + " in ";
    s += cmp(cadr(a), "foinobj") + ")";
    var body = mblk(cddr(a), "loop");
    if (onep(body))return s + body + ";\n";
    return s + "{\n" + body + "}\n";
  }
  
  /*function cinst(a){
    var s = cmp(car(a), "instobj") + " instanceof ";
    s += cmp(cadr(a), "instcls");
    return brac(s, "inst");
  }*/
  
  function cthr(a){
    return "throw " + cmp(car(a), "throw");
  }
  
  /*function cdel(a){
    return brac("delete " + cmp(car(a), "del"), "del");
  }*/
  
  function carr(a){
    return "[" + carr2(a) + "]";
  }
  
  function carr2(a){
    if (nilp(a))return "";
    if (nilp(cdr(a)))return cmp(car(a), "inln");
    return cmp(car(a), "inln") + ", " + carr2(cdr(a));
  }
  
  function cobj(a){
    return "{" + cobj2(a) + "}";
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
    if (nilp(a))return "[]";
    return "[" + cmp(car(a), "inln") + ", " + clis(cdr(a)) + "]";
  }
  
  function cqt(a){
    if (lisp(car(a)))return cqtl(car(a));
    return cmp(car(a), "qt");
  }
  
  function cqtl(a){
    if (nilp(a))return "[]";
    return "[" + cqt(lis(car(a))) + ", " + cqtl(cdr(a)) + "]";
  }
  
  function cmac(a){
    macs[car(a)] = evl(cons("fn", cdr(a)));
    return [];
  }
  
  function cexe(a){
    return cmp1(evl(cons("do", a)));
  }
  
  function mblk(a, ret){
    if (nilp(a))return "";
    if (nilp(cdr(a))){
      var s = "";
      var curr = cmp(car(a), ret+"last");
      if (curr != "" && onep(curr)){
        if (rtp || ret == "fn" && canret(curr))s += "return ";
        return s + curr;
      }
      return curr;
    }
    return mblk1(a, ret);
  }
  
  function mblk1(a, ret){
    if (nilp(cdr(a))){
      var s = "";
      var curr = cmp(car(a), ret+"last");
      if (curr != "" && onep(curr)){
        if (rtp || ret == "fn" && canret(curr))s += "return ";
        return s + curr + ";\n";
      }
      return curr;
    }
    var curr = cmp(car(a), ret);
    if (curr != "" && onep(curr))return curr + ";\n" + mblk1(cdr(a), ret);
    return curr + mblk1(cdr(a), ret);
  }
  
  function onep(a){
    return !$.end(a, ";\n", "}\n");
  }
  
  var blks = ["do", "dolast", "loop", "looplast", "fn", "fnlast", "if", "switchlast", "cas"];
  function blkp(a){
    if (nilp(a))return true;
    return $.has(a, blks);
  }
  
  var returns = ["fnlast"];
  var atend = ["dolast", "fnlast", "if", "cas", "switchlast"];
  function retp(a){
    if ($.has(a, returns))return true;
    if (!$.has(a, atend))return false;
    return rtp;
  }
  
  // precedence
  var prec = [
    "bractest", "if",
    "casif", "cas", "switch", "switchlast",
    "setable",
    "fn", "fnlast",
    "do", "dolast",
    "return", "throw", 
    "forbeg", "fortest", "forend",
    "foinobj",
    "loop", "looplast",
    "index",
    "doln", "dolnend",
    "inln",
    "set", "setend",
    "iflntest",
    "iflnans",
    "ifln",
    "or",
    "and",
    "is", "isend",
    "cpar",
    "add",
    "sub", "subend",
    "mul",
    "div", "divend",
    "mod", "modend",
    ["unaitem", "addunaitem", "subunaitem"],
    ["una", "adduna", "subuna"],
    "inc", "dec", // inc/dec
    ["incitem", "decitem"],
    "newtyp",
    "lambda",
    "fnref",
    "new",
    ["refee", "mthclass"],
    ["ref", "mth"]
  ];
  
  function brac(a, curr){
    if (jvarp(a))return a;
    if (!ge(curr, rt))return "(" + a + ")";
    return a;
  }
  
  function ge(a, b){
    if (nilp(rt))return true;
    if ($.beg(a, "inc", "adduna") && $.beg(b, "inc", "adduna"))return false;
    if ($.beg(a, "dec", "subuna") && $.beg(b, "dec", "subuna"))return false;
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
    "div", "mod",
    "refee", "mthclass",
    "ref", "mth"
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
  
  function jvarp(a){
    return $.strp(a) && $.has(/^[a-zA-Z$_][a-zA-Z0-9$_]*$/, a);
  }
  
  function varp(a){
    return $.strp(a) && $.has(/^[a-zA-Z$_][a-zA-Z0-9$_?-]*$/, a);
  }
  
  /*function propp(a){
    return $.has(/^[^[]*$/, a);
  }*/
  
  function canret(a){
    return !$.beg(a, "var", "return", "break", "throw");
  }
  
  function canbreak(a){
    if ($.beg(a, "return", "break", "throw"))return false;
    return !$.has(/(return|break|throw)[^;]*;\n$/, a);
  }
  
  function cmps(a){
    return cmp(prs(a));
  }
  
  ////// Object exposure //////
  
  $.att({
    cmp: cmp,
    cmps: cmps
  }, L);
  
  ////// Testing //////
  
  //al(prs("(+ 2 3)"));
  
})(window);
