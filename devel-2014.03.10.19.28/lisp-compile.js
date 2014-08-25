/***** Lisp to JS Compiler Devel *****/

/* require tools >= 3.0 */
/* require lisp-parse */
/* require lisp-disp */

(function (win, udef){
  ////// Import //////
  
  var err = Lisp.err;
  
  ////// Lisp functions //////
  
  //// Predicates ////
  
  function consp(a){
    return $.arrp(a) && !($.strp(a[0]) && a[0][0] == "&");
  }
  
  function atomp(a){
    return !consp(a) || a.length == 0;
  }
  
  function nilp(a){
    return $.arrp(a) && a.length == 0;
  }
  
  function nump(a){
    return $.strp(a) && $.has(/^-?[0-9]+(\.[0-9]+)?$/, a);
  }
  
  function strp(a){
    return $.arrp(a) && a[0] === "&str";
  }
  
  function objp(a){
    return $.objp(a);
  }
  
  function arrp(a){
    return $.arrp(a) && a[0] === "&arr";
  }
  
  function rgxp(a){
    return $.rgxp(a);
  }
  
  function procp(a){
    return fnp(a) || specp(a);
  }
  
  function symp(a){
    return $.strp(a) && !nump(a);
  }
  
  //// Basic ////
  
  function car(a){
    return (a[0] !== udef)?a[0]:[];
  }
  
  function cdr(a){
    return (a[1] !== udef)?a[1]:[];
  }
  
  function cons(a, b){
    return [a, b];
  }
  
  //// car and cdr extensions ////
  
  function caar(a){
    return car(car(a));
  }
  
  function cadr(a){
    return car(cdr(a));
  }
  
  function cdar(a){
    return cdr(car(a));
  }
  
  function cddr(a){
    return cdr(cdr(a));
  }
  
  //// General ////
  
  function list(){
    var a = arguments;
    var r = [];
    for (var i = $.len(a)-1; i >= 0; i--){
      r = cons(a[i], r);
    }
    return r;
  }
  
  function map(f, a){
    if (nilp(a))return [];
    return cons(f(car(a)), map(f, cdr(a)));
  }
  
  function join(a, x){
    if ($.udefp(x))x = "";
    if (nilp(a))return "";
    return car(a) + join2(cdr(a), x);
  }
  
  function join2(a, x){
    if (nilp(a))return "";
    return x + car(a) + join2(cdr(a), x);
  }
  
  function nth(n, a){
    if (n == 0)return car(a);
    return nth(n-1, cdr(a));
  }
  
  function nthcdr(n, a){
    if (n == 0)return a;
    return nthcdr(n-1, cdr(a));
  }
  
  ////// Lisp compiler //////
  
  var rets = [];
  
  function cmp(a, ret){
    if ($.udefp(ret))return cmp1(a);
    return $.dyn(rets, ret, function (){
      return cmp1(a);
    });
  }
  
  function cmp1(a){
    if (car(rets) == "objname")return cmponame(a);
    if (atomp(a)){
      if (symp(a))return jvar(a);
      if (strp(a))return $.disp(a[1]);
      if (nump(a))return a;
      if (rgxp(a))return String(a);
      if (nilp(a))return "";
      err(cmp1, "Unexpected atom a = $1", a);
    }
    var o = car(a);
    if (strp(o))return makestr(o[1]) + "[" + cmp(cadr(o), "index") + "]";
    if (nump(o))return o + "[" + cmp(cadr(o), "index") + "]";
    if (rgxp(o))return String(o) + "[" + cmp(cadr(o), "index") + "]";
    if (!symp(o))return cmp(o, "fnref") + makebrac(cdr(a));
    return cmpfunc(o, cdr(a));
  }
  
  /*
  todo:
  macros
  argument destructuring
  fn numbered args
  indenting
  block comments #|  |#
  object.property
  */
  
  // a = args
  function cmpfunc(o, a){
    if (o != "." && o != ".."){
      if (o[0] == ".")return cmpmthd(o, a);
      if ($.last(o) == ".")return cmpnew(o, a);
    }
    switch (o){
      //case ".": return cmpmthd(a);
      case ".": return cmpmthds(a);
      case "+":
      case "-":
      case "*":
      case "/": return cmpsgn(o, a);
      case "%": 
      case "<": 
      case ">": 
      case ">=": 
      case "<=": return cmpsgnsp(o, a);
      case "++":
      case "--": return cmppost(o, a);
      //case "^": return "Math.pow" + makebrac(a); // function call near highest level so don't need brackets
      case "and": 
      case "or": return cmpop(o, a);
      case "#": return cmpref(a);
      case "var": return cmpvar(a);
      case "=":
      case "+=":
      case "-=":
      case "*=": 
      case "%=": return cmpeq(o, a);
      case "fn": return cmpfn(a);
      case "if": return cmpif(a);
      case "def": return cmpdef(a);
      case "do": return cmpdo(a);
      case "is": return cmpis(o, a);
      case "isnt": return cmpis(o, a);
      case "loop": return cmploop(a);
      case "while": return cmpwhile(a);
      case "not": return cmpsgn("!", a);
      case "return": return cmpret(a);
      case "switch": return cmpswit(a);
      case "case": return cmpcase(a);
      case "break": return cmpbreak(a);
      case "forin": return cmpforin(a);
      case "instof": return cmpinstof(a);
      case "throw": return cmpthr(a);
      case "delete": return cmpdel(a);
      case "arr": return cmparr(a);
      case "obj": return cmpobj(a);
      case "list": return cmplis(a);
      case "qt": return cmpqt(a);
    }
    return cmp(o, "fnref") + makebrac(a);
  }
  
  function makebrac(a){
    return "(" + join(cmpall(a, "inln"), ", ") + ")";
  }
  
  function cmpall(a, ret){
    if (nilp(a))return [];
    return cons(cmp(car(a), ret), cmpall(cdr(a), ret));
  }
  
  function cmpalllast(a, ret){
    if (nilp(cdr(a)))return list(cmp(car(a), ret+"last"));
    return cons(cmp(car(a), ret), cmpall(cdr(a), ret));
  }
  
  /*function cmpmthd(a){
    return brac(cmp(car(a), "mthdclass") + "." + cmp(cadr(a), "varname") + makebrac(cddr(a)), rets, "mthd");
  }*/
  
  function cmpmthd(o, a){
    return brac(cmp(car(a), "mthdclass") + "." + cmp($.slc(o, 1), "varname") + makebrac(cdr(a)), rets, "mthd");
  }
  
  function cmpmthds(a){
    return brac(cmp(car(a), "mthdclass") + "." + join(cmpall(cdr(a), "inln"), "."), rets, "mthd");
  }
  
  function cmpnew(o, a){
    return brac("new " + $.slc(o, 0, $.len(o)-1) + makebrac(a), rets, "new");
  }
  
  function cmpsgn(o, a){
    if (nilp(cdr(a)))return brac(o + cmp(car(a), "unary"), rets, "unary");
    return brac(join(cmpall(a, sgnname(o)), o), rets, sgnname(o));
  }
  
  function cmpsgnsp(o, a){
    return brac(join(cmpall(a, sgnname(o)), " " + o + " "), rets, sgnname(o));
  }
  
  function sgnname(o){
    switch (o){
      case "+": return "add";
      case "-": return "sub";
      case "*": return "mul";
      case "/": return "div";
      case "%": return "mod";
      case "<": return "lt";
      case ">": return "gt";
      case "<=": return "le";
      case ">=": return "ge";
      case "++": return "pp";
      case "--": return "mm";
      default: err(sgnname, "Unknown sign o = $1", o);
    }
  }
  
  function cmpop(o, a){
    return brac(join(cmpall(a, o), sgnsym(o)), rets, o);
  }
  
  function sgnsym(a){
    switch (a){
      case "and": return " && ";
      case "or": return " || ";
      case "is": return " === ";
      case "isnt": return " !== ";
      default: err(sgnsym, "Unknown sign a = $1", a);
    }
  }
  
  function cmppost(o, a){
    return brac(cmp(car(a), sgnname(o)) + o, rets, sgnname(o));
  }
  
  function cmpref(a){
    return brac(cmp(car(a), "refee") + "[" + join(cmpall(cdr(a), "index"), "][") + "]", rets, "ref");
  }
  
  function cmpvar(a){
    if (!inblock(rets) && car(rets) != "forbeg"){
      err(cmpvar, "var must be in block in a = $1", a);
    }
    if (nilp(cdr(a)))return "var " + cmp(car(a), "varname");
    return "var " + cmp(car(a), "varname") + " = " + cmp(cadr(a), "eqval");
  }
  
  function cmpeq(o, a){
    return brac(cmp(car(a), "varname") + " " + o + " " + cmp(cadr(a), "eqval"), rets, "eq");
  }
  
  function cmpdef(a){
    if (!inblock(rets))err(cmpdef, "def must be in block position in a = $1", a);
    var s = "function " + cmp(car(a), "varname") + makebrac(cadr(a)) + "{";
    var body = block(nthcdr(2, a), "fn");
    if (body != ""){
      s += "\n";
      if (oneptp(body))s += body + ";\n";
      else s += body;
    }
    return s + "}\n";
  }
  
  function cmpfn(a){
    if (varp(car(a))){
      var s = "function " + cmp(car(a), "varname") + makebrac(cadr(a)) + "{\n";
      var body = block(nthcdr(2, a), "fn");
      if (oneptp(body))body += ";\n";
      return s + body + "}"; //  no \n because fn is inline
    }
    var s = "function " + makebrac(car(a)) + "{";
    var body = block(nthcdr(1, a), "fn");
    if (body != ""){
      s += "\n";
      if (oneptp(body))s += body + ";\n";
      else s += body;
    }
    return brac(s + "}", rets, "lambda");
  }
  
  function cmpif(a){
    var ret = retp(rets);
    if (inblock(rets))return cmpif2(a, ret);
    var ifpt = cmp(car(a), "iflntest");
    var yespt = cmp(cadr(a), "iflnans");
    var nopt = cmp(nth(2, a), "iflnans");
    if (nopt == "")nopt = "false";
    return brac(ifpt + "?" + yespt + ":" + nopt, rets, "ifln");
  }
  
  function cmpif2(a, ret){
    if (nilp(cdr(a))){
      var nopt = cmp(car(a), "if");
      if (ret && canret(nopt)){
        if (oneptp(nopt))return "return " + nopt + ";\n";
        return nopt;
      }
      if (oneptp(nopt))return nopt + ";\n";
      return "{\n" + nopt + "}\n";
    }
    var ifpt = cmp(car(a), "bractest");
    var yespt = cmp(cadr(a), "if");
    var s = "if (" + ifpt + ")";
    if (oneptp(yespt)){
      if (ret && canret(yespt))s += "return ";
      s += yespt + ";\n";
    } else s += "{\n" + yespt + "}\n";
    if (nilp(cddr(a)))return s;
    if (!ret)s += "else ";
    return s + cmpif2(cddr(a), ret);
  }
  
  function cmpdo(a){
    if (inblock(rets))return block(a, "do");
    return brac(join(cmpall(a, "doln"), ", "), rets, "doln");
  }
  
  function cmpis(o, a){
    return brac(cmp(car(a), "isfront") + sgnsym(o) + cmp(cadr(a), "isback"), rets, "is");
  }
  
  function cmploop(a){
    var s = "for (";
    s += cmp(car(a), "forbeg") + "; ";
    s += cmp(cadr(a), "fortest") + "; ";
    s += cmp(nth(2, a), "forend") + ")";
    var body = block(nthcdr(3, a), "loop");
    if (oneptp(body))return s + body + ";\n";
    return s + "{\n" + body + "}\n";
  }
  
  function cmpwhile(a){
    var s = "while (";
    s += cmp(car(a), "bractest") + ")";
    var body = block(cdr(a), "loop");
    if (oneptp(body))return s + body + ";\n";
    return s + "{\n" + body + "}\n";
  }
  
  function cmpret(a){
    if (!inblock(rets))err(cmpret, "return must be in block position in a = $1", a);
    var body = cmp(car(a), "return");
    if (!canret(body))err(cmpret, "can't return body = $1", body);
    //if (retp(rets))return body;
    if (body == "")return "return";
    return "return " + body;
  }
  
  function cmpswit(a){
    var test = cmp(car(a), "bractest");
    var s = "switch (" + test + "){";
    if (!nilp(cdr(a))){
      s += "\n" + cmpswit2(cdr(a));
    }
    return s + "}\n";
  }
  
  function cmpswit2(a){
    var curr = car(a);
    var ifpt = cmp(car(curr), "caseif");
    var s = "";
    if (ifpt == "default")s += "default: ";
    else s += "case " + ifpt + ": ";
    var body = block(cdr(curr), "switch");
    if (oneptp(body) && body != "")s += body + ";\n";
    else s += "\n" + body;
    if (nilp(cdr(a)))return s;
    return s + cmpswit2(cdr(a));
  }
  
  function cmpcase(a){
    var test = cmp(car(a), "bractest");
    var s = "switch (" + test + "){";
    if (!nilp(cdr(a))){
      s += "\n" + cmpcase2(cdr(a));
    }
    return s + "}\n";
  }
  
  function cmpcase2(a){
    if (nilp(cdr(a))){
      var s = "default: ";
      var body = cmp(car(a), "case");
      if (oneptp(body)){
        if (retp(rets) && canret(body))s += "return " + body + ";\n";
        else {
          s += body + ";";
          if (canbreak(body))s += " break;";
          s += "\n";
        }
      } else {
        s += "\n" + body;
        if (!retp(rets) && canbreak(body))s += "break;\n";
      }
      return s;
    }
    var s = "case " + cmp(car(a), "caseif") + ": ";
    var body = cmp(cadr(a), "case");
    if (body != ""){
      if (oneptp(body)){
        if (retp(rets) && canret(body))s += "return " + body + ";\n";
        else {
          s += body + ";";
          if (canbreak(body))s += " break;";
          s += "\n";
        }
      } else {
        s += "\n" + body;
        if (!retp(rets) && canbreak(body))s += "break;\n";
      }
    } else {
      if (retp(rets))s += "return;\n";
      else s += "break;\n";
    }
    if (nilp(cddr(a)))return s;
    return s + cmpcase2(cddr(a));
  }
  
  function cmpbreak(a){
    return retp(rets)?"":"break";
  }
  
  function cmpforin(a){
    var name = cmp(car(a), "varname");
    var s = "for (";
    if (varp(name))s += "var ";
    s += name + " in ";
    s += cmp(cadr(a), "forinobj") + ")";
    var body = block(cddr(a), "loop");
    if (oneptp(body))return s + body + ";\n";
    return s + "{\n" + body + "}\n";
  }
  
  function cmpinstof(a){
    var s = cmp(car(a), "instofobj") + " instanceof ";
    s += cmp(cadr(a), "varname");
    return brac(s, rets, "instof");
  }
  
  function cmpthr(a){
    return "throw " + cmp(car(a), "throw");
  }
  
  function cmpdel(a){
    return brac("delete " + cmp(car(a), "delobj"), rets, "del");
  }
  
  function cmparr(a){
    return "[" + cmparr2(a) + "]";
  }
  
  function cmparr2(a){
    if (nilp(a))return "";
    if (nilp(cdr(a)))return cmp(car(a), "inln");
    return cmp(car(a), "inln") + ", " + cmparr2(cdr(a));
  }
  
  function cmpobj(a){
    return "{" + cmpobj2(a) + "}";
  }
  
  function cmpobj2(a){
    if (nilp(a))return "";
    if (nilp(cdr(a)))return cmp(car(a), "objname") + ": undefined";
    var s = cmp(car(a), "objname") + ": " + cmp(cadr(a), "inln");
    if (nilp(cddr(a)))return s;
    return s + ", " + cmpobj2(cddr(a));
  }
  
  function cmplis(a){
    if (nilp(a))return "[]";
    return "[" + cmp(car(a), "inln") + ", " + cmplis(cdr(a)) + "]";
  }
  
  function cmpqt(a){
    if (consp(car(a)))return cmpqtlis(car(a));
    return cmp(car(a), "qt");
  }
  
  function cmpqtlis(a){
    if (nilp(a))return "[]";
    return "[" + cmpqt(list(car(a))) + ", " + cmpqtlis(cdr(a)) + "]";
  }
  
  function block(a, ret){
    if (nilp(a))return "";
    if (nilp(cdr(a))){
      var s = "";
      var curr = cmp(car(a), ret+"last");
      if (oneptp(curr)){
        if (retp(rets) || ret == "fn" && canret(curr))s += "return ";
        return s + curr;
      }
      return curr;
    }
    return block1(a, ret);
  }
  
  function block1(a, ret){
    if (nilp(cdr(a))){
      var s = "";
      var curr = cmp(car(a), ret+"last");
      if (oneptp(curr)){
        if (retp(rets) || ret == "fn" && canret(curr))s += "return ";
        return s + curr + ";\n";
      }
      return curr;
    }
    var curr = cmp(car(a), ret);
    if (oneptp(curr))return curr + ";\n" + block1(cdr(a), ret);
    return curr + block1(cdr(a), ret);
  }
  
  function oneptp(a){
    return !$.end(a, ";\n", "}\n");
  }
  
  var blocks = ["do", "dolast", "loop", "looplast", "fn", "fnlast", "if", "switchlast", "case"];
  function inblock(rets){
    return blockp(car(rets));
  }
  
  function blockp(ret){
    if (nilp(ret))return true;
    return $.has(ret, blocks);
  }
  
  var returns = ["fnlast"];
  var atend = ["dolast", "fnlast", "if", "case", "switchlast"];
  function retp(rets){
    if (nilp(rets))return false;
    if (!inblock(rets))return false;
    if ($.has(car(rets), returns))return true;
    if ($.has(car(rets), atend))return retp(cdr(rets));
    return false;
  }
  
  var nobrac = ["bractest", "if", "fn", "fnlast", "forbeg", "fortest", "forend"];
  function bracp(a, rets, curr){
    if ($.has(/^[a-zA-Z0-9.]+$/, a))return false;
    //if ($.has(car(rets), nobrac))return false;
    //if (curr == "doln")return bracpdo(car(rets));
    return !higher(curr, car(rets));
  }
  
  // precedence
  var prec = ["bractest", "if",
              "caseif", "case", "switch", "switchlast",
              "varname",
              "fn", "fnlast",
              "do", "dolast",
              "return", "throw", 
              "forbeg", "fortest", "forend",
              "forinobj",
              "loop", "looplast",
              "index",
              "doln", "inln",
              "eq", "eqval",
              "iflntest", "iflnans", "ifln",
              "or", "and",
              "is", "isfront", "isback",
              "instofobj", "instof",
              "lt", "gt", "le", "ge",
              "add", "sub",
              "mul", "div",
              "delobj", "del",
              "unary",
              "pp", "mm",
              "lambda",
              "fnref",
              "new",
              ["refee", "mthdclass"],
              ["ref", "mthd"]];
  
  var ltr = ["add", "sub", "mul", "div",
             "refee", "mthclass",
             "ref", "mthd"];
  
  function higher(a, b){
    var posa = getprec(a);
    var posb = getprec(b);
    if (posa == -1)err(higher, "Unknown a = $1", a);
    if (posb == -1)err(higher, "Unknown b = $1", b);
    if (posa != posb)return posa > posb;
    if ($.has(a, ltr))return true;
    return false;
  }
  
  function getprec(a){
    for (var i = 0; i < $.len(prec); i++){
      if ($.arrp(prec[i])){
        if ($.has(a, prec[i]))return i;
      } else {
        if (prec[i] === a)return i;
      }
    }
    return -1;
  }
  
  function brac(a, rets, curr){
    if (bracp(a, rets, curr))return "(" + a + ")";
    return a;
  }
  
  function jvar(a){
    if (!varp(a))err(jvar, "Invalid var name a = $1", a);
    return dash2case(a);
  }
  
  function cmponame(a){
    if (symp(a)){
      if (varp(a))return a;
      return $.disp(a);
    }
    if (nump(a))return $.disp(a);
    err(cmponame, "Invalid obj property name a = $1", a);
  }
  
  function dash2case(a){
    var s = "";
    for (var i = 0; i < $.len(a); i++){
      if (a[i] == "-"){
        if (i+1 >= $.len(a))break;
        s += a[i+1].toUpperCase();
        i++;
      } else s += a[i];
    }
    return s;
  }
  
  function varp(a){
    return $.strp(a) && $.has(/^[a-zA-Z$_][a-zA-Z0-9.$_-]*$/, a);
  }
  
  function propp(a){
    return $.has(/^[^[]*$/, a);
  }
  
  function canret(a){
    return !$.beg(a, "var", "return", "break", "throw");
  }
  
  function canbreak(a){
    if ($.beg(a, "return", "break", "throw"))return false;
    return !$.has(/(return|break|throw)[^;]*;\n$/, a);
  }
  
  ////// Object exposure //////
  
  $.apd({
    cmp: cmp
  }, Lisp);
  
  ////// Testing //////
  
  //al(prs("(+ 2 3)"));
  
})(window);
