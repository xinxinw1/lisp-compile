/***** Lisp to JS Compiler Devel *****/

/* requires tools >= 3.0 */
/* requires lisp-parse */

(function (win, udef){
  ////// Import //////
  
  var err = $.err;
  
  ////// Macros //////
  
  ////// Lisp functions //////
  
  //// Predicates ////
  
  function listp(a){
    return $.arrp(a) && !($.strp(a[0]) && a[0][0] == "&");
  }
  
  function pairp(a){
    return listp(a) && !listp(cdr(a));
  }
  
  function atomp(a){
    return !listp(a) || $.len(a) == 0;
  }
  
  function nilp(a){
    return $.arrp(a) && $.len(a) == 0;
  }
  
  function nump(a){
    return $.nump(a) || $.has(/^-?[0-9]+(\.[0-9]+)?$/, a);
  }
  
  function strp(a){
    return $.arrp(a) && $.beg(a, "&str");
  }
  
  function objp(a){
    return $.objp(a);
  }
  
  function arrp(a){
    return $.arrp(a) && $.beg(a, "&arr");
  }
  
  function procp(a){
    return fnp(a) || specp(a);
  }
  
  function symp(a){
    return $.strp(a);
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
    var args = arguments;
    var r = [];
    for (var i = $.len(args)-1; i >= 0; i--){
      r = cons(args[i], r);
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
  
  function push(x, a){
    if (nilp(a)){
      a[1] = [];
      a[0] = x;
      return a;
    }
    a[1] = cons(a[0], a[1]);
    a[0] = x;
    return a;
  }
  
  function pop(a){
    var x = car(a);
    if (nilp(cdr(a))){
      a.pop();
      a.pop();
    } else {
      a[0] = cadr(a);
      a[1] = cddr(a);
    }
    return x;
  }
  
  ////// Lisp compiler //////
  
  var rets = [];
  
  function cmp(a, ret){
    if ($.udefp(ret))return cmp1(a);
    push(ret, rets);
    var s = cmp1(a);
    pop(rets);
    return s;
  }
  
  function cmp1(a){
    if (atomp(a)){
      if (symp(a)){
        if (car(rets) == "objname")return ovar(a);
        return jvar(a);
      }
      if (arrp(a))return cmparr(a);
      if (strp(a))return "\"" + a[1] + "\"";
      if (nump(a))return String(a);
      if (objp(a))return cmpobj(a);
      if (nilp(a))return "";
      err(cmp1, "Unexpected atom in a = $1", a);
    }
    var o = car(a);
    if (arrp(o))return cmparr(o) + "[" + cmp(cadr(o), "index") + "]";
    if (strp(o))return "\"" + o[1] + "\"" + "[" + cmp(cadr(o), "index") + "]";
    if (nump(o))return String(o) + "[" + cmp(cadr(o), "index") + "]";
    if (objp(o))return cmpobj(o) + "[" + cmp(cadr(o), "index") + "]";
    if (!symp(o))return cmp(o, "fnref") + makebrac(cdr(a));
    return cmpfunc(o, cdr(a));
  }
  
  function cmparr(a){
    a = a[1];
    var s = "[";
    if ($.len(a) > 0){
      s += cmp(a[0], "inln");
      for (var i = 1; i < $.len(a); i++){
        s += ", " + cmp(a[i], "inln");
      }
    }
    s += "]";
    return s;
  }
  
  function cmpobj(a){
    var r = [];
    for (var i in a){
      r.push(cmp(i, "objname") + ": " + cmp(a[i], "inln"));
    }
    return "{" + $.join(r, ", ") + "}";
  }
  
  // a = args
  function cmpfunc(o, a){
    if (o != "."){
      if (o[0] == ".")return cmpmthd2(o, a);
      if ($.last(o) == ".")return cmpnew(o, a);
    }
    switch (o){
      case ".": return cmpmthd(a);
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
      case "^": return "Math.pow" + makebrac(a); // function call near highest level so don't need brackets
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
      case "not": return cmpsgn("!", a);
      case "return": return cmpret(a);
      case "switch": return cmpswit(a);
      case "case": return cmpcase(a);
      case "break": return cmpbreak(a);
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
  
  function cmpmthd(a){
    return brac(cmp(car(a), "mthdclass") + "." + cmp(cadr(a), "varname") + makebrac(cddr(a)), rets, "mthd");
  }
  
  function cmpmthd2(o, a){
    return brac(cmp(car(a), "mthdclass") + o + makebrac(cdr(a)), rets, "mthd");
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
    if (!inblock(rets)){
      if (car(rets) == "forbeg")return "var " + cmp(car(a), "varname") + " = " + cmp(cadr(a), "eqval");
      err(cmpvar, "var must be in block in a = $1", a);
    }
    return "var " + cmp(car(a), "varname") + " = " + cmp(cadr(a), "eqval") + ";\n";
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
      if (ret){
        if (oneptp(nopt)){
          return "return " + nopt + ";\n";
        }
        return nopt;
      }
      if (oneptp(nopt))return nopt + ";\n";
      return "{\n" + nopt + "}\n";
    }
    var ifpt = cmp(car(a), "bractest");
    var yespt = cmp(cadr(a), "if");
    var s = "if (" + ifpt + ")";
    if (oneptp(yespt)){
      if (ret)s += "return ";
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
    var body = block(nthcdr(3, a), "for");
    if (oneptp(body))return s + body + ";\n";
    return s + "{\n" + body + "}\n";
  }
  
  function cmpret(a){
    if (!inblock(rets))err(cmpret, "return must be in block position in a = $1", a);
    var body = cmp(car(a), "return");
    if (retp(rets))return body;
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
        if (retp(rets))s += "return " + body + ";\n";
        else s += body + "; break;\n";
      } else {
        s += body;
        if (!retp(rets))s += "break;\n";
      }
      return s;
    }
    var s = "case " + cmp(car(a), "caseif") + ": ";
    var body = cmp(cadr(a), "case");
    if (body != ""){
      if (oneptp(body)){
        if (retp(rets))s += "return " + body + ";\n";
        else s += body + "; break;\n";
      } else {
        s += "\n" + body;
        if (!retp(rets))s += "break;\n";
      }
    } else {
      if (oneptp(body)){
        if (retp(rets))s += "return;\n";
        else s += "break;\n";
      } else {
        if (!retp(rets))s += "break;\n";
        else s += "\n";
      }
    }
    if (nilp(cddr(a)))return s;
    return s + cmpcase2(cddr(a));
  }
  
  function cmpbreak(a){
    if (retp(rets))return "";
    return "break";
  }
  
  function block(a, ret){
    if (nilp(a))return "";
    if (nilp(cdr(a))){
      var s = "";
      var curr = cmp(car(a), ret+"last");
      if (oneptp(curr)){
        if (retp(rets) || ret == "fn")s += "return ";
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
        if (retp(rets) || ret == "fn")s += "return ";
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
  
  var blocks = ["do", "dolast", "for", "forlast", "while", "whilelast", "fn", "fnlast", "if", "switchlast", "case"];
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
  
  var prec = ["bractest", "if",
              "caseif", "case", "switch", "switchlast",
              "fn", "fnlast",
              "do", "dolast",
              "return",
              "forbeg", "fortest", "forend",
              "for", "forlast",
              "index",
              "doln", "inln",
              "eq", "eqval",
              "iflntest", "iflnans",
              "or", "and",
              "is", "isfront", "isback",
              "lt", "gt", "le", "ge",
              "add", "sub",
              "mul", "div",
              "unary",
              "pp", "mm",
              "lambda",
              "fnref",
              "new",
              "refee", "ref",
              "mthdclass", "mthd"];
              
  function higher(a, b){
    var posa = $.pos(a, prec);
    var posb = $.pos(b, prec);
    if (posa == -1)err(higher, "Unknown a = $1", a);
    if (posb == -1)err(higher, "Unknown b = $1", b);
    return posa > posb;
  }
      
  
  /*var dobrac = ["inln", "doln"];
  function bracpdo(ret){
    return $.has(ret, dobrac);
  }*/
  
  function brac(a, rets, curr){
    if (bracp(a, rets, curr))return "(" + a + ")";
    return a;
  }
  
  function jvar(a){
    if (!varp(a))err(jvar, "Invalid var name a = $1", a);
    return dash2case(a);
  }
  
  function ovar(a){
    if (varp(a))return a;
    return "\"" + a + "\"";
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
    return $.has(/^[a-zA-Z$][a-zA-Z0-9.$-]*$/, a);
  }
  
  function propp(a){
    return $.has(/^[^[]*$/, a);
  }
  
  
  ////// Object exposure //////
  
  win.Lisp = $.apd({
    cmp: cmp
  }, Lisp);
  
  ////// Testing //////
  
  //al(prs("(+ 2 3)"));
  
})(window);
