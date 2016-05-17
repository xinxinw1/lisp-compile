(js-mac mac a `(js-mac ,@a))
(mac exe a `(js-exe ,@a))
(mac exen a `(exe ,@a nil))

(mac defn a `(exen (def ,@a)))
(mac macn a `(exen (mac ,@a)))

(mac dot () `|.|)

(mac by (n nm op)
  `(mac ,nm #g
     `(do ,@(map [qq (,,op ,@_)] (grp #g ,n)))))

(mac byone (nm op)
  `(by 1 ,nm ,op))

(mac bytwo (nm op)
  `(by 2 ,nm ,op))

(bytwo alias alias1)

(mac alias1 (new old)
  `(mac ,new #args `(,,old ,@#args)))

(mac jsali a
  `(alias ,@(fla (map jsali1 a))))

(defn jsali1 (a)
  (lis a (app 'js- a)))

(jsali ++ --
       not del
       inst
       arr obj
       # cal
       var fn rfn def new
       if brk cont
       ret thr nret
       mmac mblk smblk exe qt)

(mmac dtfn a (x . args)
  `((. ,x ,@a) ,@args))

(mac amblk a
  `(mblk (smblk ,@a)))

(mac binop (nm nbd obd tbd)
  `(mac ,nm #a
     (fold3 #a
       (fn () ,nbd)
       (fn (a) ,obd)
       (fn (a b) ,tbd))))

(mac binopr (nm nbd obd tbd)
  `(mac ,nm #a
     (foldr3 #a
       (fn () ,nbd)
       (fn (a) ,obd)
       (fn (a b) ,tbd))))

(by 4 binops binop)
(by 4 binoprs binopr)

(binops
  + 0
    `(js-+ ,a)
    `(js-+ ,a ,b)
  
  - 0
    `(js-- ,a)
    `(js-- ,a ,b)
  
  * 1
    a
    `(js-* ,a ,b)
  
  / 1
    `(js-/ 1 ,a)
    `(js-/ ,a ,b)
  
  % 1
    a
    `(js-% ,a ,b)
  
  and 'true
      a
      `(js-and ,a ,b)
  
  or 'false
     a
     `(js-or ,a ,b)
  
  do nil
     a
     `(js-do ,a ,b)
  
  cdo1 nil
       a
       `(js-cdo1 ,a ,b))

(byone setrs setr)

(mac setr (a)
  `(binopr ,a
     nil
     a
     `(,,(app 'js- a) ,a ,b)))

(setrs = += -= *= /= %=)

(byone cmpars cmpar)

(mac cmpar (a)
  `(mac ,a #a
     `(and ,@(map [qq (,,(app 'js- a) ,@_)] (grpovr #a 2 1)))))
     
(cmpars < > <= >= is isn)

(mac |.| (x . a)
  (if (no a) x
      `(|.| ,(let y (car a)
               (if (atm? y) `(js-. ,x ,y)
                   (is (car y) '#) `(# (|.| ,x ,(cadr y)) ,@(cddr y))
                   `((|.| ,x ,(car y)) ,@(cdr y))))
            ,@(cdr a))))

(byone dmac js-dmac)
(bytwo rmac js-rmac)

(bytwo swmac swmac2)

(mac swmac2 (a b)
  `(rmac ,a #a
         ,b ,a
         #a ,b))

(mac mlet (a . bd)
  `(mblk (mac ,@a) ,@bd))

(mac mwith (a . bd)
  `(mblk ,@(map [qq (mac ,@_)] a) ,@bd))

(mac mout (a . bd)
  (slis a
    `(mblk (dmac ,@a) ,@bd)))

(mac mren (old new . bd)
  `(mblk (rmac ,old ,new) ,@bd))

(mac mrens (vs . bd)
  `(mblk (rmac ,@vs) ,@bd))

(bytwo smac js-smac)
(byone dsmac js-dsmac)
(bytwo rsmac js-rsmac)

(mac smlet (a x . bd)
  `(smblk (smac ,a ,x) ,@bd))

(mac smwith (vs . bd)
  `(smblk (smac ,@vs) ,@bd))

(mac smout (a . bd)
  (slis a
    `(smblk (dsmac ,@a) ,@bd)))

(mac let (a x . bd)
  `((fn (,a) ,@bd) ,x))

(mac with (vs . bd)
  (let g (grp vs 2)
    `((fn ,(map car g) ,@bd) ,@(map cadr g))))

(mac withi (vs . bd)
  (let r (remdup vs)
    (if (no r) `(do ,@bd)
        `(with ,r ,@bd))))

(mac withs (vs . bd)
  (if (no vs) `(do ,@bd)
      `(let ,(car vs) ,(cadr vs)
         (with ,(cddr vs) ,@bd))))

(mac blk a
  `((fn () ,@a)))

(mac dec a
  `(var ,@(afta a nil)))

(mac wgs (nm . bd)
  (slis nm
    `(with ,(afta nm '(gs)) ,@bd)))

(mac afn (ag . bd)
  `(rfn self ,ag ,@bd))

(mac ngs (n v . bd)
  `(let ,v (mkngs ,n) ,@bd))

(mac once (vs . bd)
  (slis vs
    (ngs (len vs) gens
      `(with ,(fla (par gens (map [qq (if (sym? ,_) ,_ (gs))] vs)))
         (gswith (lis ,@gens) (lis ,@vs)
           (with ,(fla (par vs gens)) ,@bd))))))

(bytwo surblk surblk2)

(mac surblk2 (a b)
  `(mac ,a #a
     (if (blk?) `(,,b ,@#a)
         `(blk (,,b ,@#a)))))

(surblk while js-while
        loop js-loop
        forin js-forin
        try js-try
        swit js-swit
        case js-case)

(mac for (i n m . bd)
  (once (n m)
    `(loop (var ,i ,n) (<= ,i ,m) (++ ,i) ,@bd)))

(mac down (i n m . bd)
  (once (n m)
    `(loop (var ,i ,n) (>= ,i ,m) (-- ,i) ,@bd)))

(mac to (i n . bd)
  (once n
    `(loop (var ,i 0) (< ,i ,n) (++ ,i) ,@bd)))

(mac fr (i n . bd)
  `(down ,i ,n 0 ,@bd))

(mac ind (i a . bd)
  `(to ,i (len ,a) ,@bd))

(mac inr (i a . bd)
  `(fr ,i (- (len ,a) 1) ,@bd))

(mac each (x a . bd)
  (once a
    `(let ,x nil
       (ind #i ,a
         (= ,x #(,a #i))
         ,@bd))))

(mac eacr (x a . bd)
  (once a
    `(let ,x nil
       (inr #i ,a
         (= ,x #(,a #i))
         ,@bd))))

(mac rep (n . bd)
  `(down #i ,n 1 ,@bd))

(mac when (ts . bd)
  `(if ,ts (do ,@bd)))

(mac stk (a x . bd)
  `(do (psh ,x ,a)
       (var #ret (do ,@bd))
       (pop ,a)
       #ret))

(mac dyn (a x . bd)
  `(do (var #ori ,a)
       (= ,a ,x)
       (var #ret (do ,@bd))
       (= ,a #ori)
       #ret))

; (in x 1 2 3) -> (or (is x 1) (is x 2) (is x 3)
(mac in (x . a)
  (once x
    `(or ,@(map [qq (is ,x ,_)] a))))

(mac inl (nm ag . bd)
  `(mac ,nm ,ag
     `(smwith ,,(let p (pnms ag)
                  (fla (map [qq (,_ (smout ,_ ,(auq _)))] p)))
     ,,@bd)))

(mac dfm (nm ag . bd)
  `(do (def ,nm ,ag ,@bd)
       (inl ,nm ,ag ,@bd)))

(mac jn (ag . bd)
  `(fn ,ag (nret (do ,@bd))))

(mac dej (nm ag . bd)
  `(def ,nm ,ag (nret (do ,@bd))))

(mac &= (x a)
  `(= ,a (+ ,x ,a)))

(mac zap (f a . rst)
  `(= ,a (,f ,a ,@rst)))

(mac swap (a b)
  `(let #c ,a
     (= ,a ,b)
     (= ,b #c)))

(mac nfn (a) `(fn (_) ,a))

(mac psh (x a)
  `(= ,a (app ,a ,x)))

; accumulate
(mac accum (f . bd)
  `(withs (#var [] ,f [psh _ #var])
     ,@bd
     #var))

; Repeatedly evaluates its body till it returns nil, then returns vals.

(mac drai (ex (o eof nil))
  `(with (#acc #[] #done false)
     (while !#done
       (let #res ,ex
         (if (is #res ,eof)
             (= #done true)
             (psh #res #acc))))
     #acc))

(mac whir (var ex end . bd)
  `(with (,var nil #f (tfn ,end))
     (while !(#f (= ,var ,ex)) ,@bd)))

(mac chk (x tst (o alt))
  (once x `(if (,tst ,x) ,x ,alt)))

(mac nof (n a)
  `(let #r (emp ,a)
     (rep ,n (psh ,a #r))
     #r))

(mac cmcx (a)
  `(exe (al (cmcx ,a))))

(mac cmcx1 (a)
  `(exe (al (cmcx1 ,a))))

(mac tags a
  (let (f . s) (splbef a sym?)
    `(mlet (go (a) `(ret (,a)))
        (blk ,@f
          ,@(let g (maplis [lisd (caar _) (caadr _) (cdar _)] s)
              (map mktag1 g))
         (,(caar s))))))

(mac block (i . bd)
  `(let ,i #[]
     (try (do ,@bd)
       #g (if (is #(#g 0) ,i) #(#g 1)
              (thr #g)))))

(mac retfr (i a)
  `(thr #[,i ,a]))

(mac protect (a . bd)
  `(try ,a
     #g (thr #g)
     (do ,@bd)))

(mac objsel a
  `(obj ,@(fla (par a a))))

(defn splbut (a n)
  (if (no n) (splbut a 1)
      (no a) (lis nil nil)
      (no (ncdr n a)) (lis nil (fstn n a))
      (let (l x) (splbut (cdr a) n)
        (lis (cons (car a) l) x))))

(mac cdob1 a
  (let (bef aft) (splbut a 2)
    `(do ,@bef (cdo1 ,(car aft) ,(cadr aft)))))

(exe (var pkgs {}))
(mac mkpackage (nm . bd)
  `(do (exe (= (. pkgs ,nm) {vars nil macs nil}))
       (with (win window udf undefined)
         (mrens (def #def fn #fn var #var mac #mac mblk #mblk)
           (#mac #mkexp ()
             `(= (. win ,,nm)
                 (att (objsel ,@(rev (. pkgs ,nm vars)))
                      (or ,,nm {}))))
           
           (#mac def (nm ag . bd)
             (psh nm (. pkgs ,nm vars))
             `(#def ,nm ,ag (private ,@bd)))
           
           (#mac fn (ag . bd)
             `(#fn ,ag (private ,@bd)))
           
           (#mac var a
             (each x (evry a 2)
               (psh x (. pkgs ,nm vars)))
             `(#var ,@a))
           
           (#mac mac a
             (psh a (. pkgs ,nm macs))
             `(#mac ,@a))
           
           (#mac mblk a
             `(#mblk (rmac #mblk mblk #mac mac)
                     ,@a))
           
           (#mac private a
             `(cdob1 (swmac def #def fn #fn var #var mac #mac mblk #mblk)
                     ,@a
                     (swmac def #def fn #fn var #var mac #mac mblk #mblk)))
           
           ,@bd
           
           (#mkexp)))))


(mac imp (x . a)
  `(do ,@(map [mkimp x _] a)))

(defn mkimp (x a)
  (if (pkgs x)
        (let m (mat [is (car _) a] ((pkgs x) 'macs))
          (if m `(mac ,@m)
              `(var ,a (. ,x ,a))))
      `(var ,a (. ,x ,a))))

(mac handler (x . a)
  (wgs e
    `(try ,x
       ,e (case (typ ,e)
            ,@(fla (map [qq (',(car _) ((fn ,@(cdr _)) ,e))] a))
            (thr ,e)))))

(mac init a
  (mkinit a))

(defn mkinit (a)
  (if (no a) nil
      (let l (car a)
        (if (atm? l) (definit a)
            (case (car l)
              'do (mkinit (app (cdr l) (cdr a)))
              'package `(mkpackage ,(cadr l) ,@(cdr a))
              (definit a))))))

(defn definit (a)
  `(amblk ,@a))

(mac on (syms . a)
  (slis syms
    `(do ,@(map [mkon1 _ a] syms))))

(defn mkon1 (sym a)
  (case sym
    'exe `(do ,@a)
    'cmp `(exe ,@a)
    (err mkon1 "Unknown sym = $1" sym)))
