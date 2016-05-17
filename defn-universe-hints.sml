(* constants introduction, type checking, type synthesizing *)

(* a minimal type theory with universes *)
(**

t,u,A,B ::= x | lambda x : A . t | t u | PI (x : A) . B
         | EQ A t u | REFL A | TYPE_i

+ naive universes (cumulative universe)
+ hints (for Reflection rules)

*)
datatype Term = VAR of string * int
              | LAM of string * Term * Term * int | APP of Term * Term * int | PI of string * Term * Term * int
              | PAIR of Term * Term * int | SIG of string * Term * Term * int | PR1 of Term * int | PR2 of Term * int
              | EQ of Term * Term * Term * int | REFL of Term * int
              | TYPE of int


type Ctxt = (Term * Term) list

(** (e1 = e1' : A) list **)
type Hint = (Term * Term * Term) list

fun remove a xs =
  case xs of
      [] => []
    | x::xs => if x = a then remove a xs else x :: (remove a xs)

(** collect free variables of an expression as a list **)
fun FV e =
  case e of
      VAR (x,_) => [x]
   |  LAM (x,t,e,_) => remove x (FV e @ FV t)
   |  APP (m,n,_) => (FV m) @ (FV n)
   |  PI  (x,A,B,_) => remove x (FV A @ FV B)
   |  PAIR (a,b,_) => (FV a) @ (FV b)
   |  PR1 (p,_) => FV p
   |  PR2 (p,_) => FV p
   |  SIG (x,A,B,_) => remove x (FV A @ FV B)
   |  EQ  (A,x,y,_) => FV A @ FV x @ FV y
   |  REFL (A,_) => FV A
   |  TYPE _ => []

fun member x xs =
  case xs of
      [] => false
    | y::xs => if x = y then true else member x xs

(** invariant: **)
(** (1) each term is tupled with a number representing next free variable to be generated in the term **)
(** (2) fresh variable number of the term is always greater than that of its subterms **)
fun subst (e : Term) (x : string) (m : Term) : Term =
  case e of
      VAR (y,_) => if x = y then m else e
    | LAM (y,t,n,c) => if x = y
                       then e
                       else if member y (FV m)
                       then
                           let val nvar = "T" ^ (Int.toString c)
                           in LAM(nvar,t,(subst (subst n y (VAR (nvar,c+1))) x m),c+1)
                           end
                       else
                           LAM(y,t,(subst n x m),c)
    | APP (e1,e2,c) => APP (subst e1 x m, subst e2 x m,c)
    | PI (y,A,B,c) => if x = y
                        then e
                        else if member y (FV m)
                        then
                            let val nvar = "T" ^ (Int.toString c)
                            in PI (nvar,(subst (subst A y (VAR (nvar,c+1))) x m),
                                        (subst (subst B y (VAR (nvar,c+1))) x m),c+1)
                            end
                        else
                            PI (y,(subst A x m),(subst B x m),c)
    | PAIR (a,b,c) => PAIR (subst a x m, subst b x m, c)
    | SIG (y,A,B,c) => if x = y
                       then e
                       else if member y (FV m)
                       then
                           let val nvar = "T" ^ (Int.toString c)
                           in SIG (nvar,(subst (subst A y (VAR (nvar,c+1))) x m),
                                   (subst (subst B y (VAR (nvar,c+1))) x m),c+1)
                           end
                       else
                           SIG (y,subst A x m, subst B x m,c)
    | PR1 (p,c) => PR1 (subst p x m,c)
    | PR2 (p,c) => PR2 (subst p x m,c)
    | EQ (A,a,b,c) => EQ (subst A x m, subst a x m, subst b x m,c)
    | REFL (A,c) => REFL (subst A x m, c)
    | TYPE _ => e

(** alpha-congruence **)
fun alpha (s : Term) (t : Term) : bool =
  case (s,t) of
      (VAR x, VAR y) => x = y
    | (LAM(x,t,m,_),(LAM(y,t',n,_))) => alpha t t' andalso alpha m (subst n y (VAR (x,0)))
    | (APP(e1,e2,_),APP(t1,t2,_)) => alpha e1 t1 andalso alpha e2 t2
    | (PI(x,A,B,_),PI(y,C,D,_)) => alpha A C andalso alpha B (subst D y (VAR (x,0)))
    | (PAIR(a,b,_),PAIR(c,d,_)) => (alpha a c) andalso (alpha b d)
    | (SIG(x,A,B,_),SIG(y,C,D,_)) => (alpha A C) andalso (alpha B (subst D y (VAR (x,0))))
    | (PR1(p,_),PR1(q,_)) => alpha p q
    | (PR2(p,_),PR1(q,_)) => alpha p q
    | (EQ(A,a,b,_),EQ(B,x,y,_)) => alpha A B andalso alpha a x andalso alpha b y
    | (REFL(A,_),REFL(B,_)) => alpha A B
    | (TYPE n,TYPE m) => n = m
    | _ => false


fun context_lookup (G : Ctxt) (e : Term) =
  case G of
      [] => NONE
    | (x,a)::G => if alpha x e then SOME a else context_lookup G e

fun hint_check (E : Hint) (e1 : Term) (e2 : Term) (t : Term) : bool =
  case E of
      [] => false
    | (A,x,y)::E =>
      (alpha A t andalso (alpha x e1 andalso alpha y e2 orelse (alpha x e2 andalso alpha y e1)))
          orelse hint_check E e1 e2 t

fun Typecheck (G : Ctxt) (E : Hint) (e : Term) (t : Term) : bool =
  case (e,t) of
      (VAR (x,_),tau) =>
      (case context_lookup G (VAR (x,0)) of
           NONE => false
        |  SOME t' => equiv G E t t')
    | (APP (e1,e2,_),tau) =>
      let val t1 = Synthesize G E e1
          val t2 = Synthesize G E e2
      in
          (case (t1,t2) of
               (SOME (LAM (_,t,m,c)), SOME (TYPE i)) => if Typecheck G E t (TYPE i) then true else false
             | (SOME (LAM (_,t,m,c)), SOME t') =>
               if equiv G E t t' then true else false
             |  _ => false)
      end
    | (LAM (x,t,m,c),PI(y,A,B,c')) => (equiv G E t A) andalso (Typecheck ((VAR(x,c),t)::(VAR(y,c'),A)::G) E m B)
    | (PI (x,A,B,c),TYPE n) => Typecheck G E A (TYPE n) andalso Typecheck G E B (TYPE n)
    | (PAIR(a,b,c),SIG(x,A,B,c')) => Typecheck G E a A andalso Typecheck G E b (beta G E (APP (B,a,c')))
    | (SIG(x,A,B,_),TYPE n) => Typecheck G E A (TYPE n) andalso Typecheck G E B (TYPE n)
    | (PR1(PAIR(a,_,_), _),_) => Typecheck G E a t
    | (PR2(PAIR(_,b,_), _),_) => Typecheck G E b t
    | (EQ _ ,TYPE n) => true
    | (REFL(A,_),EQ(B,a,b,_)) => equiv G E A B andalso Typecheck G E a A andalso equiv G E a b
    | (TYPE n,TYPE m) => n < m
    | _ => false
and Synthesize (G : Ctxt) (E : Hint) (e : Term) : Term option =
  case e of
      VAR _ => context_lookup G e
   |  LAM (x,t,n,c) =>
      let val A = beta G E t
          val B = Synthesize ((VAR (x,c),A)::G) E n
      in case B of
              NONE => NONE
           |  SOME B' => SOME (PI (x,A,B',c))
      end
   |  APP (e1,e2,_) =>
      let val f = Synthesize G E e1
      in case f of
             NONE => NONE
          |  SOME f' => case beta G E f' of
                            PI(x,A,B,_) =>
                            let val res = beta G E e2
                            in if Typecheck G E res A then SOME (beta G E (subst B x res)) else NONE end
                         | _ => NONE
      end
   |  REFL (A,c) => NONE
   |  PI (x,A,B,c) =>
      let val ta = Synthesize G E A
          val tb = case ta of
                       NONE => NONE
                    |  SOME t => Synthesize ((VAR (x,0),t)::G) E B
      in case (ta,tb) of
             (SOME (TYPE i), SOME (TYPE j)) =>
             if i < j then SOME (TYPE j) else SOME (TYPE i)
           | (SOME (TYPE i), SOME (VAR _)) => ta
           | (SOME (TYPE _), SOME (PI _)) => ta
           | (SOME (TYPE _), SOME (EQ _)) => ta
           | (SOME (VAR _), SOME (TYPE _)) => tb
           | (SOME (PI _), SOME (TYPE _)) => tb
           | (SOME (EQ _), SOME (TYPE _)) => tb
           | _ => NONE
      end
   | PAIR (a,b,_) =>
     let val ta = Synthesize G E a
         val tb = Synthesize G E b
     in
         (case (ta,tb) of
              (SOME t,SOME (PI (x,A,B,c))) => if equiv G E t A then SOME (SIG (x,A,B,c)) else NONE
            | _ => NONE)
     end
   | SIG (x,A,B,c) =>
     let val ta = Synthesize G E A
         val tb = case ta of
                      NONE => NONE
                   |  SOME t => Synthesize ((VAR (x,0),t)::G) E B
     in case (ta,tb) of
            (SOME (TYPE i), SOME (TYPE j)) =>
            if i < j then SOME (TYPE j) else SOME (TYPE i)
          | (SOME (TYPE i), SOME (VAR _)) => ta
          | (SOME (TYPE _), SOME (PI _)) => ta
          | (SOME (TYPE _), SOME (EQ _)) => ta
          | (SOME (VAR _), SOME (TYPE _)) => tb
          | (SOME (PI _), SOME (TYPE _)) => tb
          | (SOME (EQ _), SOME (TYPE _)) => tb
          | _ => NONE
     end
   | PR1 (p,c) =>
     let val tp = Synthesize G E p
     in case tp of
            SOME (PI(_,A,B,_)) => SOME A
          | _ => NONE
     end
   | PR2 (p,c) =>
     let val tp = Synthesize G E p
     in case tp of
            SOME (SIG(x,A,B,c')) => SOME (APP (B,PR1(p,c),c'))
          | _ => NONE
     end
   |  EQ (A,x,y,c) => Synthesize G E A
   |  TYPE i => SOME (TYPE (i + 1))
and beta (G : Ctxt) (E : Hint) (e : Term) : Term =
    case e of
        VAR _ => e
      | LAM _ =>  e
      | APP (LAM (x,t,m,c1),e2,c) =>
        let val A = beta G E t
        in if Typecheck G E e2 A
           then beta G E (subst m x e2)
           else e
        end
      | APP(e1,e2,c) => APP (beta G E e1, beta G E e2, c)
      | PI (x,A,B,c) => PI (x, beta G E A, B, c)
      | PAIR (a,b,c) => PAIR (beta G E a, beta G E b, c)
      | SIG (x,A,B,c) => SIG (x, beta G E A, B, c)
      | PR1 (p,c) =>
        let val p = beta G E p
        in
            case p of
                PAIR (a,_,_) => a
              | _ => e
        end
      | PR2 (p,c) =>
        let val p = beta G E p
        in
            case p of
                PAIR (_,b,_) => b
              | _ => e
        end
      | EQ (A,x,y,c) => EQ (beta G E A, beta G E x, beta G E y, c)
      | REFL (A,c) => REFL (beta G E A, c)
      | TYPE _ => e
(** eta-congruence **)
and eta (G : Ctxt) (E : Hint) (f : Term) (e : Term) : bool =
  let val t1 = Synthesize G E f
      val t2 = Synthesize G E e
  in
      case (t1,t2) of
          (SOME A, SOME B) =>
          (if alpha A B
           then case f of
                    LAM (x,t,APP (e1,VAR (x',_),_),_) => x = x' andalso equiv G E e1 e
                  | _ => false
           else false)
        | _ => false
  end
(** generic equivalence procedure **)
and equiv (G : Ctxt) (E : Hint) (e1 : Term) (e2 : Term) : bool =
  let val e1 = beta G E e1
      val e2 = beta G E e2
      val t1 = Synthesize G E e1
      val t2 = Synthesize G E e2
  in
      case (t1,t2) of
          (SOME t1, SOME t2) =>
          if alpha t1 t2
          then hint_check E e1 e2 t1 orelse eta G E e1 e2 orelse alpha e1 e2
          else false
       |  _ => false
  end


fun Define (G : Ctxt) (E : Hint) (p1 : Term) (p2 : Term) : Ctxt =
  let val e1 = beta G E p1
      val e2 = beta G E p2
      val t = Synthesize G E e2
  in
      case t of
          NONE => (print "Not a type!"; G)
       |  SOME (TYPE i) =>
          if Typecheck G E e1 e2
          then (e1,e2)::G
          else (print "Type check failed!\n"; G)
       |  _ => (print "Not a type!\n"; G)
  end


(** naive tests **)

val ctxt = (VAR ("A",0),(TYPE 0))::(VAR ("x",0),VAR ("A",0))::(VAR ("Int",0),(TYPE 0))::nil
val hint = nil
(* reflx := refl A x : EQ A x x *)
val reflx = REFL (VAR ("A",0),0)
val idA = EQ (VAR ("A",0),VAR ("x",0),VAR ("x",0),0)
(* id_int := LAM x : Int . x : PI _ : Int . Int *)
val id_int = LAM ("x",VAR ("Int",0),VAR ("x",0),0)
val id_int_t = PI ("y",VAR ("Int",0),VAR ("Int",0),0)
(* id_poly := LAM T : TYPE_0 . (LAM x : T . x) : PI T : TYPE_0 . PI _ : T . T *)
val id_poly = LAM ("T",(TYPE 0),LAM ("x",VAR ("T",0),VAR ("x",0),0),0)
val id_poly_t = PI ("T",(TYPE 0),PI ("y",VAR ("T",0),VAR ("T",0),0),0)

val nctxt = (Define (Define (Define ctxt hint reflx idA) hint id_int id_int_t) hint id_poly id_poly_t)

