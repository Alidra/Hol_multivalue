Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INFINITE_CROSS_EQ_term_abbrevs.
Require Import FINITE_CROSS_EQ_spec.
Require Import FINITE_EMPTY_spec.
Require Import INFINITE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem4330225 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4330214 A B s). Qed.
Lemma lem4330226 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4330227 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4330226 A B s) (@lem4330225 A B s)). Qed.
Lemma lem4330228 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term2 A B s t.
Proof. exact (@lem4330227 A B s t). Qed.
Lemma lem4330229 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term2 A B s t) = ((term3 A B s t) = (term4 A B s t)).
Proof. exact (eq_refl (term2 A B s t)). Qed.
Lemma lem4330231 {A : Type'} (s : A -> Prop) : term5 A s.
Proof. exact (@lem3198543 A s). Qed.
Lemma lem4330232 {A : Type'} (s : A -> Prop) : (term5 A s) = ((@INFINITE A s) = (term6 A s)).
Proof. exact (eq_refl (term5 A s)). Qed.
Lemma lem4330245 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term6 A s).
Proof. exact (EQ_MP (@lem4330232 A s) (@lem4330231 A s)). Qed.
Lemma lem4330246 {A B : Type'} (s : type1210 A B) : (@INFINITE (prod A B) s) = (term7 A B s).
Proof. exact (@lem4330245 (prod A B) s). Qed.
Lemma lem4330247 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term8 A B s t) = (term9 A B s t).
Proof. exact (@lem4330246 A B (@CROSS B A s t)). Qed.
Lemma lem4330249 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term3 A B s t) = (term4 A B s t).
Proof. exact (EQ_MP (@lem4330229 A B s t) (@lem4330228 A B s t)). Qed.
Lemma lem4330250 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term3 A B s t) = (term4 A B s t).
Proof. exact (@lem4330249 A B s t). Qed.
Lemma lem4330261 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4330262 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term9 A B s t) = (term10 A B s t).
Proof. exact (MK_COMB (@lem4330261) (@lem4330250 A B s t)). Qed.
Lemma lem4330263 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term8 A B s t) = (term10 A B s t).
Proof. exact (TRANS (@lem4330247 A B s t) (@lem4330262 A B s t)). Qed.
Lemma lem4330264 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4330265 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term11 A B s t) = (term12 A B s t).
Proof. exact (MK_COMB (@lem4330264) (@lem4330263 A B s t)). Qed.
Lemma lem4330273 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term6 A s).
Proof. exact (EQ_MP (@lem4330232 A s) (@lem4330231 A s)). Qed.
Lemma lem4330274 {B : Type'} (s : B -> Prop) : (@INFINITE B s) = (term6 B s).
Proof. exact (@lem4330273 B s). Qed.
Lemma lem4330275 {B : Type'} (t : B -> Prop) : (@INFINITE B t) = (term6 B t).
Proof. exact (@lem4330274 B t). Qed.
Lemma lem4330276 {A : Type'} (s : A -> Prop) : (term13 A s) = (term13 A s).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem4330277 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term14 A B s t) = (term15 A B s t).
Proof. exact (MK_COMB (@lem4330276 A s) (@lem4330275 B t)). Qed.
Lemma lem4330280 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4330281 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term16 A B s t) = (term17 A B s t).
Proof. exact (MK_COMB (@lem4330280) (@lem4330277 A B s t)). Qed.
Lemma lem4330285 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term6 A s).
Proof. exact (EQ_MP (@lem4330232 A s) (@lem4330231 A s)). Qed.
Lemma lem4330286 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term6 A s).
Proof. exact (@lem4330285 A s). Qed.
Lemma lem4330287 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4330288 {A : Type'} (s : A -> Prop) : (term18 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem4330287) (@lem4330286 A s)). Qed.
Lemma lem4330291 {B : Type'} (t : B -> Prop) : (term20 B t) = (term20 B t).
Proof. exact (eq_refl (term20 B t)). Qed.
Lemma lem4330292 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term21 A B s t) = (term22 A B s t).
Proof. exact (MK_COMB (@lem4330288 A s) (@lem4330291 B t)). Qed.
Lemma lem4330295 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term23 A B s t) = (term24 A B s t).
Proof. exact (MK_COMB (@lem4330281 A B s t) (@lem4330292 A B s t)). Qed.
Lemma lem4330298 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : ((term8 A B s t) = (term23 A B s t)) = ((term10 A B s t) = (term24 A B s t)).
Proof. exact (MK_COMB (@lem4330265 A B s t) (@lem4330295 A B s t)). Qed.
Lemma lem4330301 {A B : Type'} (s : A -> Prop) : (term25 A B s) = (term26 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4330298 A B s t)). Qed.
Lemma lem4330302 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4330303 {A B : Type'} (s : A -> Prop) : (term27 A B s) = (term28 A B s).
Proof. exact (MK_COMB (@lem4330302 B) (@lem4330301 A B s)). Qed.
Lemma lem4330308 {A B : Type'} : (term29 A B) = (term30 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4330303 A B s)). Qed.
Lemma lem4330309 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4330310 {A B : Type'} : (term31 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem4330309 A) (@lem4330308 A B)). Qed.
Lemma lem4330315 {A B : Type'} : (term32 A B) = (term31 A B).
Proof. exact (SYM (@lem4330310 A B)). Qed.
Lemma lem4330317 (p : Prop) : p = (term33 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4330318 {A B : Type'} : (term32 A B) = (term34 A B).
Proof. exact (@lem4330317 (term32 A B)). Qed.
Lemma lem4330319 {A B : Type'} : (term34 A B) = (term32 A B).
Proof. exact (SYM (@lem4330318 A B)). Qed.
Lemma lem4330320 {A B : Type'} (h1 : term35 A B) : term35 A B.
Proof. exact (h1). Qed.
Lemma lem4330321 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (@lem3596285 A). Qed.
Lemma lem4330322 {B : Type'} : @FINITE B (@EMPTY B).
Proof. exact (@lem3596285 B). Qed.
Lemma lem4330327 {A B : Type'} (h1 : term36 A B) : term36 A B.
Proof. exact (h1). Qed.
Lemma lem4330328 {A B : Type'} : term37 A B.
Proof. exact (fun h0 : term36 A B => @lem4330327 A B h0). Qed.
Lemma lem4330329 {A B : Type'} (h1 : term37 A B) : term37 A B.
Proof. exact (h1). Qed.
Lemma lem4330330 {A B : Type'} (h1 : term36 A B) : term36 A B.
Proof. exact (h1). Qed.
Lemma lem4330331 {A B : Type'} (h1 : term36 A B) (h2 : term37 A B) : term36 A B.
Proof. exact (@lem4330329 A B h2 (@lem4330330 A B h1)). Qed.
Lemma lem4330332 {A B : Type'} (h1 : term36 A B) : term38 A B.
Proof. exact (fun h0 : term37 A B => @lem4330331 A B h1 h0). Qed.
Lemma lem4330333 {A B : Type'} (h1 : term37 A B) : term37 A B.
Proof. exact (h1). Qed.
Lemma lem4330334 {A B : Type'} (h1 : term36 A B) (h2 : term37 A B) : term36 A B.
Proof. exact (@lem4330332 A B h1 (@lem4330333 A B h2)). Qed.
Lemma lem4330335 {A B : Type'} (h1 : term37 A B) : term37 A B.
Proof. exact (fun h0 : term36 A B => @lem4330334 A B h0 h1). Qed.
Lemma lem4330336 {A B : Type'} : term39 A B.
Proof. exact (fun h0 : term37 A B => @lem4330335 A B h0). Qed.
Lemma lem4330339 {A B : Type'} : term37 A B.
Proof. exact (@lem4330336 A B (@lem4330328 A B)). Qed.
Lemma lem4330340 {A B : Type'} : term37 A B.
Proof. exact (@lem4330339 A B). Qed.
Lemma lem4330366 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4330367 {B : Type'} : (term40 B) = (term41 B).
Proof. exact (@lem4330366 (@FINITE B (@EMPTY B))). Qed.
Lemma lem4330368 {A : Type'} : (term42 A) = (term42 A).
Proof. exact (eq_refl (term42 A)). Qed.
Lemma lem4330369 {A B : Type'} : (term43 A B) = (term44 A B).
Proof. exact (MK_COMB (@lem4330368 A) (@lem4330367 B)). Qed.
Lemma lem4330372 {A B : Type'} : (term45 A B) = (term45 A B).
Proof. exact (eq_refl (term45 A B)). Qed.
Lemma lem4330379 {A B : Type'} : (term36 A B) = (term46 A B).
Proof. exact (MK_COMB (@lem4330372 A B) (@lem4330369 A B)). Qed.
Lemma lem4330386 {A B : Type'} : (term44 A B) = (term44 A B).
Proof. exact (eq_refl (term44 A B)). Qed.
Lemma lem4330425 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : ((term10 A B s t) = (term24 A B s t)) = ((term10 A B s t) = (term24 A B s t)).
Proof. exact (eq_refl ((term10 A B s t) = (term24 A B s t))). Qed.
Lemma lem4330426 {A B : Type'} (s : A -> Prop) : (term26 A B s) = (term26 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4330425 A B s t)). Qed.
Lemma lem4330427 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4330428 {A B : Type'} (s : A -> Prop) : (term28 A B s) = (term28 A B s).
Proof. exact (MK_COMB (@lem4330427 B) (@lem4330426 A B s)). Qed.
Lemma lem4330429 {A B : Type'} : (term30 A B) = (term30 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4330428 A B s)). Qed.
Lemma lem4330430 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4330431 {A B : Type'} : (term32 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem4330430 A) (@lem4330429 A B)). Qed.
Lemma lem4330432 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4330433 {A B : Type'} : (term35 A B) = (term35 A B).
Proof. exact (MK_COMB (@lem4330432) (@lem4330431 A B)). Qed.
Lemma lem4330434 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4330435 {A B : Type'} : (term45 A B) = (term45 A B).
Proof. exact (MK_COMB (@lem4330434) (@lem4330433 A B)). Qed.
Lemma lem4330436 {A B : Type'} : (term46 A B) = (term46 A B).
Proof. exact (MK_COMB (@lem4330435 A B) (@lem4330386 A B)). Qed.
Lemma lem4330467 {A B : Type'} : (term36 A B) = (term46 A B).
Proof. exact (TRANS (@lem4330379 A B) (@lem4330436 A B)). Qed.
Lemma lem4330468 {A B : Type'} : (term46 A B) = (term36 A B).
Proof. exact (SYM (@lem4330467 A B)). Qed.
Lemma lem4330469 {A B : Type'} (h1 : term35 A B) : term35 A B.
Proof. exact (h1). Qed.
Lemma lem4330484 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term47 A B s t) = (term48 A B s t).
Proof. exact (@lem17045 (@FINITE A s) (@FINITE B t)). Qed.
Lemma lem4330489 {B : Type'} (t : B -> Prop) : (term13 B t) = (term13 B t).
Proof. exact (eq_refl (term13 B t)). Qed.
Lemma lem4330490 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term49 A B s t) = (term50 A B s t).
Proof. exact (MK_COMB (@lem4330489 B t) (@lem4330484 A B s t)). Qed.
Lemma lem4330491 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term51 A B s t) = (term49 A B s t).
Proof. exact (@lem17160 (t = (@EMPTY B)) (term52 A B s t)). Qed.
Lemma lem4330492 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term51 A B s t) = (term50 A B s t).
Proof. exact (TRANS (@lem4330491 A B s t) (@lem4330490 A B s t)). Qed.
Lemma lem4330497 {A : Type'} (s : A -> Prop) : (term13 A s) = (term13 A s).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem4330498 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term53 A B s t) = (term54 A B s t).
Proof. exact (MK_COMB (@lem4330497 A s) (@lem4330492 A B s t)). Qed.
Lemma lem4330499 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term10 A B s t) = (term53 A B s t).
Proof. exact (@lem17160 (s = (@EMPTY A)) (term55 A B s t)). Qed.
Lemma lem4330500 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term10 A B s t) = (term54 A B s t).
Proof. exact (TRANS (@lem4330499 A B s t) (@lem4330498 A B s t)). Qed.
Lemma lem4330505 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term56 A B s t) = (term4 A B s t).
Proof. exact (@lem16933 (term4 A B s t)). Qed.
Lemma lem4330509 {A : Type'} (s : A -> Prop) : (term57 A s) = (s = (@EMPTY A)).
Proof. exact (@lem16933 (s = (@EMPTY A))). Qed.
Lemma lem4330513 {B : Type'} (t : B -> Prop) : (term58 B t) = (@FINITE B t).
Proof. exact (@lem16933 (@FINITE B t)). Qed.
Lemma lem4330514 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4330515 {A : Type'} (s : A -> Prop) : (term59 A s) = (term60 A s).
Proof. exact (MK_COMB (@lem4330514) (@lem4330509 A s)). Qed.
Lemma lem4330516 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term61 A B s t) = (term62 A B s t).
Proof. exact (MK_COMB (@lem4330515 A s) (@lem4330513 B t)). Qed.
Lemma lem4330517 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term63 A B s t) = (term61 A B s t).
Proof. exact (@lem17045 (term20 A s) (term6 B t)). Qed.
Lemma lem4330518 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term63 A B s t) = (term62 A B s t).
Proof. exact (TRANS (@lem4330517 A B s t) (@lem4330516 A B s t)). Qed.
Lemma lem4330525 {A : Type'} (s : A -> Prop) : (term58 A s) = (@FINITE A s).
Proof. exact (@lem16933 (@FINITE A s)). Qed.
Lemma lem4330529 {B : Type'} (t : B -> Prop) : (term57 B t) = (t = (@EMPTY B)).
Proof. exact (@lem16933 (t = (@EMPTY B))). Qed.
Lemma lem4330530 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4330531 {A : Type'} (s : A -> Prop) : (term64 A s) = (term65 A s).
Proof. exact (MK_COMB (@lem4330530) (@lem4330525 A s)). Qed.
Lemma lem4330532 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term66 A B s t) = (term67 A B s t).
Proof. exact (MK_COMB (@lem4330531 A s) (@lem4330529 B t)). Qed.
Lemma lem4330533 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term68 A B s t) = (term66 A B s t).
Proof. exact (@lem17045 (term6 A s) (term20 B t)). Qed.
Lemma lem4330534 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term68 A B s t) = (term67 A B s t).
Proof. exact (TRANS (@lem4330533 A B s t) (@lem4330532 A B s t)). Qed.
Lemma lem4330538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4330539 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term69 A B s t) = (term70 A B s t).
Proof. exact (MK_COMB (@lem4330538) (@lem4330518 A B s t)). Qed.
Lemma lem4330540 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term71 A B s t) = (term72 A B s t).
Proof. exact (MK_COMB (@lem4330539 A B s t) (@lem4330534 A B s t)). Qed.
Lemma lem4330541 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term73 A B s t) = (term71 A B s t).
Proof. exact (@lem17160 (term15 A B s t) (term22 A B s t)). Qed.
Lemma lem4330542 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term73 A B s t) = (term72 A B s t).
Proof. exact (TRANS (@lem4330541 A B s t) (@lem4330540 A B s t)). Qed.
Lemma lem4330545 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term24 A B s t) = (term24 A B s t).
Proof. exact (eq_refl (term24 A B s t)). Qed.
Lemma lem4330546 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4330547 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term74 A B s t) = (term75 A B s t).
Proof. exact (MK_COMB (@lem4330546) (@lem4330505 A B s t)). Qed.
Lemma lem4330548 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term76 A B s t) = (term77 A B s t).
Proof. exact (MK_COMB (@lem4330547 A B s t) (@lem4330545 A B s t)). Qed.
Lemma lem4330549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4330550 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term78 A B s t) = (term79 A B s t).
Proof. exact (MK_COMB (@lem4330549) (@lem4330500 A B s t)). Qed.
Lemma lem4330551 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term80 A B s t) = (term81 A B s t).
Proof. exact (MK_COMB (@lem4330550 A B s t) (@lem4330542 A B s t)). Qed.
Lemma lem4330552 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4330553 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term82 A B s t) = (term83 A B s t).
Proof. exact (MK_COMB (@lem4330552) (@lem4330551 A B s t)). Qed.
Lemma lem4330554 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term84 A B s t) = (term85 A B s t).
Proof. exact (MK_COMB (@lem4330553 A B s t) (@lem4330548 A B s t)). Qed.
Lemma lem4330555 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term86 A B s t) = (term84 A B s t).
Proof. exact (@lem17646 (term10 A B s t) (term24 A B s t)). Qed.
Lemma lem4330556 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term86 A B s t) = (term85 A B s t).
Proof. exact (TRANS (@lem4330555 A B s t) (@lem4330554 A B s t)). Qed.
Lemma lem4330557 {B : Type'} (P : type686 B) : (term87 B P) = (term88 B P).
Proof. exact (@lem18392 (B -> Prop) P). Qed.
Lemma lem4330558 {A B : Type'} (s : A -> Prop) : (term89 A B s) = (term90 A B s).
Proof. exact (@lem4330557 B (term26 A B s)). Qed.
Lemma lem4330559 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term91 A B s t) = ((term10 A B s t) = (term24 A B s t)).
Proof. exact (eq_refl (term91 A B s t)). Qed.
Lemma lem4330560 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4330561 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term92 A B s t) = (term86 A B s t).
Proof. exact (MK_COMB (@lem4330560) (@lem4330559 A B s t)). Qed.
Lemma lem4330562 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term92 A B s t) = (term85 A B s t).
Proof. exact (TRANS (@lem4330561 A B s t) (@lem4330556 A B s t)). Qed.
Lemma lem4330563 {A B : Type'} (s : A -> Prop) : (term93 A B s) = (term94 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4330562 A B s t)). Qed.
Lemma lem4330564 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem4330565 {A B : Type'} (s : A -> Prop) : (term90 A B s) = (term95 A B s).
Proof. exact (MK_COMB (@lem4330564 B) (@lem4330563 A B s)). Qed.
Lemma lem4330566 {A B : Type'} (s : A -> Prop) : (term89 A B s) = (term95 A B s).
Proof. exact (TRANS (@lem4330558 A B s) (@lem4330565 A B s)). Qed.
Lemma lem4330567 {A : Type'} (P : type686 A) : (term87 A P) = (term88 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4330568 {A B : Type'} : (term35 A B) = (term96 A B).
Proof. exact (@lem4330567 A (term30 A B)). Qed.
Lemma lem4330569 {A B : Type'} (s : A -> Prop) : (term97 A B s) = (term28 A B s).
Proof. exact (eq_refl (term97 A B s)). Qed.
Lemma lem4330570 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4330571 {A B : Type'} (s : A -> Prop) : (term98 A B s) = (term89 A B s).
Proof. exact (MK_COMB (@lem4330570) (@lem4330569 A B s)). Qed.
Lemma lem4330572 {A B : Type'} (s : A -> Prop) : (term98 A B s) = (term95 A B s).
Proof. exact (TRANS (@lem4330571 A B s) (@lem4330566 A B s)). Qed.
Lemma lem4330573 {A B : Type'} : (term99 A B) = (term100 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4330572 A B s)). Qed.
Lemma lem4330574 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4330575 {A B : Type'} : (term96 A B) = (term101 A B).
Proof. exact (MK_COMB (@lem4330574 A) (@lem4330573 A B)). Qed.
Lemma lem4330576 {A B : Type'} : (term35 A B) = (term101 A B).
Proof. exact (TRANS (@lem4330568 A B) (@lem4330575 A B)). Qed.
Lemma lem4330582 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4330583 {B : Type'} (P : type686 B) (Q : type686 B) : (term104 B P Q) = (term105 B P Q).
Proof. exact (@lem4330582 (B -> Prop) P Q). Qed.
Lemma lem4330584 {A B : Type'} (s : A -> Prop) : (term106 A B s) = (term107 A B s).
Proof. exact (@lem4330583 B (term108 A B s) (term109 A B s)). Qed.
Lemma lem4330585 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term110 A B s t) = (term81 A B s t).
Proof. exact (eq_refl (term110 A B s t)). Qed.
Lemma lem4330586 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4330587 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term111 A B s t) = (term83 A B s t).
Proof. exact (MK_COMB (@lem4330586) (@lem4330585 A B s t)). Qed.
Lemma lem4330588 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term112 A B s t) = (term77 A B s t).
Proof. exact (eq_refl (term112 A B s t)). Qed.
Lemma lem4330589 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term113 A B s t) = (term85 A B s t).
Proof. exact (MK_COMB (@lem4330587 A B s t) (@lem4330588 A B s t)). Qed.
Lemma lem4330590 {A B : Type'} (s : A -> Prop) : (term114 A B s) = (term94 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4330589 A B s t)). Qed.
Lemma lem4330591 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem4330592 {A B : Type'} (s : A -> Prop) : (term106 A B s) = (term95 A B s).
Proof. exact (MK_COMB (@lem4330591 B) (@lem4330590 A B s)). Qed.
Lemma lem4330593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4330594 {A B : Type'} (s : A -> Prop) : (term115 A B s) = (term116 A B s).
Proof. exact (MK_COMB (@lem4330593) (@lem4330592 A B s)). Qed.
Lemma lem4330595 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term110 A B s t) = (term81 A B s t).
Proof. exact (eq_refl (term110 A B s t)). Qed.
Lemma lem4330596 {A B : Type'} (s : A -> Prop) : (term117 A B s) = (term108 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4330595 A B s t)). Qed.
Lemma lem4330597 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem4330598 {A B : Type'} (s : A -> Prop) : (term118 A B s) = (term119 A B s).
Proof. exact (MK_COMB (@lem4330597 B) (@lem4330596 A B s)). Qed.
Lemma lem4330599 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4330600 {A B : Type'} (s : A -> Prop) : (term120 A B s) = (term121 A B s).
Proof. exact (MK_COMB (@lem4330599) (@lem4330598 A B s)). Qed.
Lemma lem4330601 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term112 A B s t) = (term77 A B s t).
Proof. exact (eq_refl (term112 A B s t)). Qed.
Lemma lem4330602 {A B : Type'} (s : A -> Prop) : (term122 A B s) = (term109 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4330601 A B s t)). Qed.
Lemma lem4330603 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem4330604 {A B : Type'} (s : A -> Prop) : (term123 A B s) = (term124 A B s).
Proof. exact (MK_COMB (@lem4330603 B) (@lem4330602 A B s)). Qed.
Lemma lem4330605 {A B : Type'} (s : A -> Prop) : (term107 A B s) = (term125 A B s).
Proof. exact (MK_COMB (@lem4330600 A B s) (@lem4330604 A B s)). Qed.
Lemma lem4330606 {A B : Type'} (s : A -> Prop) : ((term106 A B s) = (term107 A B s)) = ((term95 A B s) = (term125 A B s)).
Proof. exact (MK_COMB (@lem4330594 A B s) (@lem4330605 A B s)). Qed.
Lemma lem4330607 {A B : Type'} (s : A -> Prop) : (term95 A B s) = (term125 A B s).
Proof. exact (EQ_MP (@lem4330606 A B s) (@lem4330584 A B s)). Qed.
Lemma lem4330704 {A B : Type'} : (term100 A B) = (term126 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4330607 A B s)). Qed.
Lemma lem4330705 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4330706 {A B : Type'} : (term101 A B) = (term127 A B).
Proof. exact (MK_COMB (@lem4330705 A) (@lem4330704 A B)). Qed.
Lemma lem4330708 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4330709 {A : Type'} (P : type686 A) (Q : type686 A) : (term104 A P Q) = (term105 A P Q).
Proof. exact (@lem4330708 (A -> Prop) P Q). Qed.
Lemma lem4330710 {A B : Type'} : (term128 A B) = (term129 A B).
Proof. exact (@lem4330709 A (term130 A B) (term131 A B)). Qed.
Lemma lem4330711 {A B : Type'} (s : A -> Prop) : (term132 A B s) = (term119 A B s).
Proof. exact (eq_refl (term132 A B s)). Qed.
Lemma lem4330712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4330713 {A B : Type'} (s : A -> Prop) : (term133 A B s) = (term121 A B s).
Proof. exact (MK_COMB (@lem4330712) (@lem4330711 A B s)). Qed.
Lemma lem4330714 {A B : Type'} (s : A -> Prop) : (term134 A B s) = (term124 A B s).
Proof. exact (eq_refl (term134 A B s)). Qed.
Lemma lem4330715 {A B : Type'} (s : A -> Prop) : (term135 A B s) = (term125 A B s).
Proof. exact (MK_COMB (@lem4330713 A B s) (@lem4330714 A B s)). Qed.
Lemma lem4330716 {A B : Type'} : (term136 A B) = (term126 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4330715 A B s)). Qed.
Lemma lem4330717 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4330718 {A B : Type'} : (term128 A B) = (term127 A B).
Proof. exact (MK_COMB (@lem4330717 A) (@lem4330716 A B)). Qed.
Lemma lem4330719 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4330720 {A B : Type'} : (term137 A B) = (term138 A B).
Proof. exact (MK_COMB (@lem4330719) (@lem4330718 A B)). Qed.
Lemma lem4330721 {A B : Type'} (s : A -> Prop) : (term132 A B s) = (term119 A B s).
Proof. exact (eq_refl (term132 A B s)). Qed.
Lemma lem4330722 {A B : Type'} : (term139 A B) = (term130 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4330721 A B s)). Qed.
Lemma lem4330723 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4330724 {A B : Type'} : (term140 A B) = (term141 A B).
Proof. exact (MK_COMB (@lem4330723 A) (@lem4330722 A B)). Qed.
Lemma lem4330725 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4330726 {A B : Type'} : (term142 A B) = (term143 A B).
Proof. exact (MK_COMB (@lem4330725) (@lem4330724 A B)). Qed.
Lemma lem4330727 {A B : Type'} (s : A -> Prop) : (term134 A B s) = (term124 A B s).
Proof. exact (eq_refl (term134 A B s)). Qed.
Lemma lem4330728 {A B : Type'} : (term144 A B) = (term131 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4330727 A B s)). Qed.
Lemma lem4330729 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4330730 {A B : Type'} : (term145 A B) = (term146 A B).
Proof. exact (MK_COMB (@lem4330729 A) (@lem4330728 A B)). Qed.
Lemma lem4330731 {A B : Type'} : (term129 A B) = (term147 A B).
Proof. exact (MK_COMB (@lem4330726 A B) (@lem4330730 A B)). Qed.
Lemma lem4330732 {A B : Type'} : ((term128 A B) = (term129 A B)) = ((term127 A B) = (term147 A B)).
Proof. exact (MK_COMB (@lem4330720 A B) (@lem4330731 A B)). Qed.
Lemma lem4330733 {A B : Type'} : (term127 A B) = (term147 A B).
Proof. exact (EQ_MP (@lem4330732 A B) (@lem4330710 A B)). Qed.
Lemma lem4330838 {A B : Type'} : (term101 A B) = (term147 A B).
Proof. exact (TRANS (@lem4330706 A B) (@lem4330733 A B)). Qed.
Lemma lem4330840 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4330841 {A : Type'} (P : type686 A) (Q : type686 A) : (term105 A P Q) = (term104 A P Q).
Proof. exact (@lem4330840 (A -> Prop) P Q). Qed.
Lemma lem4330842 {A B : Type'} : (term129 A B) = (term128 A B).
Proof. exact (@lem4330841 A (term130 A B) (term131 A B)). Qed.
Lemma lem4330843 {A B : Type'} (s : A -> Prop) : (term132 A B s) = (term119 A B s).
Proof. exact (eq_refl (term132 A B s)). Qed.
Lemma lem4330844 {A B : Type'} : (term139 A B) = (term130 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4330843 A B s)). Qed.
Lemma lem4330845 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4330846 {A B : Type'} : (term140 A B) = (term141 A B).
Proof. exact (MK_COMB (@lem4330845 A) (@lem4330844 A B)). Qed.
Lemma lem4330847 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4330848 {A B : Type'} : (term142 A B) = (term143 A B).
Proof. exact (MK_COMB (@lem4330847) (@lem4330846 A B)). Qed.
Lemma lem4330849 {A B : Type'} (s : A -> Prop) : (term134 A B s) = (term124 A B s).
Proof. exact (eq_refl (term134 A B s)). Qed.
Lemma lem4330850 {A B : Type'} : (term144 A B) = (term131 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4330849 A B s)). Qed.
Lemma lem4330851 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4330852 {A B : Type'} : (term145 A B) = (term146 A B).
Proof. exact (MK_COMB (@lem4330851 A) (@lem4330850 A B)). Qed.
Lemma lem4330853 {A B : Type'} : (term129 A B) = (term147 A B).
Proof. exact (MK_COMB (@lem4330848 A B) (@lem4330852 A B)). Qed.
Lemma lem4330854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4330855 {A B : Type'} : (term148 A B) = (term149 A B).
Proof. exact (MK_COMB (@lem4330854) (@lem4330853 A B)). Qed.
Lemma lem4330856 {A B : Type'} (s : A -> Prop) : (term132 A B s) = (term119 A B s).
Proof. exact (eq_refl (term132 A B s)). Qed.
Lemma lem4330857 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4330858 {A B : Type'} (s : A -> Prop) : (term133 A B s) = (term121 A B s).
Proof. exact (MK_COMB (@lem4330857) (@lem4330856 A B s)). Qed.
Lemma lem4330859 {A B : Type'} (s : A -> Prop) : (term134 A B s) = (term124 A B s).
Proof. exact (eq_refl (term134 A B s)). Qed.
Lemma lem4330860 {A B : Type'} (s : A -> Prop) : (term135 A B s) = (term125 A B s).
Proof. exact (MK_COMB (@lem4330858 A B s) (@lem4330859 A B s)). Qed.
Lemma lem4330861 {A B : Type'} : (term136 A B) = (term126 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4330860 A B s)). Qed.
Lemma lem4330862 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4330863 {A B : Type'} : (term128 A B) = (term127 A B).
Proof. exact (MK_COMB (@lem4330862 A) (@lem4330861 A B)). Qed.
Lemma lem4330864 {A B : Type'} : ((term129 A B) = (term128 A B)) = ((term147 A B) = (term127 A B)).
Proof. exact (MK_COMB (@lem4330855 A B) (@lem4330863 A B)). Qed.
Lemma lem4330865 {A B : Type'} : (term147 A B) = (term127 A B).
Proof. exact (EQ_MP (@lem4330864 A B) (@lem4330842 A B)). Qed.
Lemma lem4330867 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4330868 {B : Type'} (P : type686 B) (Q : type686 B) : (term105 B P Q) = (term104 B P Q).
Proof. exact (@lem4330867 (B -> Prop) P Q). Qed.
Lemma lem4330869 {A B : Type'} (s : A -> Prop) : (term107 A B s) = (term106 A B s).
Proof. exact (@lem4330868 B (term108 A B s) (term109 A B s)). Qed.
Lemma lem4330870 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term110 A B s t) = (term81 A B s t).
Proof. exact (eq_refl (term110 A B s t)). Qed.
Lemma lem4330871 {A B : Type'} (s : A -> Prop) : (term117 A B s) = (term108 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4330870 A B s t)). Qed.
Lemma lem4330872 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem4330873 {A B : Type'} (s : A -> Prop) : (term118 A B s) = (term119 A B s).
Proof. exact (MK_COMB (@lem4330872 B) (@lem4330871 A B s)). Qed.
Lemma lem4330874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4330875 {A B : Type'} (s : A -> Prop) : (term120 A B s) = (term121 A B s).
Proof. exact (MK_COMB (@lem4330874) (@lem4330873 A B s)). Qed.
Lemma lem4330876 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term112 A B s t) = (term77 A B s t).
Proof. exact (eq_refl (term112 A B s t)). Qed.
Lemma lem4330877 {A B : Type'} (s : A -> Prop) : (term122 A B s) = (term109 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4330876 A B s t)). Qed.
Lemma lem4330878 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem4330879 {A B : Type'} (s : A -> Prop) : (term123 A B s) = (term124 A B s).
Proof. exact (MK_COMB (@lem4330878 B) (@lem4330877 A B s)). Qed.
Lemma lem4330880 {A B : Type'} (s : A -> Prop) : (term107 A B s) = (term125 A B s).
Proof. exact (MK_COMB (@lem4330875 A B s) (@lem4330879 A B s)). Qed.
Lemma lem4330881 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4330882 {A B : Type'} (s : A -> Prop) : (term150 A B s) = (term151 A B s).
Proof. exact (MK_COMB (@lem4330881) (@lem4330880 A B s)). Qed.
Lemma lem4330883 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term110 A B s t) = (term81 A B s t).
Proof. exact (eq_refl (term110 A B s t)). Qed.
Lemma lem4330884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4330885 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term111 A B s t) = (term83 A B s t).
Proof. exact (MK_COMB (@lem4330884) (@lem4330883 A B s t)). Qed.
Lemma lem4330886 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term112 A B s t) = (term77 A B s t).
Proof. exact (eq_refl (term112 A B s t)). Qed.
Lemma lem4330887 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term113 A B s t) = (term85 A B s t).
Proof. exact (MK_COMB (@lem4330885 A B s t) (@lem4330886 A B s t)). Qed.
Lemma lem4330888 {A B : Type'} (s : A -> Prop) : (term114 A B s) = (term94 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4330887 A B s t)). Qed.
Lemma lem4330889 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem4330890 {A B : Type'} (s : A -> Prop) : (term106 A B s) = (term95 A B s).
Proof. exact (MK_COMB (@lem4330889 B) (@lem4330888 A B s)). Qed.
Lemma lem4330891 {A B : Type'} (s : A -> Prop) : ((term107 A B s) = (term106 A B s)) = ((term125 A B s) = (term95 A B s)).
Proof. exact (MK_COMB (@lem4330882 A B s) (@lem4330890 A B s)). Qed.
Lemma lem4330892 {A B : Type'} (s : A -> Prop) : (term125 A B s) = (term95 A B s).
Proof. exact (EQ_MP (@lem4330891 A B s) (@lem4330869 A B s)). Qed.
Lemma lem4330893 {A B : Type'} : (term126 A B) = (term100 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4330892 A B s)). Qed.
Lemma lem4330894 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4330895 {A B : Type'} : (term127 A B) = (term101 A B).
Proof. exact (MK_COMB (@lem4330894 A) (@lem4330893 A B)). Qed.
Lemma lem4330896 {A B : Type'} : (term147 A B) = (term101 A B).
Proof. exact (TRANS (@lem4330865 A B) (@lem4330895 A B)). Qed.
Lemma lem4330897 {A B : Type'} : (term101 A B) = (term101 A B).
Proof. exact (TRANS (@lem4330838 A B) (@lem4330896 A B)). Qed.
Lemma lem4330898 {A B : Type'} : (term35 A B) = (term101 A B).
Proof. exact (TRANS (@lem4330576 A B) (@lem4330897 A B)). Qed.
Lemma lem4330899 {A B : Type'} (h1 : term35 A B) : term101 A B.
Proof. exact (EQ_MP (@lem4330898 A B) (@lem4330469 A B h1)). Qed.
Lemma lem4330905 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4330911 {B : Type'} (h1 : @FINITE B (@EMPTY B)) : @FINITE B (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4330912 {A B : Type'} (s : A -> Prop) (h1 : term95 A B s) : term95 A B s.
Proof. exact (h1). Qed.
Lemma lem4330917 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4330921 {B : Type'} (h1 : @FINITE B (@EMPTY B)) : @FINITE B (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4331047 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term85 A B s t) : term85 A B s t.
Proof. exact (h1). Qed.
Lemma lem4331048 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) : term81 A B s t.
Proof. exact (h1). Qed.
Lemma lem4331049 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term77 A B s t) : term77 A B s t.
Proof. exact (h1). Qed.
Lemma lem4331050 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) : term72 A B s t.
Proof. exact (proj2 (@lem4331048 A B s t h1)). Qed.
Lemma lem4331051 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) : term54 A B s t.
Proof. exact (proj1 (@lem4331048 A B s t h1)). Qed.
Lemma lem4331052 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) : term67 A B s t.
Proof. exact (proj2 (@lem4331050 A B s t h1)). Qed.
Lemma lem4331053 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) : term62 A B s t.
Proof. exact (proj1 (@lem4331050 A B s t h1)). Qed.
Lemma lem4331054 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) : term50 A B s t.
Proof. exact (proj2 (@lem4331051 A B s t h1)). Qed.
Lemma lem4331056 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) : term48 A B s t.
Proof. exact (proj2 (@lem4331054 A B s t h1)). Qed.
Lemma lem4331072 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term77 A B s t) : term24 A B s t.
Proof. exact (proj2 (@lem4331049 A B s t h1)). Qed.
Lemma lem4331073 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term77 A B s t) : term4 A B s t.
Proof. exact (proj1 (@lem4331049 A B s t h1)). Qed.
Lemma lem4331074 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term15 A B s t.
Proof. exact (h1). Qed.
Lemma lem4331075 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) : term22 A B s t.
Proof. exact (h1). Qed.
Lemma lem4331079 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : term55 A B s t.
Proof. exact (h1). Qed.
Lemma lem4331081 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term52 A B s t) : term52 A B s t.
Proof. exact (h1). Qed.
Lemma lem4331087 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : term55 A B s t.
Proof. exact (h1). Qed.
Lemma lem4331089 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term52 A B s t) : term52 A B s t.
Proof. exact (h1). Qed.
Lemma lem4331111 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : term6 A s.
Proof. exact (h1). Qed.
Lemma lem4331115 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4331119 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331139 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : term6 A s.
Proof. exact (h1). Qed.
Lemma lem4331143 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4331151 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331167 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : term6 A s.
Proof. exact (h1). Qed.
Lemma lem4331175 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331199 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4331231 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331251 {B : Type'} (t : B -> Prop) (h1 : term6 B t) : term6 B t.
Proof. exact (h1). Qed.
Lemma lem4331259 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem4331267 {B : Type'} (h1 : @FINITE B (@EMPTY B)) : @FINITE B (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4331279 {B : Type'} (t : B -> Prop) (h1 : term6 B t) : term6 B t.
Proof. exact (h1). Qed.
Lemma lem4331283 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4331307 {B : Type'} (t : B -> Prop) (h1 : term6 B t) : term6 B t.
Proof. exact (h1). Qed.
Lemma lem4331311 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4331315 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem4331335 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331343 {B : Type'} (h1 : @FINITE B (@EMPTY B)) : @FINITE B (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4331355 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4331383 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331399 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331419 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4331453 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : term6 A s.
Proof. exact (h1). Qed.
Lemma lem4331455 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4331457 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331467 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : term6 A s.
Proof. exact (h1). Qed.
Lemma lem4331469 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4331473 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331481 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : term6 A s.
Proof. exact (h1). Qed.
Lemma lem4331485 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331493 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) : term20 B t.
Proof. exact (proj1 (@lem4331054 A B s t h1)). Qed.
Lemma lem4331497 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4331505 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) : term20 A s.
Proof. exact (proj1 (@lem4331051 A B s t h1)). Qed.
Lemma lem4331513 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331523 {B : Type'} (t : B -> Prop) (h1 : term6 B t) : term6 B t.
Proof. exact (h1). Qed.
Lemma lem4331527 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem4331531 {B : Type'} (h1 : @FINITE B (@EMPTY B)) : @FINITE B (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4331537 {B : Type'} (t : B -> Prop) (h1 : term6 B t) : term6 B t.
Proof. exact (h1). Qed.
Lemma lem4331539 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4331551 {B : Type'} (t : B -> Prop) (h1 : term6 B t) : term6 B t.
Proof. exact (h1). Qed.
Lemma lem4331553 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4331555 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem4331561 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term20 A s.
Proof. exact (proj1 (@lem4331074 A B s t h1)). Qed.
Lemma lem4331565 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331569 {B : Type'} (h1 : @FINITE B (@EMPTY B)) : @FINITE B (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4331573 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term6 B t.
Proof. exact (proj2 (@lem4331074 A B s t h1)). Qed.
Lemma lem4331575 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4331583 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term6 B t.
Proof. exact (proj2 (@lem4331074 A B s t h1)). Qed.
Lemma lem4331589 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331593 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) : term6 A s.
Proof. exact (proj1 (@lem4331075 A B s t h1)). Qed.
Lemma lem4331597 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331605 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) : term20 B t.
Proof. exact (proj2 (@lem4331075 A B s t h1)). Qed.
Lemma lem4331607 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4331613 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) : term6 A s.
Proof. exact (proj1 (@lem4331075 A B s t h1)). Qed.
Lemma lem4331689 {A : Type'} : (term152 A) = (term152 A).
Proof. exact (eq_refl (term152 A)). Qed.
Lemma lem4331690 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term153 A s) = (term154 A).
Proof. exact (MK_COMB (@lem4331689 A) (@lem4331457 A s h1)). Qed.
Lemma lem4331691 {A : Type'} : (term154 A) = (term41 A).
Proof. exact (eq_refl (term154 A)). Qed.
Lemma lem4331692 {A : Type'} (s : A -> Prop) : (term155 A s) = (term155 A s).
Proof. exact (eq_refl (term155 A s)). Qed.
Lemma lem4331693 {A : Type'} (s : A -> Prop) : ((term153 A s) = (term154 A)) = ((term153 A s) = (term41 A)).
Proof. exact (MK_COMB (@lem4331692 A s) (@lem4331691 A)). Qed.
Lemma lem4331694 {A : Type'} (s : A -> Prop) : (term153 A s) = (term6 A s).
Proof. exact (eq_refl (term153 A s)). Qed.
Lemma lem4331695 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4331696 {A : Type'} (s : A -> Prop) : (term155 A s) = (term156 A s).
Proof. exact (MK_COMB (@lem4331695) (@lem4331694 A s)). Qed.
Lemma lem4331697 {A : Type'} : (term41 A) = (term41 A).
Proof. exact (eq_refl (term41 A)). Qed.
Lemma lem4331698 {A : Type'} (s : A -> Prop) : ((term153 A s) = (term41 A)) = ((term6 A s) = (term41 A)).
Proof. exact (MK_COMB (@lem4331696 A s) (@lem4331697 A)). Qed.
Lemma lem4331699 {A : Type'} (s : A -> Prop) : ((term153 A s) = (term154 A)) = ((term6 A s) = (term41 A)).
Proof. exact (TRANS (@lem4331693 A s) (@lem4331698 A s)). Qed.
Lemma lem4331700 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term6 A s) = (term41 A).
Proof. exact (EQ_MP (@lem4331699 A s) (@lem4331690 A s h1)). Qed.
Lemma lem4331701 {A : Type'} (s : A -> Prop) (h1 : term6 A s) (h2 : s = (@EMPTY A)) : term41 A.
Proof. exact (EQ_MP (@lem4331700 A s h2) (@lem4331453 A s h1)). Qed.
Lemma lem4331702 {A : Type'} : (term157 A) = (term157 A).
Proof. exact (eq_refl (term157 A)). Qed.
Lemma lem4331703 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term158 A s) = (term159 A).
Proof. exact (MK_COMB (@lem4331702 A) (@lem4331457 A s h1)). Qed.
Lemma lem4331704 {A : Type'} : (term159 A) = (@FINITE A (@EMPTY A)).
Proof. exact (eq_refl (term159 A)). Qed.
Lemma lem4331705 {A : Type'} (s : A -> Prop) : (term160 A s) = (term160 A s).
Proof. exact (eq_refl (term160 A s)). Qed.
Lemma lem4331706 {A : Type'} (s : A -> Prop) : ((term158 A s) = (term159 A)) = ((term158 A s) = (@FINITE A (@EMPTY A))).
Proof. exact (MK_COMB (@lem4331705 A s) (@lem4331704 A)). Qed.
Lemma lem4331707 {A : Type'} (s : A -> Prop) : (term158 A s) = (@FINITE A s).
Proof. exact (eq_refl (term158 A s)). Qed.
Lemma lem4331708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4331709 {A : Type'} (s : A -> Prop) : (term160 A s) = (term161 A s).
Proof. exact (MK_COMB (@lem4331708) (@lem4331707 A s)). Qed.
Lemma lem4331710 {A : Type'} : (@FINITE A (@EMPTY A)) = (@FINITE A (@EMPTY A)).
Proof. exact (eq_refl (@FINITE A (@EMPTY A))). Qed.
Lemma lem4331711 {A : Type'} (s : A -> Prop) : ((term158 A s) = (@FINITE A (@EMPTY A))) = ((@FINITE A s) = (@FINITE A (@EMPTY A))).
Proof. exact (MK_COMB (@lem4331709 A s) (@lem4331710 A)). Qed.
Lemma lem4331712 {A : Type'} (s : A -> Prop) : ((term158 A s) = (term159 A)) = ((@FINITE A s) = (@FINITE A (@EMPTY A))).
Proof. exact (TRANS (@lem4331706 A s) (@lem4331711 A s)). Qed.
Lemma lem4331713 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@FINITE A s) = (@FINITE A (@EMPTY A)).
Proof. exact (EQ_MP (@lem4331712 A s) (@lem4331703 A s h1)). Qed.
Lemma lem4331742 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331784 {A : Type'} : (term152 A) = (term152 A).
Proof. exact (eq_refl (term152 A)). Qed.
Lemma lem4331785 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term153 A s) = (term154 A).
Proof. exact (MK_COMB (@lem4331784 A) (@lem4331485 A s h1)). Qed.
Lemma lem4331786 {A : Type'} : (term154 A) = (term41 A).
Proof. exact (eq_refl (term154 A)). Qed.
Lemma lem4331787 {A : Type'} (s : A -> Prop) : (term155 A s) = (term155 A s).
Proof. exact (eq_refl (term155 A s)). Qed.
Lemma lem4331788 {A : Type'} (s : A -> Prop) : ((term153 A s) = (term154 A)) = ((term153 A s) = (term41 A)).
Proof. exact (MK_COMB (@lem4331787 A s) (@lem4331786 A)). Qed.
Lemma lem4331789 {A : Type'} (s : A -> Prop) : (term153 A s) = (term6 A s).
Proof. exact (eq_refl (term153 A s)). Qed.
Lemma lem4331790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4331791 {A : Type'} (s : A -> Prop) : (term155 A s) = (term156 A s).
Proof. exact (MK_COMB (@lem4331790) (@lem4331789 A s)). Qed.
Lemma lem4331792 {A : Type'} : (term41 A) = (term41 A).
Proof. exact (eq_refl (term41 A)). Qed.
Lemma lem4331793 {A : Type'} (s : A -> Prop) : ((term153 A s) = (term41 A)) = ((term6 A s) = (term41 A)).
Proof. exact (MK_COMB (@lem4331791 A s) (@lem4331792 A)). Qed.
Lemma lem4331794 {A : Type'} (s : A -> Prop) : ((term153 A s) = (term154 A)) = ((term6 A s) = (term41 A)).
Proof. exact (TRANS (@lem4331788 A s) (@lem4331793 A s)). Qed.
Lemma lem4331795 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term6 A s) = (term41 A).
Proof. exact (EQ_MP (@lem4331794 A s) (@lem4331785 A s h1)). Qed.
Lemma lem4331838 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4331893 {A : Type'} (s : A -> Prop) (h1 : term6 A s) (h2 : s = (@EMPTY A)) : term41 A.
Proof. exact (EQ_MP (@lem4331795 A s h2) (@lem4331481 A s h1)). Qed.
Lemma lem4331950 {B : Type'} : (term162 B) = (term162 B).
Proof. exact (eq_refl (term162 B)). Qed.
Lemma lem4331951 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term163 B t) = (term164 B).
Proof. exact (MK_COMB (@lem4331950 B) (@lem4331497 B t h1)). Qed.
Lemma lem4331952 {B : Type'} : (term164 B) = (term165 B).
Proof. exact (eq_refl (term164 B)). Qed.
Lemma lem4331953 {B : Type'} (t : B -> Prop) : (term166 B t) = (term166 B t).
Proof. exact (eq_refl (term166 B t)). Qed.
Lemma lem4331954 {B : Type'} (t : B -> Prop) : ((term163 B t) = (term164 B)) = ((term163 B t) = (term165 B)).
Proof. exact (MK_COMB (@lem4331953 B t) (@lem4331952 B)). Qed.
Lemma lem4331955 {B : Type'} (t : B -> Prop) : (term163 B t) = (term20 B t).
Proof. exact (eq_refl (term163 B t)). Qed.
Lemma lem4331956 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4331957 {B : Type'} (t : B -> Prop) : (term166 B t) = (term167 B t).
Proof. exact (MK_COMB (@lem4331956) (@lem4331955 B t)). Qed.
Lemma lem4331958 {B : Type'} : (term165 B) = (term165 B).
Proof. exact (eq_refl (term165 B)). Qed.
Lemma lem4331959 {B : Type'} (t : B -> Prop) : ((term163 B t) = (term165 B)) = ((term20 B t) = (term165 B)).
Proof. exact (MK_COMB (@lem4331957 B t) (@lem4331958 B)). Qed.
Lemma lem4331960 {B : Type'} (t : B -> Prop) : ((term163 B t) = (term164 B)) = ((term20 B t) = (term165 B)).
Proof. exact (TRANS (@lem4331954 B t) (@lem4331959 B t)). Qed.
Lemma lem4331961 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term20 B t) = (term165 B).
Proof. exact (EQ_MP (@lem4331960 B t) (@lem4331951 B t h1)). Qed.
Lemma lem4331962 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) (h2 : t = (@EMPTY B)) : term165 B.
Proof. exact (EQ_MP (@lem4331961 B t h2) (@lem4331493 A B s t h1)). Qed.
Lemma lem4332032 {A : Type'} : (term162 A) = (term162 A).
Proof. exact (eq_refl (term162 A)). Qed.
Lemma lem4332033 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term163 A s) = (term164 A).
Proof. exact (MK_COMB (@lem4332032 A) (@lem4331513 A s h1)). Qed.
Lemma lem4332034 {A : Type'} : (term164 A) = (term165 A).
Proof. exact (eq_refl (term164 A)). Qed.
Lemma lem4332035 {A : Type'} (s : A -> Prop) : (term166 A s) = (term166 A s).
Proof. exact (eq_refl (term166 A s)). Qed.
Lemma lem4332036 {A : Type'} (s : A -> Prop) : ((term163 A s) = (term164 A)) = ((term163 A s) = (term165 A)).
Proof. exact (MK_COMB (@lem4332035 A s) (@lem4332034 A)). Qed.
Lemma lem4332037 {A : Type'} (s : A -> Prop) : (term163 A s) = (term20 A s).
Proof. exact (eq_refl (term163 A s)). Qed.
Lemma lem4332038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4332039 {A : Type'} (s : A -> Prop) : (term166 A s) = (term167 A s).
Proof. exact (MK_COMB (@lem4332038) (@lem4332037 A s)). Qed.
Lemma lem4332040 {A : Type'} : (term165 A) = (term165 A).
Proof. exact (eq_refl (term165 A)). Qed.
Lemma lem4332041 {A : Type'} (s : A -> Prop) : ((term163 A s) = (term165 A)) = ((term20 A s) = (term165 A)).
Proof. exact (MK_COMB (@lem4332039 A s) (@lem4332040 A)). Qed.
Lemma lem4332042 {A : Type'} (s : A -> Prop) : ((term163 A s) = (term164 A)) = ((term20 A s) = (term165 A)).
Proof. exact (TRANS (@lem4332036 A s) (@lem4332041 A s)). Qed.
Lemma lem4332043 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term20 A s) = (term165 A).
Proof. exact (EQ_MP (@lem4332042 A s) (@lem4332033 A s h1)). Qed.
Lemma lem4332044 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term81 A B s t) (h2 : s = (@EMPTY A)) : term165 A.
Proof. exact (EQ_MP (@lem4332043 A s h2) (@lem4331505 A B s t h1)). Qed.
Lemma lem4332127 {B : Type'} (h1 : @FINITE B (@EMPTY B)) : @FINITE B (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4332168 {B : Type'} (t : B -> Prop) (h1 : term6 B t) : term6 B t.
Proof. exact (h1). Qed.
Lemma lem4332182 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4332224 {B : Type'} (h1 : @FINITE B (@EMPTY B)) : @FINITE B (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4332252 {B : Type'} : (term152 B) = (term152 B).
Proof. exact (eq_refl (term152 B)). Qed.
Lemma lem4332253 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term153 B t) = (term154 B).
Proof. exact (MK_COMB (@lem4332252 B) (@lem4332182 B t h1)). Qed.
Lemma lem4332254 {B : Type'} : (term154 B) = (term41 B).
Proof. exact (eq_refl (term154 B)). Qed.
Lemma lem4332255 {B : Type'} (t : B -> Prop) : (term155 B t) = (term155 B t).
Proof. exact (eq_refl (term155 B t)). Qed.
Lemma lem4332256 {B : Type'} (t : B -> Prop) : ((term153 B t) = (term154 B)) = ((term153 B t) = (term41 B)).
Proof. exact (MK_COMB (@lem4332255 B t) (@lem4332254 B)). Qed.
Lemma lem4332257 {B : Type'} (t : B -> Prop) : (term153 B t) = (term6 B t).
Proof. exact (eq_refl (term153 B t)). Qed.
Lemma lem4332258 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4332259 {B : Type'} (t : B -> Prop) : (term155 B t) = (term156 B t).
Proof. exact (MK_COMB (@lem4332258) (@lem4332257 B t)). Qed.
Lemma lem4332260 {B : Type'} : (term41 B) = (term41 B).
Proof. exact (eq_refl (term41 B)). Qed.
Lemma lem4332261 {B : Type'} (t : B -> Prop) : ((term153 B t) = (term41 B)) = ((term6 B t) = (term41 B)).
Proof. exact (MK_COMB (@lem4332259 B t) (@lem4332260 B)). Qed.
Lemma lem4332262 {B : Type'} (t : B -> Prop) : ((term153 B t) = (term154 B)) = ((term6 B t) = (term41 B)).
Proof. exact (TRANS (@lem4332256 B t) (@lem4332261 B t)). Qed.
Lemma lem4332263 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term6 B t) = (term41 B).
Proof. exact (EQ_MP (@lem4332262 B t) (@lem4332253 B t h1)). Qed.
Lemma lem4332264 {B : Type'} (t : B -> Prop) (h1 : term6 B t) (h2 : t = (@EMPTY B)) : term41 B.
Proof. exact (EQ_MP (@lem4332263 B t h2) (@lem4332168 B t h1)). Qed.
Lemma lem4332334 {B : Type'} : (term152 B) = (term152 B).
Proof. exact (eq_refl (term152 B)). Qed.
Lemma lem4332335 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term153 B t) = (term154 B).
Proof. exact (MK_COMB (@lem4332334 B) (@lem4331553 B t h1)). Qed.
Lemma lem4332336 {B : Type'} : (term154 B) = (term41 B).
Proof. exact (eq_refl (term154 B)). Qed.
Lemma lem4332337 {B : Type'} (t : B -> Prop) : (term155 B t) = (term155 B t).
Proof. exact (eq_refl (term155 B t)). Qed.
Lemma lem4332338 {B : Type'} (t : B -> Prop) : ((term153 B t) = (term154 B)) = ((term153 B t) = (term41 B)).
Proof. exact (MK_COMB (@lem4332337 B t) (@lem4332336 B)). Qed.
Lemma lem4332339 {B : Type'} (t : B -> Prop) : (term153 B t) = (term6 B t).
Proof. exact (eq_refl (term153 B t)). Qed.
Lemma lem4332340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4332341 {B : Type'} (t : B -> Prop) : (term155 B t) = (term156 B t).
Proof. exact (MK_COMB (@lem4332340) (@lem4332339 B t)). Qed.
Lemma lem4332342 {B : Type'} : (term41 B) = (term41 B).
Proof. exact (eq_refl (term41 B)). Qed.
Lemma lem4332343 {B : Type'} (t : B -> Prop) : ((term153 B t) = (term41 B)) = ((term6 B t) = (term41 B)).
Proof. exact (MK_COMB (@lem4332341 B t) (@lem4332342 B)). Qed.
Lemma lem4332344 {B : Type'} (t : B -> Prop) : ((term153 B t) = (term154 B)) = ((term6 B t) = (term41 B)).
Proof. exact (TRANS (@lem4332338 B t) (@lem4332343 B t)). Qed.
Lemma lem4332345 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term6 B t) = (term41 B).
Proof. exact (EQ_MP (@lem4332344 B t) (@lem4332335 B t h1)). Qed.
Lemma lem4332346 {B : Type'} (t : B -> Prop) (h1 : term6 B t) (h2 : t = (@EMPTY B)) : term41 B.
Proof. exact (EQ_MP (@lem4332345 B t h2) (@lem4331551 B t h1)). Qed.
Lemma lem4332347 {B : Type'} : (term157 B) = (term157 B).
Proof. exact (eq_refl (term157 B)). Qed.
Lemma lem4332348 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term158 B t) = (term159 B).
Proof. exact (MK_COMB (@lem4332347 B) (@lem4331553 B t h1)). Qed.
Lemma lem4332349 {B : Type'} : (term159 B) = (@FINITE B (@EMPTY B)).
Proof. exact (eq_refl (term159 B)). Qed.
Lemma lem4332350 {B : Type'} (t : B -> Prop) : (term160 B t) = (term160 B t).
Proof. exact (eq_refl (term160 B t)). Qed.
Lemma lem4332351 {B : Type'} (t : B -> Prop) : ((term158 B t) = (term159 B)) = ((term158 B t) = (@FINITE B (@EMPTY B))).
Proof. exact (MK_COMB (@lem4332350 B t) (@lem4332349 B)). Qed.
Lemma lem4332352 {B : Type'} (t : B -> Prop) : (term158 B t) = (@FINITE B t).
Proof. exact (eq_refl (term158 B t)). Qed.
Lemma lem4332353 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4332354 {B : Type'} (t : B -> Prop) : (term160 B t) = (term161 B t).
Proof. exact (MK_COMB (@lem4332353) (@lem4332352 B t)). Qed.
Lemma lem4332355 {B : Type'} : (@FINITE B (@EMPTY B)) = (@FINITE B (@EMPTY B)).
Proof. exact (eq_refl (@FINITE B (@EMPTY B))). Qed.
Lemma lem4332356 {B : Type'} (t : B -> Prop) : ((term158 B t) = (@FINITE B (@EMPTY B))) = ((@FINITE B t) = (@FINITE B (@EMPTY B))).
Proof. exact (MK_COMB (@lem4332354 B t) (@lem4332355 B)). Qed.
Lemma lem4332357 {B : Type'} (t : B -> Prop) : ((term158 B t) = (term159 B)) = ((@FINITE B t) = (@FINITE B (@EMPTY B))).
Proof. exact (TRANS (@lem4332351 B t) (@lem4332356 B t)). Qed.
Lemma lem4332358 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (@FINITE B t) = (@FINITE B (@EMPTY B)).
Proof. exact (EQ_MP (@lem4332357 B t) (@lem4332348 B t h1)). Qed.
Lemma lem4332402 {A : Type'} : (term162 A) = (term162 A).
Proof. exact (eq_refl (term162 A)). Qed.
Lemma lem4332403 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term163 A s) = (term164 A).
Proof. exact (MK_COMB (@lem4332402 A) (@lem4331565 A s h1)). Qed.
Lemma lem4332404 {A : Type'} : (term164 A) = (term165 A).
Proof. exact (eq_refl (term164 A)). Qed.
Lemma lem4332405 {A : Type'} (s : A -> Prop) : (term166 A s) = (term166 A s).
Proof. exact (eq_refl (term166 A s)). Qed.
Lemma lem4332406 {A : Type'} (s : A -> Prop) : ((term163 A s) = (term164 A)) = ((term163 A s) = (term165 A)).
Proof. exact (MK_COMB (@lem4332405 A s) (@lem4332404 A)). Qed.
Lemma lem4332407 {A : Type'} (s : A -> Prop) : (term163 A s) = (term20 A s).
Proof. exact (eq_refl (term163 A s)). Qed.
Lemma lem4332408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4332409 {A : Type'} (s : A -> Prop) : (term166 A s) = (term167 A s).
Proof. exact (MK_COMB (@lem4332408) (@lem4332407 A s)). Qed.
Lemma lem4332410 {A : Type'} : (term165 A) = (term165 A).
Proof. exact (eq_refl (term165 A)). Qed.
Lemma lem4332411 {A : Type'} (s : A -> Prop) : ((term163 A s) = (term165 A)) = ((term20 A s) = (term165 A)).
Proof. exact (MK_COMB (@lem4332409 A s) (@lem4332410 A)). Qed.
Lemma lem4332412 {A : Type'} (s : A -> Prop) : ((term163 A s) = (term164 A)) = ((term20 A s) = (term165 A)).
Proof. exact (TRANS (@lem4332406 A s) (@lem4332411 A s)). Qed.
Lemma lem4332413 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term20 A s) = (term165 A).
Proof. exact (EQ_MP (@lem4332412 A s) (@lem4332403 A s h1)). Qed.
Lemma lem4332414 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term15 A B s t) (h2 : s = (@EMPTY A)) : term165 A.
Proof. exact (EQ_MP (@lem4332413 A s h2) (@lem4331561 A B s t h1)). Qed.
Lemma lem4332470 {B : Type'} (h1 : @FINITE B (@EMPTY B)) : @FINITE B (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4332485 {B : Type'} : (term152 B) = (term152 B).
Proof. exact (eq_refl (term152 B)). Qed.
Lemma lem4332486 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term153 B t) = (term154 B).
Proof. exact (MK_COMB (@lem4332485 B) (@lem4331575 B t h1)). Qed.
Lemma lem4332487 {B : Type'} : (term154 B) = (term41 B).
Proof. exact (eq_refl (term154 B)). Qed.
Lemma lem4332488 {B : Type'} (t : B -> Prop) : (term155 B t) = (term155 B t).
Proof. exact (eq_refl (term155 B t)). Qed.
Lemma lem4332489 {B : Type'} (t : B -> Prop) : ((term153 B t) = (term154 B)) = ((term153 B t) = (term41 B)).
Proof. exact (MK_COMB (@lem4332488 B t) (@lem4332487 B)). Qed.
Lemma lem4332490 {B : Type'} (t : B -> Prop) : (term153 B t) = (term6 B t).
Proof. exact (eq_refl (term153 B t)). Qed.
Lemma lem4332491 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4332492 {B : Type'} (t : B -> Prop) : (term155 B t) = (term156 B t).
Proof. exact (MK_COMB (@lem4332491) (@lem4332490 B t)). Qed.
Lemma lem4332493 {B : Type'} : (term41 B) = (term41 B).
Proof. exact (eq_refl (term41 B)). Qed.
Lemma lem4332494 {B : Type'} (t : B -> Prop) : ((term153 B t) = (term41 B)) = ((term6 B t) = (term41 B)).
Proof. exact (MK_COMB (@lem4332492 B t) (@lem4332493 B)). Qed.
Lemma lem4332495 {B : Type'} (t : B -> Prop) : ((term153 B t) = (term154 B)) = ((term6 B t) = (term41 B)).
Proof. exact (TRANS (@lem4332489 B t) (@lem4332494 B t)). Qed.
Lemma lem4332496 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term6 B t) = (term41 B).
Proof. exact (EQ_MP (@lem4332495 B t) (@lem4332486 B t h1)). Qed.
Lemma lem4332497 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) (h2 : t = (@EMPTY B)) : term41 B.
Proof. exact (EQ_MP (@lem4332496 B t h2) (@lem4331573 A B s t h1)). Qed.
Lemma lem4332525 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4332540 {A : Type'} : (term152 A) = (term152 A).
Proof. exact (eq_refl (term152 A)). Qed.
Lemma lem4332541 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term153 A s) = (term154 A).
Proof. exact (MK_COMB (@lem4332540 A) (@lem4331597 A s h1)). Qed.
Lemma lem4332542 {A : Type'} : (term154 A) = (term41 A).
Proof. exact (eq_refl (term154 A)). Qed.
Lemma lem4332543 {A : Type'} (s : A -> Prop) : (term155 A s) = (term155 A s).
Proof. exact (eq_refl (term155 A s)). Qed.
Lemma lem4332544 {A : Type'} (s : A -> Prop) : ((term153 A s) = (term154 A)) = ((term153 A s) = (term41 A)).
Proof. exact (MK_COMB (@lem4332543 A s) (@lem4332542 A)). Qed.
Lemma lem4332545 {A : Type'} (s : A -> Prop) : (term153 A s) = (term6 A s).
Proof. exact (eq_refl (term153 A s)). Qed.
Lemma lem4332546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4332547 {A : Type'} (s : A -> Prop) : (term155 A s) = (term156 A s).
Proof. exact (MK_COMB (@lem4332546) (@lem4332545 A s)). Qed.
Lemma lem4332548 {A : Type'} : (term41 A) = (term41 A).
Proof. exact (eq_refl (term41 A)). Qed.
Lemma lem4332549 {A : Type'} (s : A -> Prop) : ((term153 A s) = (term41 A)) = ((term6 A s) = (term41 A)).
Proof. exact (MK_COMB (@lem4332547 A s) (@lem4332548 A)). Qed.
Lemma lem4332550 {A : Type'} (s : A -> Prop) : ((term153 A s) = (term154 A)) = ((term6 A s) = (term41 A)).
Proof. exact (TRANS (@lem4332544 A s) (@lem4332549 A s)). Qed.
Lemma lem4332551 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term6 A s) = (term41 A).
Proof. exact (EQ_MP (@lem4332550 A s) (@lem4332541 A s h1)). Qed.
Lemma lem4332552 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term22 A B s t) (h2 : s = (@EMPTY A)) : term41 A.
Proof. exact (EQ_MP (@lem4332551 A s h2) (@lem4331593 A B s t h1)). Qed.
Lemma lem4332623 {B : Type'} : (term162 B) = (term162 B).
Proof. exact (eq_refl (term162 B)). Qed.
Lemma lem4332624 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term163 B t) = (term164 B).
Proof. exact (MK_COMB (@lem4332623 B) (@lem4331607 B t h1)). Qed.
Lemma lem4332625 {B : Type'} : (term164 B) = (term165 B).
Proof. exact (eq_refl (term164 B)). Qed.
Lemma lem4332626 {B : Type'} (t : B -> Prop) : (term166 B t) = (term166 B t).
Proof. exact (eq_refl (term166 B t)). Qed.
Lemma lem4332627 {B : Type'} (t : B -> Prop) : ((term163 B t) = (term164 B)) = ((term163 B t) = (term165 B)).
Proof. exact (MK_COMB (@lem4332626 B t) (@lem4332625 B)). Qed.
Lemma lem4332628 {B : Type'} (t : B -> Prop) : (term163 B t) = (term20 B t).
Proof. exact (eq_refl (term163 B t)). Qed.
Lemma lem4332629 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4332630 {B : Type'} (t : B -> Prop) : (term166 B t) = (term167 B t).
Proof. exact (MK_COMB (@lem4332629) (@lem4332628 B t)). Qed.
Lemma lem4332631 {B : Type'} : (term165 B) = (term165 B).
Proof. exact (eq_refl (term165 B)). Qed.
Lemma lem4332632 {B : Type'} (t : B -> Prop) : ((term163 B t) = (term165 B)) = ((term20 B t) = (term165 B)).
Proof. exact (MK_COMB (@lem4332630 B t) (@lem4332631 B)). Qed.
Lemma lem4332633 {B : Type'} (t : B -> Prop) : ((term163 B t) = (term164 B)) = ((term20 B t) = (term165 B)).
Proof. exact (TRANS (@lem4332627 B t) (@lem4332632 B t)). Qed.
Lemma lem4332634 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term20 B t) = (term165 B).
Proof. exact (EQ_MP (@lem4332633 B t) (@lem4332624 B t h1)). Qed.
Lemma lem4332635 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) (h2 : t = (@EMPTY B)) : term165 B.
Proof. exact (EQ_MP (@lem4332634 B t h2) (@lem4331605 A B s t h1)). Qed.
Lemma lem4332665 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : s = (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (EQ_MP (@lem4331713 A s h2) (@lem4331455 A s h1)). Qed.
Lemma lem4332666 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : s = (@EMPTY A)) : term168 A.
Proof. exact (fun h0 : term41 A => @lem4332665 A s h1 h2). Qed.
Lemma lem4332668 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4332669 {A : Type'} : (term168 A) = (@FINITE A (@EMPTY A)).
Proof. exact (@lem4332668 (@FINITE A (@EMPTY A))). Qed.
Lemma lem4332670 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : s = (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (EQ_MP (@lem4332669 A) (@lem4332666 A s h1 h2)). Qed.
Lemma lem4332673 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4332675 {A : Type'} : (term41 A) = (term40 A).
Proof. exact (@lem4332673 (@FINITE A (@EMPTY A))). Qed.
Lemma lem4332678 {A : Type'} (s : A -> Prop) (h1 : term6 A s) (h2 : s = (@EMPTY A)) : term40 A.
Proof. exact (EQ_MP (@lem4332675 A) (@lem4331701 A s h1 h2)). Qed.
Lemma lem4332681 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (@lem4332678 A s h2 h3 (@lem4332670 A s h1 h3)). Qed.
Lemma lem4332682 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : term170.
Proof. exact (fun h0 : ~ False => @lem4332681 A s h1 h2 h3). Qed.
Lemma lem4332684 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4332685 : term170 = False.
Proof. exact (@lem4332684 False). Qed.
Lemma lem4332716 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4332717 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term171 A s.
Proof. exact (fun h0 : term6 A s => @lem4332716 A s h1). Qed.
Lemma lem4332719 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4332720 {A : Type'} (s : A -> Prop) : (term171 A s) = (@FINITE A s).
Proof. exact (@lem4332719 (@FINITE A s)). Qed.
Lemma lem4332721 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4332720 A s) (@lem4332717 A s h1)). Qed.
Lemma lem4332724 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4332726 {A : Type'} (s : A -> Prop) : (term6 A s) = (term172 A s).
Proof. exact (@lem4332724 (@FINITE A s)). Qed.
Lemma lem4332729 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : term172 A s.
Proof. exact (EQ_MP (@lem4332726 A s) (@lem4331467 A s h1)). Qed.
Lemma lem4332732 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : False.
Proof. exact (@lem4332729 A s h2 (@lem4332721 A s h1)). Qed.
Lemma lem4332733 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : term170.
Proof. exact (fun h0 : ~ False => @lem4332732 A s h1 h2). Qed.
Lemma lem4332735 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4332736 : term170 = False.
Proof. exact (@lem4332735 False). Qed.
Lemma lem4332737 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : False.
Proof. exact (EQ_MP (@lem4332736) (@lem4332733 A s h1 h2)). Qed.
Lemma lem4332767 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4332768 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : term168 A.
Proof. exact (fun h0 : term41 A => @lem4332767 A h1). Qed.
Lemma lem4332770 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4332771 {A : Type'} : (term168 A) = (@FINITE A (@EMPTY A)).
Proof. exact (@lem4332770 (@FINITE A (@EMPTY A))). Qed.
Lemma lem4332772 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (EQ_MP (@lem4332771 A) (@lem4332768 A h1)). Qed.
Lemma lem4332775 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4332777 {A : Type'} : (term41 A) = (term40 A).
Proof. exact (@lem4332775 (@FINITE A (@EMPTY A))). Qed.
Lemma lem4332780 {A : Type'} (s : A -> Prop) (h1 : term6 A s) (h2 : s = (@EMPTY A)) : term40 A.
Proof. exact (EQ_MP (@lem4332777 A) (@lem4331893 A s h1 h2)). Qed.
Lemma lem4332783 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (@lem4332780 A s h2 h3 (@lem4332772 A h1)). Qed.
Lemma lem4332784 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : term170.
Proof. exact (fun h0 : ~ False => @lem4332783 A s h1 h2 h3). Qed.
Lemma lem4332786 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4332787 : term170 = False.
Proof. exact (@lem4332786 False). Qed.
Lemma lem4332788 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4332787) (@lem4332784 A s h1 h2 h3)). Qed.
Lemma lem4332818 {B : Type'} (x : B -> Prop) : x = x.
Proof. exact (@lem21386 (B -> Prop) x). Qed.
Lemma lem4332819 {B : Type'} (x : B -> Prop) : x = x.
Proof. exact (@lem4332818 B x). Qed.
Lemma lem4332820 {B : Type'} : (@EMPTY B) = (@EMPTY B).
Proof. exact (@lem4332819 B (@EMPTY B)). Qed.
Lemma lem4332821 {B : Type'} : term173 B.
Proof. exact (fun h0 : term165 B => @lem4332820 B). Qed.
Lemma lem4332823 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4332824 {B : Type'} : (term173 B) = ((@EMPTY B) = (@EMPTY B)).
Proof. exact (@lem4332823 ((@EMPTY B) = (@EMPTY B))). Qed.
Lemma lem4332825 {B : Type'} : (@EMPTY B) = (@EMPTY B).
Proof. exact (EQ_MP (@lem4332824 B) (@lem4332821 B)). Qed.
Lemma lem4332828 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4332830 {B : Type'} : (term165 B) = (term174 B).
Proof. exact (@lem4332828 ((@EMPTY B) = (@EMPTY B))). Qed.
Lemma lem4332833 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) (h2 : t = (@EMPTY B)) : term174 B.
Proof. exact (EQ_MP (@lem4332830 B) (@lem4331962 A B s t h1 h2)). Qed.
Lemma lem4332836 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) (h2 : t = (@EMPTY B)) : False.
Proof. exact (@lem4332833 A B s t h1 h2 (@lem4332825 B)). Qed.
Lemma lem4332837 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) (h2 : t = (@EMPTY B)) : term170.
Proof. exact (fun h0 : ~ False => @lem4332836 A B s t h1 h2). Qed.
Lemma lem4332839 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4332840 : term170 = False.
Proof. exact (@lem4332839 False). Qed.
Lemma lem4332871 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem4332872 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem4332871 A x). Qed.
Lemma lem4332873 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (@lem4332872 A (@EMPTY A)). Qed.
Lemma lem4332874 {A : Type'} : term173 A.
Proof. exact (fun h0 : term165 A => @lem4332873 A). Qed.
Lemma lem4332876 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4332877 {A : Type'} : (term173 A) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (@lem4332876 ((@EMPTY A) = (@EMPTY A))). Qed.
Lemma lem4332878 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (EQ_MP (@lem4332877 A) (@lem4332874 A)). Qed.
Lemma lem4332881 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4332883 {A : Type'} : (term165 A) = (term174 A).
Proof. exact (@lem4332881 ((@EMPTY A) = (@EMPTY A))). Qed.
Lemma lem4332886 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term81 A B s t) (h2 : s = (@EMPTY A)) : term174 A.
Proof. exact (EQ_MP (@lem4332883 A) (@lem4332044 A B t s h1 h2)). Qed.
Lemma lem4332889 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term81 A B s t) (h2 : s = (@EMPTY A)) : False.
Proof. exact (@lem4332886 A B t s h1 h2 (@lem4332878 A)). Qed.
Lemma lem4332890 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term81 A B s t) (h2 : s = (@EMPTY A)) : term170.
Proof. exact (fun h0 : ~ False => @lem4332889 A B t s h1 h2). Qed.
Lemma lem4332892 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4332893 : term170 = False.
Proof. exact (@lem4332892 False). Qed.
Lemma lem4332924 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem4332925 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : term171 B t.
Proof. exact (fun h0 : term6 B t => @lem4332924 B t h1). Qed.
Lemma lem4332927 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4332928 {B : Type'} (t : B -> Prop) : (term171 B t) = (@FINITE B t).
Proof. exact (@lem4332927 (@FINITE B t)). Qed.
Lemma lem4332929 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem4332928 B t) (@lem4332925 B t h1)). Qed.
Lemma lem4332932 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4332934 {B : Type'} (t : B -> Prop) : (term6 B t) = (term172 B t).
Proof. exact (@lem4332932 (@FINITE B t)). Qed.
Lemma lem4332937 {B : Type'} (t : B -> Prop) (h1 : term6 B t) : term172 B t.
Proof. exact (EQ_MP (@lem4332934 B t) (@lem4331523 B t h1)). Qed.
Lemma lem4332940 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) : False.
Proof. exact (@lem4332937 B t h2 (@lem4332929 B t h1)). Qed.
Lemma lem4332941 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) : term170.
Proof. exact (fun h0 : ~ False => @lem4332940 B t h1 h2). Qed.
Lemma lem4332943 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4332944 : term170 = False.
Proof. exact (@lem4332943 False). Qed.
Lemma lem4332945 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) : False.
Proof. exact (EQ_MP (@lem4332944) (@lem4332941 B t h1 h2)). Qed.
Lemma lem4332975 {B : Type'} (h1 : @FINITE B (@EMPTY B)) : @FINITE B (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4332976 {B : Type'} (h1 : @FINITE B (@EMPTY B)) : term168 B.
Proof. exact (fun h0 : term41 B => @lem4332975 B h1). Qed.
Lemma lem4332978 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4332979 {B : Type'} : (term168 B) = (@FINITE B (@EMPTY B)).
Proof. exact (@lem4332978 (@FINITE B (@EMPTY B))). Qed.
Lemma lem4332980 {B : Type'} (h1 : @FINITE B (@EMPTY B)) : @FINITE B (@EMPTY B).
Proof. exact (EQ_MP (@lem4332979 B) (@lem4332976 B h1)). Qed.
Lemma lem4332983 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4332985 {B : Type'} : (term41 B) = (term40 B).
Proof. exact (@lem4332983 (@FINITE B (@EMPTY B))). Qed.
Lemma lem4332988 {B : Type'} (t : B -> Prop) (h1 : term6 B t) (h2 : t = (@EMPTY B)) : term40 B.
Proof. exact (EQ_MP (@lem4332985 B) (@lem4332264 B t h1 h2)). Qed.
Lemma lem4332991 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (@lem4332988 B t h2 h3 (@lem4332980 B h1)). Qed.
Lemma lem4332992 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : term170.
Proof. exact (fun h0 : ~ False => @lem4332991 B t h1 h2 h3). Qed.
Lemma lem4332994 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4332995 : term170 = False.
Proof. exact (@lem4332994 False). Qed.
Lemma lem4332996 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4332995) (@lem4332992 B t h1 h2 h3)). Qed.
Lemma lem4333026 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : t = (@EMPTY B)) : @FINITE B (@EMPTY B).
Proof. exact (EQ_MP (@lem4332358 B t h2) (@lem4331555 B t h1)). Qed.
Lemma lem4333027 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : t = (@EMPTY B)) : term168 B.
Proof. exact (fun h0 : term41 B => @lem4333026 B t h1 h2). Qed.
Lemma lem4333029 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4333030 {B : Type'} : (term168 B) = (@FINITE B (@EMPTY B)).
Proof. exact (@lem4333029 (@FINITE B (@EMPTY B))). Qed.
Lemma lem4333031 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : t = (@EMPTY B)) : @FINITE B (@EMPTY B).
Proof. exact (EQ_MP (@lem4333030 B) (@lem4333027 B t h1 h2)). Qed.
Lemma lem4333034 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4333036 {B : Type'} : (term41 B) = (term40 B).
Proof. exact (@lem4333034 (@FINITE B (@EMPTY B))). Qed.
Lemma lem4333039 {B : Type'} (t : B -> Prop) (h1 : term6 B t) (h2 : t = (@EMPTY B)) : term40 B.
Proof. exact (EQ_MP (@lem4333036 B) (@lem4332346 B t h1 h2)). Qed.
Lemma lem4333042 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (@lem4333039 B t h2 h3 (@lem4333031 B t h1 h3)). Qed.
Lemma lem4333043 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : term170.
Proof. exact (fun h0 : ~ False => @lem4333042 B t h1 h2 h3). Qed.
Lemma lem4333045 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4333046 : term170 = False.
Proof. exact (@lem4333045 False). Qed.
Lemma lem4333077 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem4333078 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem4333077 A x). Qed.
Lemma lem4333079 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (@lem4333078 A (@EMPTY A)). Qed.
Lemma lem4333080 {A : Type'} : term173 A.
Proof. exact (fun h0 : term165 A => @lem4333079 A). Qed.
Lemma lem4333082 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4333083 {A : Type'} : (term173 A) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (@lem4333082 ((@EMPTY A) = (@EMPTY A))). Qed.
Lemma lem4333084 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (EQ_MP (@lem4333083 A) (@lem4333080 A)). Qed.
Lemma lem4333087 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4333089 {A : Type'} : (term165 A) = (term174 A).
Proof. exact (@lem4333087 ((@EMPTY A) = (@EMPTY A))). Qed.
Lemma lem4333092 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term15 A B s t) (h2 : s = (@EMPTY A)) : term174 A.
Proof. exact (EQ_MP (@lem4333089 A) (@lem4332414 A B t s h1 h2)). Qed.
Lemma lem4333095 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term15 A B s t) (h2 : s = (@EMPTY A)) : False.
Proof. exact (@lem4333092 A B t s h1 h2 (@lem4333084 A)). Qed.
Lemma lem4333096 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term15 A B s t) (h2 : s = (@EMPTY A)) : term170.
Proof. exact (fun h0 : ~ False => @lem4333095 A B t s h1 h2). Qed.
Lemma lem4333098 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4333099 : term170 = False.
Proof. exact (@lem4333098 False). Qed.
Lemma lem4333130 {B : Type'} (h1 : @FINITE B (@EMPTY B)) : @FINITE B (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4333131 {B : Type'} (h1 : @FINITE B (@EMPTY B)) : term168 B.
Proof. exact (fun h0 : term41 B => @lem4333130 B h1). Qed.
Lemma lem4333133 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4333134 {B : Type'} : (term168 B) = (@FINITE B (@EMPTY B)).
Proof. exact (@lem4333133 (@FINITE B (@EMPTY B))). Qed.
Lemma lem4333135 {B : Type'} (h1 : @FINITE B (@EMPTY B)) : @FINITE B (@EMPTY B).
Proof. exact (EQ_MP (@lem4333134 B) (@lem4333131 B h1)). Qed.
Lemma lem4333138 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4333140 {B : Type'} : (term41 B) = (term40 B).
Proof. exact (@lem4333138 (@FINITE B (@EMPTY B))). Qed.
Lemma lem4333143 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) (h2 : t = (@EMPTY B)) : term40 B.
Proof. exact (EQ_MP (@lem4333140 B) (@lem4332497 A B s t h1 h2)). Qed.
Lemma lem4333146 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (@lem4333143 A B s t h2 h3 (@lem4333135 B h1)). Qed.
Lemma lem4333147 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : term170.
Proof. exact (fun h0 : ~ False => @lem4333146 A B s t h1 h2 h3). Qed.
Lemma lem4333149 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4333150 : term170 = False.
Proof. exact (@lem4333149 False). Qed.
Lemma lem4333151 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333150) (@lem4333147 A B s t h1 h2 h3)). Qed.
Lemma lem4333181 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term52 A B s t) : @FINITE B t.
Proof. exact (proj2 (@lem4331081 A B s t h1)). Qed.
Lemma lem4333182 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term52 A B s t) : term171 B t.
Proof. exact (fun h0 : term6 B t => @lem4333181 A B s t h1). Qed.
Lemma lem4333184 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4333185 {B : Type'} (t : B -> Prop) : (term171 B t) = (@FINITE B t).
Proof. exact (@lem4333184 (@FINITE B t)). Qed.
Lemma lem4333186 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term52 A B s t) : @FINITE B t.
Proof. exact (EQ_MP (@lem4333185 B t) (@lem4333182 A B s t h1)). Qed.
Lemma lem4333189 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4333191 {B : Type'} (t : B -> Prop) : (term6 B t) = (term172 B t).
Proof. exact (@lem4333189 (@FINITE B t)). Qed.
Lemma lem4333194 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term172 B t.
Proof. exact (EQ_MP (@lem4333191 B t) (@lem4331583 A B s t h1)). Qed.
Lemma lem4333197 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term52 A B s t) (h2 : term15 A B s t) : False.
Proof. exact (@lem4333194 A B s t h2 (@lem4333186 A B s t h1)). Qed.
Lemma lem4333198 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term52 A B s t) (h2 : term15 A B s t) : term170.
Proof. exact (fun h0 : ~ False => @lem4333197 A B s t h1 h2). Qed.
Lemma lem4333200 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4333201 : term170 = False.
Proof. exact (@lem4333200 False). Qed.
Lemma lem4333202 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term52 A B s t) (h2 : term15 A B s t) : False.
Proof. exact (EQ_MP (@lem4333201) (@lem4333198 A B s t h1 h2)). Qed.
Lemma lem4333232 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4333233 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : term168 A.
Proof. exact (fun h0 : term41 A => @lem4333232 A h1). Qed.
Lemma lem4333235 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4333236 {A : Type'} : (term168 A) = (@FINITE A (@EMPTY A)).
Proof. exact (@lem4333235 (@FINITE A (@EMPTY A))). Qed.
Lemma lem4333237 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (EQ_MP (@lem4333236 A) (@lem4333233 A h1)). Qed.
Lemma lem4333240 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4333242 {A : Type'} : (term41 A) = (term40 A).
Proof. exact (@lem4333240 (@FINITE A (@EMPTY A))). Qed.
Lemma lem4333245 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term22 A B s t) (h2 : s = (@EMPTY A)) : term40 A.
Proof. exact (EQ_MP (@lem4333242 A) (@lem4332552 A B t s h1 h2)). Qed.
Lemma lem4333248 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : False.
Proof. exact (@lem4333245 A B t s h2 h3 (@lem4333237 A h1)). Qed.
Lemma lem4333249 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : term170.
Proof. exact (fun h0 : ~ False => @lem4333248 A B t s h1 h2 h3). Qed.
Lemma lem4333251 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4333252 : term170 = False.
Proof. exact (@lem4333251 False). Qed.
Lemma lem4333253 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333252) (@lem4333249 A B t s h1 h2 h3)). Qed.
Lemma lem4333283 {B : Type'} (x : B -> Prop) : x = x.
Proof. exact (@lem21386 (B -> Prop) x). Qed.
Lemma lem4333284 {B : Type'} (x : B -> Prop) : x = x.
Proof. exact (@lem4333283 B x). Qed.
Lemma lem4333285 {B : Type'} : (@EMPTY B) = (@EMPTY B).
Proof. exact (@lem4333284 B (@EMPTY B)). Qed.
Lemma lem4333286 {B : Type'} : term173 B.
Proof. exact (fun h0 : term165 B => @lem4333285 B). Qed.
Lemma lem4333288 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4333289 {B : Type'} : (term173 B) = ((@EMPTY B) = (@EMPTY B)).
Proof. exact (@lem4333288 ((@EMPTY B) = (@EMPTY B))). Qed.
Lemma lem4333290 {B : Type'} : (@EMPTY B) = (@EMPTY B).
Proof. exact (EQ_MP (@lem4333289 B) (@lem4333286 B)). Qed.
Lemma lem4333293 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4333295 {B : Type'} : (term165 B) = (term174 B).
Proof. exact (@lem4333293 ((@EMPTY B) = (@EMPTY B))). Qed.
Lemma lem4333298 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) (h2 : t = (@EMPTY B)) : term174 B.
Proof. exact (EQ_MP (@lem4333295 B) (@lem4332635 A B s t h1 h2)). Qed.
Lemma lem4333301 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) (h2 : t = (@EMPTY B)) : False.
Proof. exact (@lem4333298 A B s t h1 h2 (@lem4333290 B)). Qed.
Lemma lem4333302 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) (h2 : t = (@EMPTY B)) : term170.
Proof. exact (fun h0 : ~ False => @lem4333301 A B s t h1 h2). Qed.
Lemma lem4333304 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4333305 : term170 = False.
Proof. exact (@lem4333304 False). Qed.
Lemma lem4333336 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term52 A B s t) : @FINITE A s.
Proof. exact (proj1 (@lem4331089 A B s t h1)). Qed.
Lemma lem4333337 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term52 A B s t) : term171 A s.
Proof. exact (fun h0 : term6 A s => @lem4333336 A B s t h1). Qed.
Lemma lem4333339 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4333340 {A : Type'} (s : A -> Prop) : (term171 A s) = (@FINITE A s).
Proof. exact (@lem4333339 (@FINITE A s)). Qed.
Lemma lem4333341 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term52 A B s t) : @FINITE A s.
Proof. exact (EQ_MP (@lem4333340 A s) (@lem4333337 A B s t h1)). Qed.
Lemma lem4333344 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4333346 {A : Type'} (s : A -> Prop) : (term6 A s) = (term172 A s).
Proof. exact (@lem4333344 (@FINITE A s)). Qed.
Lemma lem4333349 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) : term172 A s.
Proof. exact (EQ_MP (@lem4333346 A s) (@lem4331613 A B s t h1)). Qed.
Lemma lem4333352 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term52 A B s t) (h2 : term22 A B s t) : False.
Proof. exact (@lem4333349 A B s t h2 (@lem4333341 A B s t h1)). Qed.
Lemma lem4333353 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term52 A B s t) (h2 : term22 A B s t) : term170.
Proof. exact (fun h0 : ~ False => @lem4333352 A B s t h1 h2). Qed.
Lemma lem4333355 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4333356 : term170 = False.
Proof. exact (@lem4333355 False). Qed.
Lemma lem4333357 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term52 A B s t) (h2 : term22 A B s t) : False.
Proof. exact (EQ_MP (@lem4333356) (@lem4333353 A B s t h1 h2)). Qed.
Lemma lem4333358 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) (h2 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333305) (@lem4333302 A B s t h1 h2)). Qed.
Lemma lem4333359 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : (@FINITE A (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A (@EMPTY A) => @lem4333253 A B t s h1 h2 h3) (fun h4 : False => @lem4332525 A h1)). Qed.
Lemma lem4333361 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333359 A B t s h1 h2 h3) (@lem4332525 A h1)). Qed.
Lemma lem4333362 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : (@FINITE B (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE B (@EMPTY B) => @lem4333151 A B s t h1 h2 h3) (fun h4 : False => @lem4332470 B h1)). Qed.
Lemma lem4333364 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333362 A B s t h1 h2 h3) (@lem4332470 B h1)). Qed.
Lemma lem4333365 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term15 A B s t) (h2 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333099) (@lem4333096 A B t s h1 h2)). Qed.
Lemma lem4333366 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333046) (@lem4333043 B t h1 h2 h3)). Qed.
Lemma lem4333367 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (@FINITE B (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE B (@EMPTY B) => @lem4332996 B t h1 h2 h3) (fun h4 : False => @lem4332224 B h1)). Qed.
Lemma lem4333369 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333367 B t h1 h2 h3) (@lem4332224 B h1)). Qed.
Lemma lem4333370 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : t = (@EMPTY B) => @lem4333369 B t h1 h2 h3) (fun h4 : False => @lem4332182 B t h3)). Qed.
Lemma lem4333371 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333370 B t h1 h2 h3) (@lem4332182 B t h3)). Qed.
Lemma lem4333372 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (term6 B t) = False.
Proof. exact (prop_ext (fun h4 : term6 B t => @lem4333371 B t h1 h2 h3) (fun h4 : False => @lem4332168 B t h2)). Qed.
Lemma lem4333373 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333372 B t h1 h2 h3) (@lem4332168 B t h2)). Qed.
Lemma lem4333374 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (@FINITE B (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE B (@EMPTY B) => @lem4333373 B t h1 h2 h3) (fun h4 : False => @lem4332127 B h1)). Qed.
Lemma lem4333376 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333374 B t h1 h2 h3) (@lem4332127 B h1)). Qed.
Lemma lem4333377 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term81 A B s t) (h2 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4332893) (@lem4332890 A B t s h1 h2)). Qed.
Lemma lem4333378 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) (h2 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4332840) (@lem4332837 A B s t h1 h2)). Qed.
Lemma lem4333379 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (@FINITE A (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A (@EMPTY A) => @lem4332788 A s h1 h2 h3) (fun h4 : False => @lem4331838 A h1)). Qed.
Lemma lem4333381 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333379 A s h1 h2 h3) (@lem4331838 A h1)). Qed.
Lemma lem4333382 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (@FINITE A (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A (@EMPTY A) => @lem4333381 A s h1 h2 h3) (fun h4 : False => @lem4331742 A h1)). Qed.
Lemma lem4333384 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333382 A s h1 h2 h3) (@lem4331742 A h1)). Qed.
Lemma lem4333385 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4332685) (@lem4332682 A s h1 h2 h3)). Qed.
Lemma lem4333386 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) (h2 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h3 : t = (@EMPTY B) => @lem4333358 A B s t h1 h2) (fun h3 : False => @lem4331607 B t h2)). Qed.
Lemma lem4333387 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) (h2 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333386 A B s t h1 h2) (@lem4331607 B t h2)). Qed.
Lemma lem4333388 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY A) => @lem4333361 A B t s h1 h2 h3) (fun h4 : False => @lem4331597 A s h3)). Qed.
Lemma lem4333389 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333388 A B t s h1 h2 h3) (@lem4331597 A s h3)). Qed.
Lemma lem4333390 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : (@FINITE A (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A (@EMPTY A) => @lem4333389 A B t s h1 h2 h3) (fun h4 : False => @lem4331589 A h1)). Qed.
Lemma lem4333391 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333390 A B t s h1 h2 h3) (@lem4331589 A h1)). Qed.
Lemma lem4333392 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : t = (@EMPTY B) => @lem4333364 A B s t h1 h2 h3) (fun h4 : False => @lem4331575 B t h3)). Qed.
Lemma lem4333393 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333392 A B s t h1 h2 h3) (@lem4331575 B t h3)). Qed.
Lemma lem4333394 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : (@FINITE B (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE B (@EMPTY B) => @lem4333393 A B s t h1 h2 h3) (fun h4 : False => @lem4331569 B h1)). Qed.
Lemma lem4333395 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333394 A B s t h1 h2 h3) (@lem4331569 B h1)). Qed.
Lemma lem4333396 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term15 A B s t) (h2 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h3 : s = (@EMPTY A) => @lem4333365 A B t s h1 h2) (fun h3 : False => @lem4331565 A s h2)). Qed.
Lemma lem4333397 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term15 A B s t) (h2 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333396 A B t s h1 h2) (@lem4331565 A s h2)). Qed.
Lemma lem4333398 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (@FINITE B t) = False.
Proof. exact (prop_ext (fun h4 : @FINITE B t => @lem4333366 B t h1 h2 h3) (fun h4 : False => @lem4331555 B t h1)). Qed.
Lemma lem4333399 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333398 B t h1 h2 h3) (@lem4331555 B t h1)). Qed.
Lemma lem4333400 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : t = (@EMPTY B) => @lem4333399 B t h1 h2 h3) (fun h4 : False => @lem4331553 B t h3)). Qed.
Lemma lem4333401 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333400 B t h1 h2 h3) (@lem4331553 B t h3)). Qed.
Lemma lem4333402 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (term6 B t) = False.
Proof. exact (prop_ext (fun h4 : term6 B t => @lem4333401 B t h1 h2 h3) (fun h4 : False => @lem4331551 B t h2)). Qed.
Lemma lem4333403 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333402 B t h1 h2 h3) (@lem4331551 B t h2)). Qed.
Lemma lem4333404 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : t = (@EMPTY B) => @lem4333376 B t h1 h2 h3) (fun h4 : False => @lem4331539 B t h3)). Qed.
Lemma lem4333405 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333404 B t h1 h2 h3) (@lem4331539 B t h3)). Qed.
Lemma lem4333406 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (term6 B t) = False.
Proof. exact (prop_ext (fun h4 : term6 B t => @lem4333405 B t h1 h2 h3) (fun h4 : False => @lem4331537 B t h2)). Qed.
Lemma lem4333407 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333406 B t h1 h2 h3) (@lem4331537 B t h2)). Qed.
Lemma lem4333408 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (@FINITE B (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE B (@EMPTY B) => @lem4333407 B t h1 h2 h3) (fun h4 : False => @lem4331531 B h1)). Qed.
Lemma lem4333409 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333408 B t h1 h2 h3) (@lem4331531 B h1)). Qed.
Lemma lem4333410 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) : (@FINITE B t) = False.
Proof. exact (prop_ext (fun h3 : @FINITE B t => @lem4332945 B t h1 h2) (fun h3 : False => @lem4331527 B t h1)). Qed.
Lemma lem4333411 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) : False.
Proof. exact (EQ_MP (@lem4333410 B t h1 h2) (@lem4331527 B t h1)). Qed.
Lemma lem4333412 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) : (term6 B t) = False.
Proof. exact (prop_ext (fun h3 : term6 B t => @lem4333411 B t h1 h2) (fun h3 : False => @lem4331523 B t h2)). Qed.
Lemma lem4333413 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) : False.
Proof. exact (EQ_MP (@lem4333412 B t h1 h2) (@lem4331523 B t h2)). Qed.
Lemma lem4333414 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term81 A B s t) (h2 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h3 : s = (@EMPTY A) => @lem4333377 A B t s h1 h2) (fun h3 : False => @lem4331513 A s h2)). Qed.
Lemma lem4333415 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term81 A B s t) (h2 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333414 A B t s h1 h2) (@lem4331513 A s h2)). Qed.
Lemma lem4333416 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) (h2 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h3 : t = (@EMPTY B) => @lem4333378 A B s t h1 h2) (fun h3 : False => @lem4331497 B t h2)). Qed.
Lemma lem4333417 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) (h2 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333416 A B s t h1 h2) (@lem4331497 B t h2)). Qed.
Lemma lem4333418 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY A) => @lem4333384 A s h1 h2 h3) (fun h4 : False => @lem4331485 A s h3)). Qed.
Lemma lem4333419 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333418 A s h1 h2 h3) (@lem4331485 A s h3)). Qed.
Lemma lem4333420 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (term6 A s) = False.
Proof. exact (prop_ext (fun h4 : term6 A s => @lem4333419 A s h1 h2 h3) (fun h4 : False => @lem4331481 A s h2)). Qed.
Lemma lem4333421 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333420 A s h1 h2 h3) (@lem4331481 A s h2)). Qed.
Lemma lem4333422 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (@FINITE A (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A (@EMPTY A) => @lem4333421 A s h1 h2 h3) (fun h4 : False => @lem4331473 A h1)). Qed.
Lemma lem4333423 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333422 A s h1 h2 h3) (@lem4331473 A h1)). Qed.
Lemma lem4333424 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem4332737 A s h1 h2) (fun h3 : False => @lem4331469 A s h1)). Qed.
Lemma lem4333425 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : False.
Proof. exact (EQ_MP (@lem4333424 A s h1 h2) (@lem4331469 A s h1)). Qed.
Lemma lem4333426 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : (term6 A s) = False.
Proof. exact (prop_ext (fun h3 : term6 A s => @lem4333425 A s h1 h2) (fun h3 : False => @lem4331467 A s h2)). Qed.
Lemma lem4333427 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : False.
Proof. exact (EQ_MP (@lem4333426 A s h1 h2) (@lem4331467 A s h2)). Qed.
Lemma lem4333428 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY A) => @lem4333385 A s h1 h2 h3) (fun h4 : False => @lem4331457 A s h3)). Qed.
Lemma lem4333429 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333428 A s h1 h2 h3) (@lem4331457 A s h3)). Qed.
Lemma lem4333430 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem4333429 A s h1 h2 h3) (fun h4 : False => @lem4331455 A s h1)). Qed.
Lemma lem4333431 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333430 A s h1 h2 h3) (@lem4331455 A s h1)). Qed.
Lemma lem4333432 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (term6 A s) = False.
Proof. exact (prop_ext (fun h4 : term6 A s => @lem4333431 A s h1 h2 h3) (fun h4 : False => @lem4331453 A s h2)). Qed.
Lemma lem4333433 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333432 A s h1 h2 h3) (@lem4331453 A s h2)). Qed.
Lemma lem4333434 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) (h2 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h3 : t = (@EMPTY B) => @lem4333387 A B s t h1 h2) (fun h3 : False => @lem4331419 B t h2)). Qed.
Lemma lem4333435 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) (h2 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333434 A B s t h1 h2) (@lem4331419 B t h2)). Qed.
Lemma lem4333436 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY A) => @lem4333391 A B t s h1 h2 h3) (fun h4 : False => @lem4331399 A s h3)). Qed.
Lemma lem4333437 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333436 A B t s h1 h2 h3) (@lem4331399 A s h3)). Qed.
Lemma lem4333438 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : (@FINITE A (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A (@EMPTY A) => @lem4333437 A B t s h1 h2 h3) (fun h4 : False => @lem4331383 A h1)). Qed.
Lemma lem4333439 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333438 A B t s h1 h2 h3) (@lem4331383 A h1)). Qed.
Lemma lem4333440 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : t = (@EMPTY B) => @lem4333395 A B s t h1 h2 h3) (fun h4 : False => @lem4331355 B t h3)). Qed.
Lemma lem4333441 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333440 A B s t h1 h2 h3) (@lem4331355 B t h3)). Qed.
Lemma lem4333442 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : (@FINITE B (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE B (@EMPTY B) => @lem4333441 A B s t h1 h2 h3) (fun h4 : False => @lem4331343 B h1)). Qed.
Lemma lem4333443 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333442 A B s t h1 h2 h3) (@lem4331343 B h1)). Qed.
Lemma lem4333444 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term15 A B s t) (h2 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h3 : s = (@EMPTY A) => @lem4333397 A B t s h1 h2) (fun h3 : False => @lem4331335 A s h2)). Qed.
Lemma lem4333445 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term15 A B s t) (h2 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333444 A B t s h1 h2) (@lem4331335 A s h2)). Qed.
Lemma lem4333446 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (@FINITE B t) = False.
Proof. exact (prop_ext (fun h4 : @FINITE B t => @lem4333403 B t h1 h2 h3) (fun h4 : False => @lem4331315 B t h1)). Qed.
Lemma lem4333447 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333446 B t h1 h2 h3) (@lem4331315 B t h1)). Qed.
Lemma lem4333448 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : t = (@EMPTY B) => @lem4333447 B t h1 h2 h3) (fun h4 : False => @lem4331311 B t h3)). Qed.
Lemma lem4333449 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333448 B t h1 h2 h3) (@lem4331311 B t h3)). Qed.
Lemma lem4333450 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (term6 B t) = False.
Proof. exact (prop_ext (fun h4 : term6 B t => @lem4333449 B t h1 h2 h3) (fun h4 : False => @lem4331307 B t h2)). Qed.
Lemma lem4333451 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333450 B t h1 h2 h3) (@lem4331307 B t h2)). Qed.
Lemma lem4333452 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : t = (@EMPTY B) => @lem4333409 B t h1 h2 h3) (fun h4 : False => @lem4331283 B t h3)). Qed.
Lemma lem4333453 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333452 B t h1 h2 h3) (@lem4331283 B t h3)). Qed.
Lemma lem4333454 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (term6 B t) = False.
Proof. exact (prop_ext (fun h4 : term6 B t => @lem4333453 B t h1 h2 h3) (fun h4 : False => @lem4331279 B t h2)). Qed.
Lemma lem4333455 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333454 B t h1 h2 h3) (@lem4331279 B t h2)). Qed.
Lemma lem4333456 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (@FINITE B (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE B (@EMPTY B) => @lem4333455 B t h1 h2 h3) (fun h4 : False => @lem4331267 B h1)). Qed.
Lemma lem4333457 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333456 B t h1 h2 h3) (@lem4331267 B h1)). Qed.
Lemma lem4333458 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) : (@FINITE B t) = False.
Proof. exact (prop_ext (fun h3 : @FINITE B t => @lem4333413 B t h1 h2) (fun h3 : False => @lem4331259 B t h1)). Qed.
Lemma lem4333459 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) : False.
Proof. exact (EQ_MP (@lem4333458 B t h1 h2) (@lem4331259 B t h1)). Qed.
Lemma lem4333460 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) : (term6 B t) = False.
Proof. exact (prop_ext (fun h3 : term6 B t => @lem4333459 B t h1 h2) (fun h3 : False => @lem4331251 B t h2)). Qed.
Lemma lem4333461 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) : False.
Proof. exact (EQ_MP (@lem4333460 B t h1 h2) (@lem4331251 B t h2)). Qed.
Lemma lem4333462 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term81 A B s t) (h2 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h3 : s = (@EMPTY A) => @lem4333415 A B t s h1 h2) (fun h3 : False => @lem4331231 A s h2)). Qed.
Lemma lem4333463 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term81 A B s t) (h2 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333462 A B t s h1 h2) (@lem4331231 A s h2)). Qed.
Lemma lem4333464 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) (h2 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h3 : t = (@EMPTY B) => @lem4333417 A B s t h1 h2) (fun h3 : False => @lem4331199 B t h2)). Qed.
Lemma lem4333465 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) (h2 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333464 A B s t h1 h2) (@lem4331199 B t h2)). Qed.
Lemma lem4333466 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY A) => @lem4333423 A s h1 h2 h3) (fun h4 : False => @lem4331175 A s h3)). Qed.
Lemma lem4333467 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333466 A s h1 h2 h3) (@lem4331175 A s h3)). Qed.
Lemma lem4333468 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (term6 A s) = False.
Proof. exact (prop_ext (fun h4 : term6 A s => @lem4333467 A s h1 h2 h3) (fun h4 : False => @lem4331167 A s h2)). Qed.
Lemma lem4333469 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333468 A s h1 h2 h3) (@lem4331167 A s h2)). Qed.
Lemma lem4333470 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (@FINITE A (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A (@EMPTY A) => @lem4333469 A s h1 h2 h3) (fun h4 : False => @lem4331151 A h1)). Qed.
Lemma lem4333471 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333470 A s h1 h2 h3) (@lem4331151 A h1)). Qed.
Lemma lem4333472 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem4333427 A s h1 h2) (fun h3 : False => @lem4331143 A s h1)). Qed.
Lemma lem4333473 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : False.
Proof. exact (EQ_MP (@lem4333472 A s h1 h2) (@lem4331143 A s h1)). Qed.
Lemma lem4333474 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : (term6 A s) = False.
Proof. exact (prop_ext (fun h3 : term6 A s => @lem4333473 A s h1 h2) (fun h3 : False => @lem4331139 A s h2)). Qed.
Lemma lem4333475 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : False.
Proof. exact (EQ_MP (@lem4333474 A s h1 h2) (@lem4331139 A s h2)). Qed.
Lemma lem4333476 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY A) => @lem4333433 A s h1 h2 h3) (fun h4 : False => @lem4331119 A s h3)). Qed.
Lemma lem4333477 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333476 A s h1 h2 h3) (@lem4331119 A s h3)). Qed.
Lemma lem4333478 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem4333477 A s h1 h2 h3) (fun h4 : False => @lem4331115 A s h1)). Qed.
Lemma lem4333479 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333478 A s h1 h2 h3) (@lem4331115 A s h1)). Qed.
Lemma lem4333480 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (term6 A s) = False.
Proof. exact (prop_ext (fun h4 : term6 A s => @lem4333479 A s h1 h2 h3) (fun h4 : False => @lem4331111 A s h2)). Qed.
Lemma lem4333481 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333480 A s h1 h2 h3) (@lem4331111 A s h2)). Qed.
Lemma lem4333482 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) (h2 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h3 : t = (@EMPTY B) => @lem4333435 A B s t h1 h2) (fun h3 : False => @lem4331419 B t h2)). Qed.
Lemma lem4333483 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) (h2 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333482 A B s t h1 h2) (@lem4331419 B t h2)). Qed.
Lemma lem4333484 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY A) => @lem4333439 A B t s h1 h2 h3) (fun h4 : False => @lem4331399 A s h3)). Qed.
Lemma lem4333485 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333484 A B t s h1 h2 h3) (@lem4331399 A s h3)). Qed.
Lemma lem4333486 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : (@FINITE A (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A (@EMPTY A) => @lem4333485 A B t s h1 h2 h3) (fun h4 : False => @lem4331383 A h1)). Qed.
Lemma lem4333487 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333486 A B t s h1 h2 h3) (@lem4331383 A h1)). Qed.
Lemma lem4333488 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : t = (@EMPTY B) => @lem4333443 A B s t h1 h2 h3) (fun h4 : False => @lem4331355 B t h3)). Qed.
Lemma lem4333489 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333488 A B s t h1 h2 h3) (@lem4331355 B t h3)). Qed.
Lemma lem4333490 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : (@FINITE B (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE B (@EMPTY B) => @lem4333489 A B s t h1 h2 h3) (fun h4 : False => @lem4331343 B h1)). Qed.
Lemma lem4333491 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333490 A B s t h1 h2 h3) (@lem4331343 B h1)). Qed.
Lemma lem4333492 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term15 A B s t) (h2 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h3 : s = (@EMPTY A) => @lem4333445 A B t s h1 h2) (fun h3 : False => @lem4331335 A s h2)). Qed.
Lemma lem4333493 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term15 A B s t) (h2 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333492 A B t s h1 h2) (@lem4331335 A s h2)). Qed.
Lemma lem4333494 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (@FINITE B t) = False.
Proof. exact (prop_ext (fun h4 : @FINITE B t => @lem4333451 B t h1 h2 h3) (fun h4 : False => @lem4331315 B t h1)). Qed.
Lemma lem4333495 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333494 B t h1 h2 h3) (@lem4331315 B t h1)). Qed.
Lemma lem4333496 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : t = (@EMPTY B) => @lem4333495 B t h1 h2 h3) (fun h4 : False => @lem4331311 B t h3)). Qed.
Lemma lem4333497 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333496 B t h1 h2 h3) (@lem4331311 B t h3)). Qed.
Lemma lem4333498 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (term6 B t) = False.
Proof. exact (prop_ext (fun h4 : term6 B t => @lem4333497 B t h1 h2 h3) (fun h4 : False => @lem4331307 B t h2)). Qed.
Lemma lem4333499 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333498 B t h1 h2 h3) (@lem4331307 B t h2)). Qed.
Lemma lem4333500 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : t = (@EMPTY B) => @lem4333457 B t h1 h2 h3) (fun h4 : False => @lem4331283 B t h3)). Qed.
Lemma lem4333501 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333500 B t h1 h2 h3) (@lem4331283 B t h3)). Qed.
Lemma lem4333502 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (term6 B t) = False.
Proof. exact (prop_ext (fun h4 : term6 B t => @lem4333501 B t h1 h2 h3) (fun h4 : False => @lem4331279 B t h2)). Qed.
Lemma lem4333503 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333502 B t h1 h2 h3) (@lem4331279 B t h2)). Qed.
Lemma lem4333504 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : (@FINITE B (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE B (@EMPTY B) => @lem4333503 B t h1 h2 h3) (fun h4 : False => @lem4331267 B h1)). Qed.
Lemma lem4333505 {B : Type'} (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333504 B t h1 h2 h3) (@lem4331267 B h1)). Qed.
Lemma lem4333506 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) : (@FINITE B t) = False.
Proof. exact (prop_ext (fun h3 : @FINITE B t => @lem4333461 B t h1 h2) (fun h3 : False => @lem4331259 B t h1)). Qed.
Lemma lem4333507 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) : False.
Proof. exact (EQ_MP (@lem4333506 B t h1 h2) (@lem4331259 B t h1)). Qed.
Lemma lem4333508 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) : (term6 B t) = False.
Proof. exact (prop_ext (fun h3 : term6 B t => @lem4333507 B t h1 h2) (fun h3 : False => @lem4331251 B t h2)). Qed.
Lemma lem4333509 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) (h2 : term6 B t) : False.
Proof. exact (EQ_MP (@lem4333508 B t h1 h2) (@lem4331251 B t h2)). Qed.
Lemma lem4333510 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term81 A B s t) (h2 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h3 : s = (@EMPTY A) => @lem4333463 A B t s h1 h2) (fun h3 : False => @lem4331231 A s h2)). Qed.
Lemma lem4333511 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term81 A B s t) (h2 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333510 A B t s h1 h2) (@lem4331231 A s h2)). Qed.
Lemma lem4333512 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) (h2 : t = (@EMPTY B)) : (t = (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h3 : t = (@EMPTY B) => @lem4333465 A B s t h1 h2) (fun h3 : False => @lem4331199 B t h2)). Qed.
Lemma lem4333513 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s t) (h2 : t = (@EMPTY B)) : False.
Proof. exact (EQ_MP (@lem4333512 A B s t h1 h2) (@lem4331199 B t h2)). Qed.
Lemma lem4333514 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY A) => @lem4333471 A s h1 h2 h3) (fun h4 : False => @lem4331175 A s h3)). Qed.
Lemma lem4333515 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333514 A s h1 h2 h3) (@lem4331175 A s h3)). Qed.
Lemma lem4333516 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (term6 A s) = False.
Proof. exact (prop_ext (fun h4 : term6 A s => @lem4333515 A s h1 h2 h3) (fun h4 : False => @lem4331167 A s h2)). Qed.
Lemma lem4333517 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333516 A s h1 h2 h3) (@lem4331167 A s h2)). Qed.
Lemma lem4333518 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (@FINITE A (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A (@EMPTY A) => @lem4333517 A s h1 h2 h3) (fun h4 : False => @lem4331151 A h1)). Qed.
Lemma lem4333519 {A : Type'} (s : A -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333518 A s h1 h2 h3) (@lem4331151 A h1)). Qed.
Lemma lem4333520 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem4333475 A s h1 h2) (fun h3 : False => @lem4331143 A s h1)). Qed.
Lemma lem4333521 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : False.
Proof. exact (EQ_MP (@lem4333520 A s h1 h2) (@lem4331143 A s h1)). Qed.
Lemma lem4333522 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : (term6 A s) = False.
Proof. exact (prop_ext (fun h3 : term6 A s => @lem4333521 A s h1 h2) (fun h3 : False => @lem4331139 A s h2)). Qed.
Lemma lem4333523 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : False.
Proof. exact (EQ_MP (@lem4333522 A s h1 h2) (@lem4331139 A s h2)). Qed.
Lemma lem4333524 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY A) => @lem4333481 A s h1 h2 h3) (fun h4 : False => @lem4331119 A s h3)). Qed.
Lemma lem4333525 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333524 A s h1 h2 h3) (@lem4331119 A s h3)). Qed.
Lemma lem4333526 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem4333525 A s h1 h2 h3) (fun h4 : False => @lem4331115 A s h1)). Qed.
Lemma lem4333527 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333526 A s h1 h2 h3) (@lem4331115 A s h1)). Qed.
Lemma lem4333528 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : (term6 A s) = False.
Proof. exact (prop_ext (fun h4 : term6 A s => @lem4333527 A s h1 h2 h3) (fun h4 : False => @lem4331111 A s h2)). Qed.
Lemma lem4333529 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4333528 A s h1 h2 h3) (@lem4331111 A s h2)). Qed.
Lemma lem4333530 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term22 A B s t) (h2 : term55 A B s t) : False.
Proof. exact (or_elim (@lem4331087 A B s t h2) (fun h0 : t = (@EMPTY B) => @lem4333483 A B s t h1 h0) (fun h0 : term52 A B s t => @lem4333357 A B s t h0 h1)). Qed.
Lemma lem4333531 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term22 A B s t) (h3 : term77 A B s t) : False.
Proof. exact (or_elim (@lem4331073 A B s t h3) (fun h0 : s = (@EMPTY A) => @lem4333487 A B t s h1 h2 h0) (fun h0 : term55 A B s t => @lem4333530 A B s t h2 h0)). Qed.
Lemma lem4333532 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : term55 A B s t) : False.
Proof. exact (or_elim (@lem4331079 A B s t h3) (fun h0 : t = (@EMPTY B) => @lem4333491 A B s t h1 h2 h0) (fun h0 : term52 A B s t => @lem4333202 A B s t h0 h2)). Qed.
Lemma lem4333533 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term15 A B s t) (h3 : term77 A B s t) : False.
Proof. exact (or_elim (@lem4331073 A B s t h3) (fun h0 : s = (@EMPTY A) => @lem4333493 A B t s h2 h0) (fun h0 : term55 A B s t => @lem4333532 A B s t h1 h2 h0)). Qed.
Lemma lem4333534 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : @FINITE B (@EMPTY B)) (h3 : term77 A B s t) : False.
Proof. exact (or_elim (@lem4331072 A B s t h3) (fun h0 : term15 A B s t => @lem4333533 A B s t h2 h0 h3) (fun h0 : term22 A B s t => @lem4333531 A B s t h1 h0 h3)). Qed.
Lemma lem4333535 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : term81 A B s t) (h4 : t = (@EMPTY B)) : False.
Proof. exact (or_elim (@lem4331053 A B s t h3) (fun h0 : s = (@EMPTY A) => @lem4333505 B t h1 h2 h4) (fun h0 : @FINITE B t => @lem4333499 B t h0 h2 h4)). Qed.
Lemma lem4333536 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term6 B t) (h2 : term81 A B s t) : False.
Proof. exact (or_elim (@lem4331053 A B s t h2) (fun h0 : s = (@EMPTY A) => @lem4333511 A B t s h2 h0) (fun h0 : @FINITE B t => @lem4333509 B t h0 h1)). Qed.
Lemma lem4333537 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B (@EMPTY B)) (h2 : term6 B t) (h3 : term81 A B s t) : False.
Proof. exact (or_elim (@lem4331052 A B s t h3) (fun h0 : @FINITE A s => @lem4333536 A B s t h2 h3) (fun h0 : t = (@EMPTY B) => @lem4333535 A B s t h1 h2 h3 h0)). Qed.
Lemma lem4333538 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : term81 A B s t) (h4 : t = (@EMPTY B)) : False.
Proof. exact (or_elim (@lem4331053 A B s t h3) (fun h0 : s = (@EMPTY A) => @lem4333519 A s h1 h2 h0) (fun h0 : @FINITE B t => @lem4333513 A B s t h3 h4)). Qed.
Lemma lem4333539 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) (h3 : term81 A B s t) : False.
Proof. exact (or_elim (@lem4331053 A B s t h3) (fun h0 : s = (@EMPTY A) => @lem4333529 A s h1 h2 h0) (fun h0 : @FINITE B t => @lem4333523 A s h1 h2)). Qed.
Lemma lem4333540 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : term6 A s) (h3 : term81 A B s t) : False.
Proof. exact (or_elim (@lem4331052 A B s t h3) (fun h0 : @FINITE A s => @lem4333539 A B s t h0 h2 h3) (fun h0 : t = (@EMPTY B) => @lem4333538 A B s t h1 h2 h3 h0)). Qed.
Lemma lem4333541 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : @FINITE B (@EMPTY B)) (h3 : term81 A B s t) : False.
Proof. exact (or_elim (@lem4331056 A B s t h3) (fun h0 : term6 A s => @lem4333540 A B s t h1 h0 h3) (fun h0 : term6 B t => @lem4333537 A B s t h2 h0 h3)). Qed.
Lemma lem4333542 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : @FINITE B (@EMPTY B)) (h3 : term85 A B s t) : False.
Proof. exact (or_elim (@lem4331047 A B s t h3) (fun h0 : term81 A B s t => @lem4333541 A B s t h1 h2 h0) (fun h0 : term77 A B s t => @lem4333534 A B s t h1 h2 h0)). Qed.
Lemma lem4333543 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : @FINITE B (@EMPTY B)) (h3 : term85 A B s t) : (term85 A B s t) = False.
Proof. exact (prop_ext (fun h4 : term85 A B s t => @lem4333542 A B s t h1 h2 h3) (fun h4 : False => @lem4331047 A B s t h3)). Qed.
Lemma lem4333544 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : @FINITE B (@EMPTY B)) (h3 : term85 A B s t) : False.
Proof. exact (EQ_MP (@lem4333543 A B s t h1 h2 h3) (@lem4331047 A B s t h3)). Qed.
Lemma lem4333545 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : @FINITE B (@EMPTY B)) (h3 : term85 A B s t) : (@FINITE B (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE B (@EMPTY B) => @lem4333544 A B s t h1 h2 h3) (fun h4 : False => @lem4330921 B h2)). Qed.
Lemma lem4333546 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : @FINITE B (@EMPTY B)) (h3 : term85 A B s t) : False.
Proof. exact (EQ_MP (@lem4333545 A B s t h1 h2 h3) (@lem4330921 B h2)). Qed.
Lemma lem4333547 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : @FINITE B (@EMPTY B)) (h3 : term85 A B s t) : (@FINITE A (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A (@EMPTY A) => @lem4333546 A B s t h1 h2 h3) (fun h4 : False => @lem4330917 A h1)). Qed.
Lemma lem4333548 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A (@EMPTY A)) (h2 : @FINITE B (@EMPTY B)) (h3 : term85 A B s t) : False.
Proof. exact (EQ_MP (@lem4333547 A B s t h1 h2 h3) (@lem4330917 A h1)). Qed.
Lemma lem4333549 {A B : Type'} (s : A -> Prop) (h1 : term95 A B s) (h2 : @FINITE A (@EMPTY A)) (h3 : @FINITE B (@EMPTY B)) : False.
Proof. exact (ex_elim (@lem4330912 A B s h1) (fun t : B -> Prop => fun h0 : term94 A B s t => @lem4333548 A B s t h2 h3 h0)). Qed.
Lemma lem4333550 {A B : Type'} (h1 : @FINITE A (@EMPTY A)) (h2 : @FINITE B (@EMPTY B)) (h3 : term35 A B) : False.
Proof. exact (ex_elim (@lem4330899 A B h3) (fun s : A -> Prop => fun h0 : term100 A B s => @lem4333549 A B s h0 h1 h2)). Qed.
Lemma lem4333551 {A B : Type'} (h1 : @FINITE A (@EMPTY A)) (h2 : @FINITE B (@EMPTY B)) (h3 : term35 A B) : (@FINITE B (@EMPTY B)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE B (@EMPTY B) => @lem4333550 A B h1 h2 h3) (fun h4 : False => @lem4330911 B h2)). Qed.
Lemma lem4333552 {A B : Type'} (h1 : @FINITE A (@EMPTY A)) (h2 : @FINITE B (@EMPTY B)) (h3 : term35 A B) : False.
Proof. exact (EQ_MP (@lem4333551 A B h1 h2 h3) (@lem4330911 B h2)). Qed.
Lemma lem4333553 {A B : Type'} (h1 : @FINITE A (@EMPTY A)) (h2 : @FINITE B (@EMPTY B)) (h3 : term35 A B) : (@FINITE A (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A (@EMPTY A) => @lem4333552 A B h1 h2 h3) (fun h4 : False => @lem4330905 A h1)). Qed.
Lemma lem4333554 {A B : Type'} (h1 : @FINITE A (@EMPTY A)) (h2 : @FINITE B (@EMPTY B)) (h3 : term35 A B) : False.
Proof. exact (EQ_MP (@lem4333553 A B h1 h2 h3) (@lem4330905 A h1)). Qed.
Lemma lem4333555 {A B : Type'} (h1 : @FINITE A (@EMPTY A)) (h2 : term35 A B) : term40 B.
Proof. exact (fun h0 : @FINITE B (@EMPTY B) => @lem4333554 A B h1 h0 h2). Qed.
Lemma lem4333556 {B : Type'} : (term40 B) = (term41 B).
Proof. exact (@lem69 (@FINITE B (@EMPTY B))). Qed.
Lemma lem4333557 {A B : Type'} (h1 : @FINITE A (@EMPTY A)) (h2 : term35 A B) : term41 B.
Proof. exact (EQ_MP (@lem4333556 B) (@lem4333555 A B h1 h2)). Qed.
Lemma lem4333558 {A B : Type'} (h1 : term35 A B) : term44 A B.
Proof. exact (fun h0 : @FINITE A (@EMPTY A) => @lem4333557 A B h0 h1). Qed.
Lemma lem4333559 {A B : Type'} : term46 A B.
Proof. exact (fun h0 : term35 A B => @lem4333558 A B h0). Qed.
Lemma lem4333560 {A B : Type'} : term36 A B.
Proof. exact (EQ_MP (@lem4330468 A B) (@lem4333559 A B)). Qed.
Lemma lem4333562 {A B : Type'} : term36 A B.
Proof. exact (@lem4330340 A B (@lem4333560 A B)). Qed.
Lemma lem4333563 {A B : Type'} (h1 : term35 A B) : term43 A B.
Proof. exact (@lem4333562 A B (@lem4330320 A B h1)). Qed.
Lemma lem4333564 {A B : Type'} (h1 : term35 A B) : term40 B.
Proof. exact (@lem4333563 A B h1 (@lem4330321 A)). Qed.
Lemma lem4333565 {A B : Type'} (h1 : term35 A B) : False.
Proof. exact (@lem4333564 A B h1 (@lem4330322 B)). Qed.
Lemma lem4333566 {A B : Type'} (h1 : term35 A B) : (term35 A B) = False.
Proof. exact (prop_ext (fun h2 : term35 A B => @lem4333565 A B h1) (fun h2 : False => @lem4330320 A B h1)). Qed.
Lemma lem4333567 {A B : Type'} (h1 : term35 A B) : False.
Proof. exact (EQ_MP (@lem4333566 A B h1) (@lem4330320 A B h1)). Qed.
Lemma lem4333568 {A B : Type'} : term34 A B.
Proof. exact (fun h0 : term35 A B => @lem4333567 A B h0). Qed.
Lemma lem4333569 {A B : Type'} : term32 A B.
Proof. exact (EQ_MP (@lem4330319 A B) (@lem4333568 A B)). Qed.
Lemma lem4333570 {A B : Type'} : term31 A B.
Proof. exact (EQ_MP (@lem4330315 A B) (@lem4333569 A B)). Qed.
