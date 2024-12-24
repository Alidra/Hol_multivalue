Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_TRIPLED_THM_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import ETA_AX_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1823_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Lemma lem56323 {A B : Type'} (t : A -> B) : term0 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem56324 {A B : Type'} (t : A -> B) : (term0 A B t) = ((term1 A B t) = t).
Proof. exact (eq_refl (term0 A B t)). Qed.
Lemma lem56325 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (EQ_MP (@lem56324 A B t) (@lem56323 A B t)). Qed.
Lemma lem56336 {A : Type'} (t : A -> Prop) : (term2 A t) = t.
Proof. exact (@lem56325 A Prop t). Qed.
Lemma lem56337 {A : Type'} (P : A -> Prop) : (term2 A P) = P.
Proof. exact (@lem56336 A P). Qed.
Lemma lem56338 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem56339 {A : Type'} (P : A -> Prop) : (term3 A P) = (ex P).
Proof. exact (MK_COMB (@lem56338 A) (@lem56337 A P)). Qed.
Lemma lem56340 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem56341 {A : Type'} (P : A -> Prop) : (term4 A P) = (term5 A P).
Proof. exact (MK_COMB (@lem56340) (@lem56339 A P)). Qed.
Lemma lem56342 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56343 {A : Type'} (P : A -> Prop) : (term6 A P) = (term7 A P).
Proof. exact (MK_COMB (@lem56342) (@lem56341 A P)). Qed.
Lemma lem56348 {A : Type'} (P : A -> Prop) : (term8 A P) = (term8 A P).
Proof. exact (eq_refl (term8 A P)). Qed.
Lemma lem56349 {A : Type'} (P : A -> Prop) : ((term4 A P) = (term8 A P)) = ((term5 A P) = (term8 A P)).
Proof. exact (MK_COMB (@lem56343 A P) (@lem56348 A P)). Qed.
Lemma lem56352 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem56349 A P)). Qed.
Lemma lem56353 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem56354 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem56353 A) (@lem56352 A)). Qed.
Lemma lem56359 {A : Type'} : term12 A.
Proof. exact (EQ_MP (@lem56354 A) (@lem10660 A)). Qed.
Lemma lem56360 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term13 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem56361 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term13 _5106 _5107 P) = ((term14 _5106 _5107 P) = (term15 _5106 _5107 P)).
Proof. exact (eq_refl (term13 _5106 _5107 P)). Qed.
Lemma lem56363 {A : Type'} (P : A -> Prop) : term16 A P.
Proof. exact (@lem56359 A P). Qed.
Lemma lem56364 {A : Type'} (P : A -> Prop) : (term16 A P) = ((term5 A P) = (term8 A P)).
Proof. exact (eq_refl (term16 A P)). Qed.
Lemma lem56376 (p : Prop) : term17 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem56377 (p : Prop) : (term17 p) = (term18 p).
Proof. exact (eq_refl (term17 p)). Qed.
Lemma lem56378 (p : Prop) : term18 p.
Proof. exact (EQ_MP (@lem56377 p) (@lem56376 p)). Qed.
Lemma lem56379 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem56380 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem56391 (q : Prop) : (term19 q) = (term19 q).
Proof. exact (eq_refl (term19 q)). Qed.
Lemma lem56392 (q : Prop) (p : Prop) (h1 : p = True) : (term20 q p) = (term21 q).
Proof. exact (MK_COMB (@lem56391 q) (@lem56379 p h1)). Qed.
Lemma lem56393 (q : Prop) : (term21 q) = (term22 q).
Proof. exact (eq_refl (term21 q)). Qed.
Lemma lem56394 (q : Prop) (p : Prop) : (term23 q p) = (term23 q p).
Proof. exact (eq_refl (term23 q p)). Qed.
Lemma lem56395 (p : Prop) (q : Prop) : ((term20 q p) = (term21 q)) = ((term20 q p) = (term22 q)).
Proof. exact (MK_COMB (@lem56394 q p) (@lem56393 q)). Qed.
Lemma lem56396 (p : Prop) (q : Prop) : (term20 q p) = (term24 p q).
Proof. exact (eq_refl (term20 q p)). Qed.
Lemma lem56397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56398 (p : Prop) (q : Prop) : (term23 q p) = (term25 p q).
Proof. exact (MK_COMB (@lem56397) (@lem56396 p q)). Qed.
Lemma lem56399 (q : Prop) : (term22 q) = (term22 q).
Proof. exact (eq_refl (term22 q)). Qed.
Lemma lem56400 (p : Prop) (q : Prop) : ((term20 q p) = (term22 q)) = ((term24 p q) = (term22 q)).
Proof. exact (MK_COMB (@lem56398 p q) (@lem56399 q)). Qed.
Lemma lem56401 (p : Prop) (q : Prop) : ((term20 q p) = (term21 q)) = ((term24 p q) = (term22 q)).
Proof. exact (TRANS (@lem56395 p q) (@lem56400 p q)). Qed.
Lemma lem56402 (q : Prop) (p : Prop) (h1 : p = True) : (term24 p q) = (term22 q).
Proof. exact (EQ_MP (@lem56401 p q) (@lem56392 q p h1)). Qed.
Lemma lem56403 (q : Prop) (p : Prop) (h1 : p = True) : (term22 q) = (term24 p q).
Proof. exact (SYM (@lem56402 q p h1)). Qed.
Lemma lem56404 (q : Prop) : (term19 q) = (term19 q).
Proof. exact (eq_refl (term19 q)). Qed.
Lemma lem56405 (q : Prop) (p : Prop) (h1 : p = False) : (term20 q p) = (term26 q).
Proof. exact (MK_COMB (@lem56404 q) (@lem56380 p h1)). Qed.
Lemma lem56406 (q : Prop) : (term26 q) = (term27 q).
Proof. exact (eq_refl (term26 q)). Qed.
Lemma lem56407 (q : Prop) (p : Prop) : (term23 q p) = (term23 q p).
Proof. exact (eq_refl (term23 q p)). Qed.
Lemma lem56408 (p : Prop) (q : Prop) : ((term20 q p) = (term26 q)) = ((term20 q p) = (term27 q)).
Proof. exact (MK_COMB (@lem56407 q p) (@lem56406 q)). Qed.
Lemma lem56409 (p : Prop) (q : Prop) : (term20 q p) = (term24 p q).
Proof. exact (eq_refl (term20 q p)). Qed.
Lemma lem56410 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56411 (p : Prop) (q : Prop) : (term23 q p) = (term25 p q).
Proof. exact (MK_COMB (@lem56410) (@lem56409 p q)). Qed.
Lemma lem56412 (q : Prop) : (term27 q) = (term27 q).
Proof. exact (eq_refl (term27 q)). Qed.
Lemma lem56413 (p : Prop) (q : Prop) : ((term20 q p) = (term27 q)) = ((term24 p q) = (term27 q)).
Proof. exact (MK_COMB (@lem56411 p q) (@lem56412 q)). Qed.
Lemma lem56414 (p : Prop) (q : Prop) : ((term20 q p) = (term26 q)) = ((term24 p q) = (term27 q)).
Proof. exact (TRANS (@lem56408 p q) (@lem56413 p q)). Qed.
Lemma lem56415 (q : Prop) (p : Prop) (h1 : p = False) : (term24 p q) = (term27 q).
Proof. exact (EQ_MP (@lem56414 p q) (@lem56405 q p h1)). Qed.
Lemma lem56416 (q : Prop) (p : Prop) (h1 : p = False) : (term27 q) = (term24 p q).
Proof. exact (SYM (@lem56415 q p h1)). Qed.
Lemma lem56424 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem56425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56426 : term28 = (@eq Prop False).
Proof. exact (MK_COMB (@lem56425) (@lem56424)). Qed.
Lemma lem56427 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem56428 (q : Prop) : ((~ True) = (~ q)) = (False = (~ q)).
Proof. exact (MK_COMB (@lem56426) (@lem56427 q)). Qed.
Lemma lem56430 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem56431 (q : Prop) : (False = (~ q)) = (term29 q).
Proof. exact (@lem56430 (~ q)). Qed.
Lemma lem56433 (t : Prop) : (term29 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem56434 (q : Prop) : (term29 q) = q.
Proof. exact (@lem56433 q). Qed.
Lemma lem56435 (q : Prop) : (False = (~ q)) = q.
Proof. exact (TRANS (@lem56431 q) (@lem56434 q)). Qed.
Lemma lem56436 (q : Prop) : ((~ True) = (~ q)) = q.
Proof. exact (TRANS (@lem56428 q) (@lem56435 q)). Qed.
Lemma lem56437 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem56438 (q : Prop) : (term30 q) = (imp q).
Proof. exact (MK_COMB (@lem56437) (@lem56436 q)). Qed.
Lemma lem56440 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem56441 (q : Prop) : (True = q) = q.
Proof. exact (@lem56440 q). Qed.
Lemma lem56442 (q : Prop) : (term22 q) = (q -> q).
Proof. exact (MK_COMB (@lem56438 q) (@lem56441 q)). Qed.
Lemma lem56444 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem56445 (q : Prop) : (q -> q) = True.
Proof. exact (@lem56444 q). Qed.
Lemma lem56446 (q : Prop) : (term22 q) = True.
Proof. exact (TRANS (@lem56442 q) (@lem56445 q)). Qed.
Lemma lem56447 (q : Prop) : True = (term22 q).
Proof. exact (SYM (@lem56446 q)). Qed.
Lemma lem56448 (q : Prop) : term22 q.
Proof. exact (EQ_MP (@lem56447 q) (@lem0)). Qed.
Lemma lem56456 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem56457 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56458 : term31 = (@eq Prop True).
Proof. exact (MK_COMB (@lem56457) (@lem56456)). Qed.
Lemma lem56459 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem56460 (q : Prop) : ((~ False) = (~ q)) = (True = (~ q)).
Proof. exact (MK_COMB (@lem56458) (@lem56459 q)). Qed.
Lemma lem56462 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem56463 (q : Prop) : (True = (~ q)) = (~ q).
Proof. exact (@lem56462 (~ q)). Qed.
Lemma lem56464 (q : Prop) : ((~ False) = (~ q)) = (~ q).
Proof. exact (TRANS (@lem56460 q) (@lem56463 q)). Qed.
Lemma lem56465 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem56466 (q : Prop) : (term32 q) = (term33 q).
Proof. exact (MK_COMB (@lem56465) (@lem56464 q)). Qed.
Lemma lem56468 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem56469 (q : Prop) : (False = q) = (~ q).
Proof. exact (@lem56468 q). Qed.
Lemma lem56470 (q : Prop) : (term27 q) = (term34 q).
Proof. exact (MK_COMB (@lem56466 q) (@lem56469 q)). Qed.
Lemma lem56472 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem56473 (q : Prop) : (term34 q) = True.
Proof. exact (@lem56472 (~ q)). Qed.
Lemma lem56474 (q : Prop) : (term27 q) = True.
Proof. exact (TRANS (@lem56470 q) (@lem56473 q)). Qed.
Lemma lem56475 (q : Prop) : True = (term27 q).
Proof. exact (SYM (@lem56474 q)). Qed.
Lemma lem56476 (q : Prop) : term27 q.
Proof. exact (EQ_MP (@lem56475 q) (@lem0)). Qed.
Lemma lem56477 (q : Prop) (p : Prop) (h1 : p = False) : term24 p q.
Proof. exact (EQ_MP (@lem56416 q p h1) (@lem56476 q)). Qed.
Lemma lem56478 (q : Prop) (p : Prop) (h1 : p = True) : term24 p q.
Proof. exact (EQ_MP (@lem56403 q p h1) (@lem56448 q)). Qed.
Lemma lem56481 (p : Prop) (q : Prop) : term24 p q.
Proof. exact (or_elim (@lem56378 p) (fun h0 : p = True => @lem56478 q p h0) (fun h0 : p = False => @lem56477 q p h0)). Qed.
Lemma lem56482 (p : Prop) (q : Prop) (h1 : term24 p q) : term24 p q.
Proof. exact (h1). Qed.
Lemma lem56483 (p : Prop) (q : Prop) (h1 : (~ p) = (~ q)) : (~ p) = (~ q).
Proof. exact (h1). Qed.
Lemma lem56484 (p : Prop) (q : Prop) (h1 : (~ p) = (~ q)) (h2 : term24 p q) : p = q.
Proof. exact (@lem56482 p q h2 (@lem56483 p q h1)). Qed.
Lemma lem56485 (p : Prop) (q : Prop) (h1 : (~ p) = (~ q)) : term35 p q.
Proof. exact (fun h0 : term24 p q => @lem56484 p q h1 h0). Qed.
Lemma lem56486 (p : Prop) (q : Prop) (h1 : term24 p q) : term24 p q.
Proof. exact (h1). Qed.
Lemma lem56487 (p : Prop) (q : Prop) (h1 : (~ p) = (~ q)) (h2 : term24 p q) : p = q.
Proof. exact (@lem56485 p q h1 (@lem56486 p q h2)). Qed.
Lemma lem56488 (p : Prop) (q : Prop) (h1 : term24 p q) : term24 p q.
Proof. exact (fun h0 : (~ p) = (~ q) => @lem56487 p q h0 h1). Qed.
Lemma lem56489 (p : Prop) (q : Prop) : term36 p q.
Proof. exact (fun h0 : term24 p q => @lem56488 p q h0). Qed.
Lemma lem56492 (p : Prop) (q : Prop) : term24 p q.
Proof. exact (@lem56489 p q (@lem56481 p q)). Qed.
Lemma lem56493 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : term37 _5851 _5852 _5853 P.
Proof. exact (@lem56492 (term38 _5851 _5852 _5853 P) (term39 _5851 _5852 _5853 P)). Qed.
Lemma lem56497 {A : Type'} (P : A -> Prop) : (term5 A P) = (term8 A P).
Proof. exact (EQ_MP (@lem56364 A P) (@lem56363 A P)). Qed.
Lemma lem56498 {_5851 _5852 _5853 : Type'} (P : type1227 _5851 _5852 _5853) : (term40 _5851 _5852 _5853 P) = (term41 _5851 _5852 _5853 P).
Proof. exact (@lem56497 (type1659 _5851 _5852 _5853) P). Qed.
Lemma lem56499 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term42 _5851 _5852 _5853 P) = (term43 _5851 _5852 _5853 P).
Proof. exact (@lem56498 _5851 _5852 _5853 (term44 _5851 _5852 _5853 P)). Qed.
Lemma lem56505 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term14 _5106 _5107 P) = (term15 _5106 _5107 P).
Proof. exact (EQ_MP (@lem56361 _5106 _5107 P) (@lem56360 _5106 _5107 P)). Qed.
Lemma lem56506 {_5851 _5852 _5853 : Type'} (P : type1227 _5851 _5852 _5853) : (term45 _5851 _5852 _5853 P) = (term46 _5851 _5852 _5853 P).
Proof. exact (@lem56505 (prod _5852 _5851) _5853 P). Qed.
Lemma lem56507 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term47 _5851 _5852 _5853 P) = (term48 _5851 _5852 _5853 P).
Proof. exact (@lem56506 _5851 _5852 _5853 (term49 _5851 _5852 _5853 P)). Qed.
Lemma lem56508 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : type1659 _5851 _5852 _5853) : (term50 _5851 _5852 _5853 P x) = (term51 _5851 _5852 _5853 P x).
Proof. exact (eq_refl (term50 _5851 _5852 _5853 P x)). Qed.
Lemma lem56509 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term52 _5851 _5852 _5853 P) = (term49 _5851 _5852 _5853 P).
Proof. exact (fun_ext (fun x : type1659 _5851 _5852 _5853 => @lem56508 _5851 _5852 _5853 P x)). Qed.
Lemma lem56510 {_5851 _5852 _5853 : Type'} : (@all (prod _5853 (prod _5852 _5851))) = (@all (prod _5853 (prod _5852 _5851))).
Proof. exact (eq_refl (@all (prod _5853 (prod _5852 _5851)))). Qed.
Lemma lem56511 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term47 _5851 _5852 _5853 P) = (term43 _5851 _5852 _5853 P).
Proof. exact (MK_COMB (@lem56510 _5851 _5852 _5853) (@lem56509 _5851 _5852 _5853 P)). Qed.
Lemma lem56512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56513 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term53 _5851 _5852 _5853 P) = (term54 _5851 _5852 _5853 P).
Proof. exact (MK_COMB (@lem56512) (@lem56511 _5851 _5852 _5853 P)). Qed.
Lemma lem56514 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) (p2 : prod _5852 _5851) : (term55 _5851 _5852 _5853 P p1 p2) = (term56 _5851 _5852 _5853 P p1 p2).
Proof. exact (eq_refl (term55 _5851 _5852 _5853 P p1 p2)). Qed.
Lemma lem56515 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) : (term57 _5851 _5852 _5853 P p1) = (term58 _5851 _5852 _5853 P p1).
Proof. exact (fun_ext (fun p2 : prod _5852 _5851 => @lem56514 _5851 _5852 _5853 P p1 p2)). Qed.
Lemma lem56516 {_5851 _5852 : Type'} : (@all (prod _5852 _5851)) = (@all (prod _5852 _5851)).
Proof. exact (eq_refl (@all (prod _5852 _5851))). Qed.
Lemma lem56517 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) : (term59 _5851 _5852 _5853 P p1) = (term60 _5851 _5852 _5853 P p1).
Proof. exact (MK_COMB (@lem56516 _5851 _5852) (@lem56515 _5851 _5852 _5853 P p1)). Qed.
Lemma lem56518 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term61 _5851 _5852 _5853 P) = (term62 _5851 _5852 _5853 P).
Proof. exact (fun_ext (fun p1 : _5853 => @lem56517 _5851 _5852 _5853 P p1)). Qed.
Lemma lem56519 {_5853 : Type'} : (@all _5853) = (@all _5853).
Proof. exact (eq_refl (@all _5853)). Qed.
Lemma lem56520 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term48 _5851 _5852 _5853 P) = (term63 _5851 _5852 _5853 P).
Proof. exact (MK_COMB (@lem56519 _5853) (@lem56518 _5851 _5852 _5853 P)). Qed.
Lemma lem56521 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : ((term47 _5851 _5852 _5853 P) = (term48 _5851 _5852 _5853 P)) = ((term43 _5851 _5852 _5853 P) = (term63 _5851 _5852 _5853 P)).
Proof. exact (MK_COMB (@lem56513 _5851 _5852 _5853 P) (@lem56520 _5851 _5852 _5853 P)). Qed.
Lemma lem56522 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term43 _5851 _5852 _5853 P) = (term63 _5851 _5852 _5853 P).
Proof. exact (EQ_MP (@lem56521 _5851 _5852 _5853 P) (@lem56507 _5851 _5852 _5853 P)). Qed.
Lemma lem56529 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term42 _5851 _5852 _5853 P) = (term63 _5851 _5852 _5853 P).
Proof. exact (TRANS (@lem56499 _5851 _5852 _5853 P) (@lem56522 _5851 _5852 _5853 P)). Qed.
Lemma lem56535 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term14 _5106 _5107 P) = (term15 _5106 _5107 P).
Proof. exact (EQ_MP (@lem56361 _5106 _5107 P) (@lem56360 _5106 _5107 P)). Qed.
Lemma lem56536 {_5851 _5852 : Type'} (P : type1223 _5851 _5852) : (term14 _5851 _5852 P) = (term15 _5851 _5852 P).
Proof. exact (@lem56535 _5851 _5852 P). Qed.
Lemma lem56537 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) : (term64 _5851 _5852 _5853 P p1) = (term65 _5851 _5852 _5853 P p1).
Proof. exact (@lem56536 _5851 _5852 (term58 _5851 _5852 _5853 P p1)). Qed.
Lemma lem56538 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) (p2 : prod _5852 _5851) : (term66 _5851 _5852 _5853 P p1 p2) = (term56 _5851 _5852 _5853 P p1 p2).
Proof. exact (eq_refl (term66 _5851 _5852 _5853 P p1 p2)). Qed.
Lemma lem56539 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) : (term67 _5851 _5852 _5853 P p1) = (term58 _5851 _5852 _5853 P p1).
Proof. exact (fun_ext (fun p2 : prod _5852 _5851 => @lem56538 _5851 _5852 _5853 P p1 p2)). Qed.
Lemma lem56540 {_5851 _5852 : Type'} : (@all (prod _5852 _5851)) = (@all (prod _5852 _5851)).
Proof. exact (eq_refl (@all (prod _5852 _5851))). Qed.
Lemma lem56541 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) : (term64 _5851 _5852 _5853 P p1) = (term60 _5851 _5852 _5853 P p1).
Proof. exact (MK_COMB (@lem56540 _5851 _5852) (@lem56539 _5851 _5852 _5853 P p1)). Qed.
Lemma lem56542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56543 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) : (term68 _5851 _5852 _5853 P p1) = (term69 _5851 _5852 _5853 P p1).
Proof. exact (MK_COMB (@lem56542) (@lem56541 _5851 _5852 _5853 P p1)). Qed.
Lemma lem56544 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) (p1' : _5852) (p2 : _5851) : (term70 _5851 _5852 _5853 P p1 p1' p2) = (term71 _5851 _5852 _5853 P p1 p1' p2).
Proof. exact (eq_refl (term70 _5851 _5852 _5853 P p1 p1' p2)). Qed.
Lemma lem56545 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) (p1' : _5852) : (term72 _5851 _5852 _5853 P p1 p1') = (term73 _5851 _5852 _5853 P p1 p1').
Proof. exact (fun_ext (fun p2 : _5851 => @lem56544 _5851 _5852 _5853 P p1 p1' p2)). Qed.
Lemma lem56546 {_5851 : Type'} : (@all _5851) = (@all _5851).
Proof. exact (eq_refl (@all _5851)). Qed.
Lemma lem56547 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) (p1' : _5852) : (term74 _5851 _5852 _5853 P p1 p1') = (term75 _5851 _5852 _5853 P p1 p1').
Proof. exact (MK_COMB (@lem56546 _5851) (@lem56545 _5851 _5852 _5853 P p1 p1')). Qed.
Lemma lem56548 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) : (term76 _5851 _5852 _5853 P p1) = (term77 _5851 _5852 _5853 P p1).
Proof. exact (fun_ext (fun p1' : _5852 => @lem56547 _5851 _5852 _5853 P p1 p1')). Qed.
Lemma lem56549 {_5852 : Type'} : (@all _5852) = (@all _5852).
Proof. exact (eq_refl (@all _5852)). Qed.
Lemma lem56550 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) : (term65 _5851 _5852 _5853 P p1) = (term78 _5851 _5852 _5853 P p1).
Proof. exact (MK_COMB (@lem56549 _5852) (@lem56548 _5851 _5852 _5853 P p1)). Qed.
Lemma lem56551 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) : ((term64 _5851 _5852 _5853 P p1) = (term65 _5851 _5852 _5853 P p1)) = ((term60 _5851 _5852 _5853 P p1) = (term78 _5851 _5852 _5853 P p1)).
Proof. exact (MK_COMB (@lem56543 _5851 _5852 _5853 P p1) (@lem56550 _5851 _5852 _5853 P p1)). Qed.
Lemma lem56552 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) : (term60 _5851 _5852 _5853 P p1) = (term78 _5851 _5852 _5853 P p1).
Proof. exact (EQ_MP (@lem56551 _5851 _5852 _5853 P p1) (@lem56537 _5851 _5852 _5853 P p1)). Qed.
Lemma lem56565 {_5851 _5852 _5853 : Type'} (a0 : _5853) (a1 : prod _5852 _5851) : a0 = (term79 _5851 _5852 _5853 a0 a1).
Proof. exact (@lem51128 _5853 (prod _5852 _5851) a0 a1). Qed.
Lemma lem56566 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : x = (term80 _5851 _5852 _5853 x y z).
Proof. exact (@lem56565 _5851 _5852 _5853 x (@pair _5852 _5851 y z)). Qed.
Lemma lem56567 {_5851 _5852 _5853 : Type'} (a0 : _5853) (a1 : prod _5852 _5851) : a1 = (term81 _5851 _5852 _5853 a0 a1).
Proof. exact (@lem51159 _5853 (prod _5852 _5851) a0 a1). Qed.
Lemma lem56568 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : (@pair _5852 _5851 y z) = (term82 _5851 _5852 _5853 x y z).
Proof. exact (@lem56567 _5851 _5852 _5853 x (@pair _5852 _5851 y z)). Qed.
Lemma lem56569 {_5853 : Type'} (x : _5853) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem56570 {_5853 : Type'} : (term83 _5853) = (term83 _5853).
Proof. exact (eq_refl (term83 _5853)). Qed.
Lemma lem56571 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : (term84 _5853 x) = (term85 _5851 _5852 _5853 x y z).
Proof. exact (MK_COMB (@lem56570 _5853) (@lem56566 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56572 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : (term85 _5851 _5852 _5853 x y z) = (term80 _5851 _5852 _5853 x y z).
Proof. exact (eq_refl (term85 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56573 {_5853 : Type'} (x : _5853) : (term86 _5853 x) = (term86 _5853 x).
Proof. exact (eq_refl (term86 _5853 x)). Qed.
Lemma lem56574 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : ((term84 _5853 x) = (term85 _5851 _5852 _5853 x y z)) = ((term84 _5853 x) = (term80 _5851 _5852 _5853 x y z)).
Proof. exact (MK_COMB (@lem56573 _5853 x) (@lem56572 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56575 {_5853 : Type'} (x : _5853) : (term84 _5853 x) = x.
Proof. exact (eq_refl (term84 _5853 x)). Qed.
Lemma lem56576 {_5853 : Type'} : (@eq _5853) = (@eq _5853).
Proof. exact (eq_refl (@eq _5853)). Qed.
Lemma lem56577 {_5853 : Type'} (x : _5853) : (term86 _5853 x) = (@eq _5853 x).
Proof. exact (MK_COMB (@lem56576 _5853) (@lem56575 _5853 x)). Qed.
Lemma lem56578 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : (term80 _5851 _5852 _5853 x y z) = (term80 _5851 _5852 _5853 x y z).
Proof. exact (eq_refl (term80 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56579 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : ((term84 _5853 x) = (term80 _5851 _5852 _5853 x y z)) = (x = (term80 _5851 _5852 _5853 x y z)).
Proof. exact (MK_COMB (@lem56577 _5853 x) (@lem56578 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56580 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : ((term84 _5853 x) = (term85 _5851 _5852 _5853 x y z)) = (x = (term80 _5851 _5852 _5853 x y z)).
Proof. exact (TRANS (@lem56574 _5851 _5852 _5853 x y z) (@lem56579 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56581 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : x = (term80 _5851 _5852 _5853 x y z).
Proof. exact (EQ_MP (@lem56580 _5851 _5852 _5853 x y z) (@lem56571 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56582 {_5853 : Type'} (x : _5853) : (@eq _5853 x) = (@eq _5853 x).
Proof. exact (eq_refl (@eq _5853 x)). Qed.
Lemma lem56583 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : (x = x) = (x = (term80 _5851 _5852 _5853 x y z)).
Proof. exact (MK_COMB (@lem56582 _5853 x) (@lem56581 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56584 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : x = (term80 _5851 _5852 _5853 x y z).
Proof. exact (EQ_MP (@lem56583 _5851 _5852 _5853 x y z) (@lem56569 _5853 x)). Qed.
Lemma lem56585 {_5851 _5852 : Type'} (a0 : _5852) (a1 : _5851) : a0 = (term87 _5851 _5852 a0 a1).
Proof. exact (@lem51128 _5852 _5851 a0 a1). Qed.
Lemma lem56586 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : y = (term87 _5851 _5852 y z).
Proof. exact (@lem56585 _5851 _5852 y z). Qed.
Lemma lem56587 {_5851 _5852 : Type'} (a0 : _5852) (a1 : _5851) : a1 = (term88 _5851 _5852 a0 a1).
Proof. exact (@lem51159 _5852 _5851 a0 a1). Qed.
Lemma lem56588 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : z = (term88 _5851 _5852 y z).
Proof. exact (@lem56587 _5851 _5852 y z). Qed.
Lemma lem56589 {_5852 : Type'} (y : _5852) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem56590 {_5852 : Type'} : (term83 _5852) = (term83 _5852).
Proof. exact (eq_refl (term83 _5852)). Qed.
Lemma lem56591 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : (term84 _5852 y) = (term89 _5851 _5852 y z).
Proof. exact (MK_COMB (@lem56590 _5852) (@lem56586 _5851 _5852 y z)). Qed.
Lemma lem56592 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : (term89 _5851 _5852 y z) = (term87 _5851 _5852 y z).
Proof. exact (eq_refl (term89 _5851 _5852 y z)). Qed.
Lemma lem56593 {_5852 : Type'} (y : _5852) : (term86 _5852 y) = (term86 _5852 y).
Proof. exact (eq_refl (term86 _5852 y)). Qed.
Lemma lem56594 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : ((term84 _5852 y) = (term89 _5851 _5852 y z)) = ((term84 _5852 y) = (term87 _5851 _5852 y z)).
Proof. exact (MK_COMB (@lem56593 _5852 y) (@lem56592 _5851 _5852 y z)). Qed.
Lemma lem56595 {_5852 : Type'} (y : _5852) : (term84 _5852 y) = y.
Proof. exact (eq_refl (term84 _5852 y)). Qed.
Lemma lem56596 {_5852 : Type'} : (@eq _5852) = (@eq _5852).
Proof. exact (eq_refl (@eq _5852)). Qed.
Lemma lem56597 {_5852 : Type'} (y : _5852) : (term86 _5852 y) = (@eq _5852 y).
Proof. exact (MK_COMB (@lem56596 _5852) (@lem56595 _5852 y)). Qed.
Lemma lem56598 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : (term87 _5851 _5852 y z) = (term87 _5851 _5852 y z).
Proof. exact (eq_refl (term87 _5851 _5852 y z)). Qed.
Lemma lem56599 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : ((term84 _5852 y) = (term87 _5851 _5852 y z)) = (y = (term87 _5851 _5852 y z)).
Proof. exact (MK_COMB (@lem56597 _5852 y) (@lem56598 _5851 _5852 y z)). Qed.
Lemma lem56600 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : ((term84 _5852 y) = (term89 _5851 _5852 y z)) = (y = (term87 _5851 _5852 y z)).
Proof. exact (TRANS (@lem56594 _5851 _5852 y z) (@lem56599 _5851 _5852 y z)). Qed.
Lemma lem56601 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : y = (term87 _5851 _5852 y z).
Proof. exact (EQ_MP (@lem56600 _5851 _5852 y z) (@lem56591 _5851 _5852 y z)). Qed.
Lemma lem56602 {_5852 : Type'} (y : _5852) : (@eq _5852 y) = (@eq _5852 y).
Proof. exact (eq_refl (@eq _5852 y)). Qed.
Lemma lem56603 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : (y = y) = (y = (term87 _5851 _5852 y z)).
Proof. exact (MK_COMB (@lem56602 _5852 y) (@lem56601 _5851 _5852 y z)). Qed.
Lemma lem56604 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : y = (term87 _5851 _5852 y z).
Proof. exact (EQ_MP (@lem56603 _5851 _5852 y z) (@lem56589 _5852 y)). Qed.
Lemma lem56605 {_5851 : Type'} (z : _5851) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem56606 {_5851 : Type'} : (term83 _5851) = (term83 _5851).
Proof. exact (eq_refl (term83 _5851)). Qed.
Lemma lem56607 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : (term84 _5851 z) = (term90 _5851 _5852 y z).
Proof. exact (MK_COMB (@lem56606 _5851) (@lem56588 _5851 _5852 y z)). Qed.
Lemma lem56608 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : (term90 _5851 _5852 y z) = (term88 _5851 _5852 y z).
Proof. exact (eq_refl (term90 _5851 _5852 y z)). Qed.
Lemma lem56609 {_5851 : Type'} (z : _5851) : (term86 _5851 z) = (term86 _5851 z).
Proof. exact (eq_refl (term86 _5851 z)). Qed.
Lemma lem56610 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : ((term84 _5851 z) = (term90 _5851 _5852 y z)) = ((term84 _5851 z) = (term88 _5851 _5852 y z)).
Proof. exact (MK_COMB (@lem56609 _5851 z) (@lem56608 _5851 _5852 y z)). Qed.
Lemma lem56611 {_5851 : Type'} (z : _5851) : (term84 _5851 z) = z.
Proof. exact (eq_refl (term84 _5851 z)). Qed.
Lemma lem56612 {_5851 : Type'} : (@eq _5851) = (@eq _5851).
Proof. exact (eq_refl (@eq _5851)). Qed.
Lemma lem56613 {_5851 : Type'} (z : _5851) : (term86 _5851 z) = (@eq _5851 z).
Proof. exact (MK_COMB (@lem56612 _5851) (@lem56611 _5851 z)). Qed.
Lemma lem56614 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : (term88 _5851 _5852 y z) = (term88 _5851 _5852 y z).
Proof. exact (eq_refl (term88 _5851 _5852 y z)). Qed.
Lemma lem56615 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : ((term84 _5851 z) = (term88 _5851 _5852 y z)) = (z = (term88 _5851 _5852 y z)).
Proof. exact (MK_COMB (@lem56613 _5851 z) (@lem56614 _5851 _5852 y z)). Qed.
Lemma lem56616 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : ((term84 _5851 z) = (term90 _5851 _5852 y z)) = (z = (term88 _5851 _5852 y z)).
Proof. exact (TRANS (@lem56610 _5851 _5852 y z) (@lem56615 _5851 _5852 y z)). Qed.
Lemma lem56617 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : z = (term88 _5851 _5852 y z).
Proof. exact (EQ_MP (@lem56616 _5851 _5852 y z) (@lem56607 _5851 _5852 y z)). Qed.
Lemma lem56618 {_5851 : Type'} (z : _5851) : (@eq _5851 z) = (@eq _5851 z).
Proof. exact (eq_refl (@eq _5851 z)). Qed.
Lemma lem56619 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : (z = z) = (z = (term88 _5851 _5852 y z)).
Proof. exact (MK_COMB (@lem56618 _5851 z) (@lem56617 _5851 _5852 y z)). Qed.
Lemma lem56620 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : z = (term88 _5851 _5852 y z).
Proof. exact (EQ_MP (@lem56619 _5851 _5852 y z) (@lem56605 _5851 z)). Qed.
Lemma lem56621 {_5851 _5852 : Type'} : (term91 _5851 _5852) = (term91 _5851 _5852).
Proof. exact (eq_refl (term91 _5851 _5852)). Qed.
Lemma lem56622 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : (term92 _5851 _5852 y z) = (term93 _5851 _5852 _5853 x y z).
Proof. exact (MK_COMB (@lem56621 _5851 _5852) (@lem56568 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56623 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : (term93 _5851 _5852 _5853 x y z) = (term94 _5851 _5852 _5853 x y z).
Proof. exact (eq_refl (term93 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56624 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : (term95 _5851 _5852 y z) = (term95 _5851 _5852 y z).
Proof. exact (eq_refl (term95 _5851 _5852 y z)). Qed.
Lemma lem56625 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : ((term92 _5851 _5852 y z) = (term93 _5851 _5852 _5853 x y z)) = ((term92 _5851 _5852 y z) = (term94 _5851 _5852 _5853 x y z)).
Proof. exact (MK_COMB (@lem56624 _5851 _5852 y z) (@lem56623 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56626 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : (term92 _5851 _5852 y z) = (term87 _5851 _5852 y z).
Proof. exact (eq_refl (term92 _5851 _5852 y z)). Qed.
Lemma lem56627 {_5852 : Type'} : (@eq _5852) = (@eq _5852).
Proof. exact (eq_refl (@eq _5852)). Qed.
Lemma lem56628 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : (term95 _5851 _5852 y z) = (term96 _5851 _5852 y z).
Proof. exact (MK_COMB (@lem56627 _5852) (@lem56626 _5851 _5852 y z)). Qed.
Lemma lem56629 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : (term94 _5851 _5852 _5853 x y z) = (term94 _5851 _5852 _5853 x y z).
Proof. exact (eq_refl (term94 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56630 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : ((term92 _5851 _5852 y z) = (term94 _5851 _5852 _5853 x y z)) = ((term87 _5851 _5852 y z) = (term94 _5851 _5852 _5853 x y z)).
Proof. exact (MK_COMB (@lem56628 _5851 _5852 y z) (@lem56629 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56631 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : ((term92 _5851 _5852 y z) = (term93 _5851 _5852 _5853 x y z)) = ((term87 _5851 _5852 y z) = (term94 _5851 _5852 _5853 x y z)).
Proof. exact (TRANS (@lem56625 _5851 _5852 _5853 x y z) (@lem56630 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56632 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : (term87 _5851 _5852 y z) = (term94 _5851 _5852 _5853 x y z).
Proof. exact (EQ_MP (@lem56631 _5851 _5852 _5853 x y z) (@lem56622 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56633 {_5852 : Type'} (y : _5852) : (@eq _5852 y) = (@eq _5852 y).
Proof. exact (eq_refl (@eq _5852 y)). Qed.
Lemma lem56634 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : (y = (term87 _5851 _5852 y z)) = (y = (term94 _5851 _5852 _5853 x y z)).
Proof. exact (MK_COMB (@lem56633 _5852 y) (@lem56632 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56635 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : y = (term94 _5851 _5852 _5853 x y z).
Proof. exact (EQ_MP (@lem56634 _5851 _5852 _5853 x y z) (@lem56604 _5851 _5852 y z)). Qed.
Lemma lem56636 {_5851 _5852 : Type'} : (term97 _5851 _5852) = (term97 _5851 _5852).
Proof. exact (eq_refl (term97 _5851 _5852)). Qed.
Lemma lem56637 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : (term98 _5851 _5852 y z) = (term99 _5851 _5852 _5853 x y z).
Proof. exact (MK_COMB (@lem56636 _5851 _5852) (@lem56568 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56638 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : (term99 _5851 _5852 _5853 x y z) = (term100 _5851 _5852 _5853 x y z).
Proof. exact (eq_refl (term99 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56639 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : (term101 _5851 _5852 y z) = (term101 _5851 _5852 y z).
Proof. exact (eq_refl (term101 _5851 _5852 y z)). Qed.
Lemma lem56640 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : ((term98 _5851 _5852 y z) = (term99 _5851 _5852 _5853 x y z)) = ((term98 _5851 _5852 y z) = (term100 _5851 _5852 _5853 x y z)).
Proof. exact (MK_COMB (@lem56639 _5851 _5852 y z) (@lem56638 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56641 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : (term98 _5851 _5852 y z) = (term88 _5851 _5852 y z).
Proof. exact (eq_refl (term98 _5851 _5852 y z)). Qed.
Lemma lem56642 {_5851 : Type'} : (@eq _5851) = (@eq _5851).
Proof. exact (eq_refl (@eq _5851)). Qed.
Lemma lem56643 {_5851 _5852 : Type'} (y : _5852) (z : _5851) : (term101 _5851 _5852 y z) = (term102 _5851 _5852 y z).
Proof. exact (MK_COMB (@lem56642 _5851) (@lem56641 _5851 _5852 y z)). Qed.
Lemma lem56644 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : (term100 _5851 _5852 _5853 x y z) = (term100 _5851 _5852 _5853 x y z).
Proof. exact (eq_refl (term100 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56645 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : ((term98 _5851 _5852 y z) = (term100 _5851 _5852 _5853 x y z)) = ((term88 _5851 _5852 y z) = (term100 _5851 _5852 _5853 x y z)).
Proof. exact (MK_COMB (@lem56643 _5851 _5852 y z) (@lem56644 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56646 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : ((term98 _5851 _5852 y z) = (term99 _5851 _5852 _5853 x y z)) = ((term88 _5851 _5852 y z) = (term100 _5851 _5852 _5853 x y z)).
Proof. exact (TRANS (@lem56640 _5851 _5852 _5853 x y z) (@lem56645 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56647 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : (term88 _5851 _5852 y z) = (term100 _5851 _5852 _5853 x y z).
Proof. exact (EQ_MP (@lem56646 _5851 _5852 _5853 x y z) (@lem56637 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56648 {_5851 : Type'} (z : _5851) : (@eq _5851 z) = (@eq _5851 z).
Proof. exact (eq_refl (@eq _5851 z)). Qed.
Lemma lem56649 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : (z = (term88 _5851 _5852 y z)) = (z = (term100 _5851 _5852 _5853 x y z)).
Proof. exact (MK_COMB (@lem56648 _5851 z) (@lem56647 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56650 {_5851 _5852 _5853 : Type'} (x : _5853) (y : _5852) (z : _5851) : z = (term100 _5851 _5852 _5853 x y z).
Proof. exact (EQ_MP (@lem56649 _5851 _5852 _5853 x y z) (@lem56620 _5851 _5852 y z)). Qed.
Lemma lem56651 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term103 _5851 _5852 _5853 P) = (term103 _5851 _5852 _5853 P).
Proof. exact (eq_refl (term103 _5851 _5852 _5853 P)). Qed.
Lemma lem56652 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term104 _5851 _5852 _5853 P x) = (term105 _5851 _5852 _5853 P x y z).
Proof. exact (MK_COMB (@lem56651 _5851 _5852 _5853 P) (@lem56584 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56653 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term105 _5851 _5852 _5853 P x y z) = (term106 _5851 _5852 _5853 P x y z).
Proof. exact (eq_refl (term105 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56654 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term107 _5851 _5852 _5853 P x) = (term107 _5851 _5852 _5853 P x).
Proof. exact (eq_refl (term107 _5851 _5852 _5853 P x)). Qed.
Lemma lem56655 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : ((term104 _5851 _5852 _5853 P x) = (term105 _5851 _5852 _5853 P x y z)) = ((term104 _5851 _5852 _5853 P x) = (term106 _5851 _5852 _5853 P x y z)).
Proof. exact (MK_COMB (@lem56654 _5851 _5852 _5853 P x) (@lem56653 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56656 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term104 _5851 _5852 _5853 P x) = (term108 _5851 _5852 _5853 P x).
Proof. exact (eq_refl (term104 _5851 _5852 _5853 P x)). Qed.
Lemma lem56657 {_5851 _5852 : Type'} : (@eq (_5852 -> _5851 -> Prop)) = (@eq (_5852 -> _5851 -> Prop)).
Proof. exact (eq_refl (@eq (_5852 -> _5851 -> Prop))). Qed.
Lemma lem56658 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term107 _5851 _5852 _5853 P x) = (term109 _5851 _5852 _5853 P x).
Proof. exact (MK_COMB (@lem56657 _5851 _5852) (@lem56656 _5851 _5852 _5853 P x)). Qed.
Lemma lem56659 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term106 _5851 _5852 _5853 P x y z) = (term106 _5851 _5852 _5853 P x y z).
Proof. exact (eq_refl (term106 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56660 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : ((term104 _5851 _5852 _5853 P x) = (term106 _5851 _5852 _5853 P x y z)) = ((term108 _5851 _5852 _5853 P x) = (term106 _5851 _5852 _5853 P x y z)).
Proof. exact (MK_COMB (@lem56658 _5851 _5852 _5853 P x) (@lem56659 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56661 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : ((term104 _5851 _5852 _5853 P x) = (term105 _5851 _5852 _5853 P x y z)) = ((term108 _5851 _5852 _5853 P x) = (term106 _5851 _5852 _5853 P x y z)).
Proof. exact (TRANS (@lem56655 _5851 _5852 _5853 P x y z) (@lem56660 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56662 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term108 _5851 _5852 _5853 P x) = (term106 _5851 _5852 _5853 P x y z).
Proof. exact (EQ_MP (@lem56661 _5851 _5852 _5853 P x y z) (@lem56652 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56663 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term110 _5851 _5852 _5853 P x y) = (term111 _5851 _5852 _5853 P x y z).
Proof. exact (MK_COMB (@lem56662 _5851 _5852 _5853 P x y z) (@lem56635 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56664 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term111 _5851 _5852 _5853 P x y z) = (term112 _5851 _5852 _5853 P x y z).
Proof. exact (eq_refl (term111 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56665 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) : (term113 _5851 _5852 _5853 P x y) = (term113 _5851 _5852 _5853 P x y).
Proof. exact (eq_refl (term113 _5851 _5852 _5853 P x y)). Qed.
Lemma lem56666 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : ((term110 _5851 _5852 _5853 P x y) = (term111 _5851 _5852 _5853 P x y z)) = ((term110 _5851 _5852 _5853 P x y) = (term112 _5851 _5852 _5853 P x y z)).
Proof. exact (MK_COMB (@lem56665 _5851 _5852 _5853 P x y) (@lem56664 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56667 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) : (term110 _5851 _5852 _5853 P x y) = (term114 _5851 _5852 _5853 P x y).
Proof. exact (eq_refl (term110 _5851 _5852 _5853 P x y)). Qed.
Lemma lem56668 {_5851 : Type'} : (@eq (_5851 -> Prop)) = (@eq (_5851 -> Prop)).
Proof. exact (eq_refl (@eq (_5851 -> Prop))). Qed.
Lemma lem56669 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) : (term113 _5851 _5852 _5853 P x y) = (term115 _5851 _5852 _5853 P x y).
Proof. exact (MK_COMB (@lem56668 _5851) (@lem56667 _5851 _5852 _5853 P x y)). Qed.
Lemma lem56670 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term112 _5851 _5852 _5853 P x y z) = (term112 _5851 _5852 _5853 P x y z).
Proof. exact (eq_refl (term112 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56671 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : ((term110 _5851 _5852 _5853 P x y) = (term112 _5851 _5852 _5853 P x y z)) = ((term114 _5851 _5852 _5853 P x y) = (term112 _5851 _5852 _5853 P x y z)).
Proof. exact (MK_COMB (@lem56669 _5851 _5852 _5853 P x y) (@lem56670 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56672 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : ((term110 _5851 _5852 _5853 P x y) = (term111 _5851 _5852 _5853 P x y z)) = ((term114 _5851 _5852 _5853 P x y) = (term112 _5851 _5852 _5853 P x y z)).
Proof. exact (TRANS (@lem56666 _5851 _5852 _5853 P x y z) (@lem56671 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56673 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term114 _5851 _5852 _5853 P x y) = (term112 _5851 _5852 _5853 P x y z).
Proof. exact (EQ_MP (@lem56672 _5851 _5852 _5853 P x y z) (@lem56663 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56674 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term116 _5851 _5852 _5853 P x y z) = (term117 _5851 _5852 _5853 P x y z).
Proof. exact (MK_COMB (@lem56673 _5851 _5852 _5853 P x y z) (@lem56650 _5851 _5852 _5853 x y z)). Qed.
Lemma lem56675 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term117 _5851 _5852 _5853 P x y z) = (term118 _5851 _5852 _5853 P x y z).
Proof. exact (eq_refl (term117 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56676 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term119 _5851 _5852 _5853 P x y z) = (term119 _5851 _5852 _5853 P x y z).
Proof. exact (eq_refl (term119 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56677 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : ((term116 _5851 _5852 _5853 P x y z) = (term117 _5851 _5852 _5853 P x y z)) = ((term116 _5851 _5852 _5853 P x y z) = (term118 _5851 _5852 _5853 P x y z)).
Proof. exact (MK_COMB (@lem56676 _5851 _5852 _5853 P x y z) (@lem56675 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56678 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term116 _5851 _5852 _5853 P x y z) = (P x y z).
Proof. exact (eq_refl (term116 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56679 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56680 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term119 _5851 _5852 _5853 P x y z) = (term120 _5851 _5852 _5853 P x y z).
Proof. exact (MK_COMB (@lem56679) (@lem56678 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56681 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term118 _5851 _5852 _5853 P x y z) = (term118 _5851 _5852 _5853 P x y z).
Proof. exact (eq_refl (term118 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56682 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : ((term116 _5851 _5852 _5853 P x y z) = (term118 _5851 _5852 _5853 P x y z)) = ((P x y z) = (term118 _5851 _5852 _5853 P x y z)).
Proof. exact (MK_COMB (@lem56680 _5851 _5852 _5853 P x y z) (@lem56681 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56683 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : ((term116 _5851 _5852 _5853 P x y z) = (term117 _5851 _5852 _5853 P x y z)) = ((P x y z) = (term118 _5851 _5852 _5853 P x y z)).
Proof. exact (TRANS (@lem56677 _5851 _5852 _5853 P x y z) (@lem56682 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56684 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (P x y z) = (term118 _5851 _5852 _5853 P x y z).
Proof. exact (EQ_MP (@lem56683 _5851 _5852 _5853 P x y z) (@lem56674 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56685 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term118 _5851 _5852 _5853 P x y z) = (P x y z).
Proof. exact (SYM (@lem56684 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56686 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term121 _5851 _5852 _5853 P x y z) = (term118 _5851 _5852 _5853 P x y z).
Proof. exact (eq_refl (term121 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56687 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term121 _5851 _5852 _5853 P x y z) = (P x y z).
Proof. exact (TRANS (@lem56686 _5851 _5852 _5853 P x y z) (@lem56685 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56688 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) : term122 _5851 _5852 _5853 P x y.
Proof. exact (fun z : _5851 => @lem56687 _5851 _5852 _5853 P x y z). Qed.
Lemma lem56689 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : term123 _5851 _5852 _5853 P x.
Proof. exact (fun y : _5852 => @lem56688 _5851 _5852 _5853 P x y). Qed.
Lemma lem56690 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : term124 _5851 _5852 _5853 P.
Proof. exact (fun x : _5853 => @lem56689 _5851 _5852 _5853 P x). Qed.
Lemma lem56691 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : term125 _5851 _5852 _5853 P.
Proof. exact (ex_intro (term126 _5851 _5852 _5853 P) (term127 _5851 _5852 _5853 P) (@lem56690 _5851 _5852 _5853 P)). Qed.
Lemma lem56693 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem56694 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem56693 Prop a b). Qed.
Lemma lem56695 {_5851 _5852 _5853 : Type'} (_1594 : type1227 _5851 _5852 _5853) (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : ((term128 _5851 _5852 _5853 _1594 x y z) = (P x y z)) = (term129 _5851 _5852 _5853 _1594 P x y z).
Proof. exact (@lem56694 (term128 _5851 _5852 _5853 _1594 x y z) (P x y z)). Qed.
Lemma lem56696 {_5851 _5852 _5853 : Type'} (_1594 : type1227 _5851 _5852 _5853) (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) : (term130 _5851 _5852 _5853 _1594 P x y) = (term131 _5851 _5852 _5853 _1594 P x y).
Proof. exact (fun_ext (fun z : _5851 => @lem56695 _5851 _5852 _5853 _1594 P x y z)). Qed.
Lemma lem56697 {_5851 : Type'} : (@all _5851) = (@all _5851).
Proof. exact (eq_refl (@all _5851)). Qed.
Lemma lem56698 {_5851 _5852 _5853 : Type'} (_1594 : type1227 _5851 _5852 _5853) (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) : (term132 _5851 _5852 _5853 _1594 P x y) = (term133 _5851 _5852 _5853 _1594 P x y).
Proof. exact (MK_COMB (@lem56697 _5851) (@lem56696 _5851 _5852 _5853 _1594 P x y)). Qed.
Lemma lem56699 {_5851 _5852 _5853 : Type'} (_1594 : type1227 _5851 _5852 _5853) (P : type1517 _5851 _5852 _5853) (x : _5853) : (term134 _5851 _5852 _5853 _1594 P x) = (term135 _5851 _5852 _5853 _1594 P x).
Proof. exact (fun_ext (fun y : _5852 => @lem56698 _5851 _5852 _5853 _1594 P x y)). Qed.
Lemma lem56700 {_5852 : Type'} : (@all _5852) = (@all _5852).
Proof. exact (eq_refl (@all _5852)). Qed.
Lemma lem56701 {_5851 _5852 _5853 : Type'} (_1594 : type1227 _5851 _5852 _5853) (P : type1517 _5851 _5852 _5853) (x : _5853) : (term136 _5851 _5852 _5853 _1594 P x) = (term137 _5851 _5852 _5853 _1594 P x).
Proof. exact (MK_COMB (@lem56700 _5852) (@lem56699 _5851 _5852 _5853 _1594 P x)). Qed.
Lemma lem56702 {_5851 _5852 _5853 : Type'} (_1594 : type1227 _5851 _5852 _5853) (P : type1517 _5851 _5852 _5853) : (term138 _5851 _5852 _5853 _1594 P) = (term139 _5851 _5852 _5853 _1594 P).
Proof. exact (fun_ext (fun x : _5853 => @lem56701 _5851 _5852 _5853 _1594 P x)). Qed.
Lemma lem56703 {_5853 : Type'} : (@all _5853) = (@all _5853).
Proof. exact (eq_refl (@all _5853)). Qed.
Lemma lem56704 {_5851 _5852 _5853 : Type'} (_1594 : type1227 _5851 _5852 _5853) (P : type1517 _5851 _5852 _5853) : (term140 _5851 _5852 _5853 _1594 P) = (term141 _5851 _5852 _5853 _1594 P).
Proof. exact (MK_COMB (@lem56703 _5853) (@lem56702 _5851 _5852 _5853 _1594 P)). Qed.
Lemma lem56705 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term126 _5851 _5852 _5853 P) = (term142 _5851 _5852 _5853 P).
Proof. exact (fun_ext (fun _1594 : type1227 _5851 _5852 _5853 => @lem56704 _5851 _5852 _5853 _1594 P)). Qed.
Lemma lem56706 {_5851 _5852 _5853 : Type'} : (@ex ((prod _5853 (prod _5852 _5851)) -> Prop)) = (@ex ((prod _5853 (prod _5852 _5851)) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5853 (prod _5852 _5851)) -> Prop))). Qed.
Lemma lem56707 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term125 _5851 _5852 _5853 P) = (term143 _5851 _5852 _5853 P).
Proof. exact (MK_COMB (@lem56706 _5851 _5852 _5853) (@lem56705 _5851 _5852 _5853 P)). Qed.
Lemma lem56708 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : term143 _5851 _5852 _5853 P.
Proof. exact (EQ_MP (@lem56707 _5851 _5852 _5853 P) (@lem56691 _5851 _5852 _5853 P)). Qed.
Lemma lem56710 {_5076 : Type'} (P : _5076 -> Prop) : term144 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem56711 {_5851 _5852 _5853 : Type'} (P : type332 _5851 _5852 _5853) : term145 _5851 _5852 _5853 P.
Proof. exact (@lem56710 (type1227 _5851 _5852 _5853) P). Qed.
Lemma lem56712 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : term146 _5851 _5852 _5853 P.
Proof. exact (@lem56711 _5851 _5852 _5853 (term142 _5851 _5852 _5853 P)). Qed.
Lemma lem56713 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : term147 _5851 _5852 _5853 P.
Proof. exact (@lem56712 _5851 _5852 _5853 P (@lem56708 _5851 _5852 _5853 P)). Qed.
Lemma lem56714 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term147 _5851 _5852 _5853 P) = (term148 _5851 _5852 _5853 P).
Proof. exact (eq_refl (term147 _5851 _5852 _5853 P)). Qed.
Lemma lem56715 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : term148 _5851 _5852 _5853 P.
Proof. exact (EQ_MP (@lem56714 _5851 _5852 _5853 P) (@lem56713 _5851 _5852 _5853 P)). Qed.
Lemma lem56716 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : term149 _5851 _5852 _5853 P x.
Proof. exact (@lem56715 _5851 _5852 _5853 P x). Qed.
Lemma lem56717 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term149 _5851 _5852 _5853 P x) = (term150 _5851 _5852 _5853 P x).
Proof. exact (eq_refl (term149 _5851 _5852 _5853 P x)). Qed.
Lemma lem56718 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : term150 _5851 _5852 _5853 P x.
Proof. exact (EQ_MP (@lem56717 _5851 _5852 _5853 P x) (@lem56716 _5851 _5852 _5853 P x)). Qed.
Lemma lem56719 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) : term151 _5851 _5852 _5853 P x y.
Proof. exact (@lem56718 _5851 _5852 _5853 P x y). Qed.
Lemma lem56720 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) : (term151 _5851 _5852 _5853 P x y) = (term152 _5851 _5852 _5853 P x y).
Proof. exact (eq_refl (term151 _5851 _5852 _5853 P x y)). Qed.
Lemma lem56721 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) : term152 _5851 _5852 _5853 P x y.
Proof. exact (EQ_MP (@lem56720 _5851 _5852 _5853 P x y) (@lem56719 _5851 _5852 _5853 P x y)). Qed.
Lemma lem56722 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : term153 _5851 _5852 _5853 P x y z.
Proof. exact (@lem56721 _5851 _5852 _5853 P x y z). Qed.
Lemma lem56723 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term153 _5851 _5852 _5853 P x y z) = (term154 _5851 _5852 _5853 P x y z).
Proof. exact (eq_refl (term153 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56724 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : term154 _5851 _5852 _5853 P x y z.
Proof. exact (EQ_MP (@lem56723 _5851 _5852 _5853 P x y z) (@lem56722 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56726 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem56727 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem56726 Prop a b). Qed.
Lemma lem56728 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term154 _5851 _5852 _5853 P x y z) = ((term155 _5851 _5852 _5853 P x y z) = (P x y z)).
Proof. exact (@lem56727 (term155 _5851 _5852 _5853 P x y z) (P x y z)). Qed.
Lemma lem56729 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term155 _5851 _5852 _5853 P x y z) = (P x y z).
Proof. exact (EQ_MP (@lem56728 _5851 _5852 _5853 P x y z) (@lem56724 _5851 _5852 _5853 P x y z)). Qed.
Lemma lem56730 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) (z : _5851) : (term155 _5851 _5852 _5853 P x y z) = (P x y z).
Proof. exact (@lem56729 _5851 _5852 _5853 P x y z). Qed.
Lemma lem56731 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) (p1' : _5852) (p2 : _5851) : (term155 _5851 _5852 _5853 P p1 p1' p2) = (P p1 p1' p2).
Proof. exact (@lem56730 _5851 _5852 _5853 P p1 p1' p2). Qed.
Lemma lem56732 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem56733 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) (p1' : _5852) (p2 : _5851) : (term71 _5851 _5852 _5853 P p1 p1' p2) = (term156 _5851 _5852 _5853 P p1 p1' p2).
Proof. exact (MK_COMB (@lem56732) (@lem56731 _5851 _5852 _5853 P p1 p1' p2)). Qed.
Lemma lem56734 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) (p1' : _5852) : (term73 _5851 _5852 _5853 P p1 p1') = (term157 _5851 _5852 _5853 P p1 p1').
Proof. exact (fun_ext (fun p2 : _5851 => @lem56733 _5851 _5852 _5853 P p1 p1' p2)). Qed.
Lemma lem56735 {_5851 : Type'} : (@all _5851) = (@all _5851).
Proof. exact (eq_refl (@all _5851)). Qed.
Lemma lem56736 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) (p1' : _5852) : (term75 _5851 _5852 _5853 P p1 p1') = (term158 _5851 _5852 _5853 P p1 p1').
Proof. exact (MK_COMB (@lem56735 _5851) (@lem56734 _5851 _5852 _5853 P p1 p1')). Qed.
Lemma lem56743 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) : (term77 _5851 _5852 _5853 P p1) = (term159 _5851 _5852 _5853 P p1).
Proof. exact (fun_ext (fun p1' : _5852 => @lem56736 _5851 _5852 _5853 P p1 p1')). Qed.
Lemma lem56744 {_5852 : Type'} : (@all _5852) = (@all _5852).
Proof. exact (eq_refl (@all _5852)). Qed.
Lemma lem56745 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) : (term78 _5851 _5852 _5853 P p1) = (term160 _5851 _5852 _5853 P p1).
Proof. exact (MK_COMB (@lem56744 _5852) (@lem56743 _5851 _5852 _5853 P p1)). Qed.
Lemma lem56752 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (p1 : _5853) : (term60 _5851 _5852 _5853 P p1) = (term160 _5851 _5852 _5853 P p1).
Proof. exact (TRANS (@lem56552 _5851 _5852 _5853 P p1) (@lem56745 _5851 _5852 _5853 P p1)). Qed.
Lemma lem56753 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term62 _5851 _5852 _5853 P) = (term161 _5851 _5852 _5853 P).
Proof. exact (fun_ext (fun p1 : _5853 => @lem56752 _5851 _5852 _5853 P p1)). Qed.
Lemma lem56754 {_5853 : Type'} : (@all _5853) = (@all _5853).
Proof. exact (eq_refl (@all _5853)). Qed.
Lemma lem56755 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term63 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P).
Proof. exact (MK_COMB (@lem56754 _5853) (@lem56753 _5851 _5852 _5853 P)). Qed.
Lemma lem56762 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term42 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P).
Proof. exact (TRANS (@lem56529 _5851 _5852 _5853 P) (@lem56755 _5851 _5852 _5853 P)). Qed.
Lemma lem56763 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56764 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term163 _5851 _5852 _5853 P) = (term164 _5851 _5852 _5853 P).
Proof. exact (MK_COMB (@lem56763) (@lem56762 _5851 _5852 _5853 P)). Qed.
Lemma lem56766 {A : Type'} (P : A -> Prop) : (term5 A P) = (term8 A P).
Proof. exact (EQ_MP (@lem56364 A P) (@lem56363 A P)). Qed.
Lemma lem56767 {_5853 : Type'} (P : _5853 -> Prop) : (term5 _5853 P) = (term8 _5853 P).
Proof. exact (@lem56766 _5853 P). Qed.
Lemma lem56768 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term165 _5851 _5852 _5853 P) = (term166 _5851 _5852 _5853 P).
Proof. exact (@lem56767 _5853 (term167 _5851 _5852 _5853 P)). Qed.
Lemma lem56776 {A B : Type'} (f : A -> B) (y : A) : (term168 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem56777 {_5853 : Type'} (f : _5853 -> Prop) (y : _5853) : (term169 _5853 f y) = (f y).
Proof. exact (@lem56776 _5853 Prop f y). Qed.
Lemma lem56778 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term170 _5851 _5852 _5853 P x) = (term171 _5851 _5852 _5853 P x).
Proof. exact (@lem56777 _5853 (term167 _5851 _5852 _5853 P) x). Qed.
Lemma lem56779 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term171 _5851 _5852 _5853 P x) = (term172 _5851 _5852 _5853 P x).
Proof. exact (eq_refl (term171 _5851 _5852 _5853 P x)). Qed.
Lemma lem56780 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term173 _5851 _5852 _5853 P) = (term167 _5851 _5852 _5853 P).
Proof. exact (fun_ext (fun x : _5853 => @lem56779 _5851 _5852 _5853 P x)). Qed.
Lemma lem56781 {_5853 : Type'} (x : _5853) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem56782 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term170 _5851 _5852 _5853 P x) = (term171 _5851 _5852 _5853 P x).
Proof. exact (MK_COMB (@lem56780 _5851 _5852 _5853 P) (@lem56781 _5853 x)). Qed.
Lemma lem56783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56784 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term174 _5851 _5852 _5853 P x) = (term175 _5851 _5852 _5853 P x).
Proof. exact (MK_COMB (@lem56783) (@lem56782 _5851 _5852 _5853 P x)). Qed.
Lemma lem56785 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term171 _5851 _5852 _5853 P x) = (term172 _5851 _5852 _5853 P x).
Proof. exact (eq_refl (term171 _5851 _5852 _5853 P x)). Qed.
Lemma lem56786 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : ((term170 _5851 _5852 _5853 P x) = (term171 _5851 _5852 _5853 P x)) = ((term171 _5851 _5852 _5853 P x) = (term172 _5851 _5852 _5853 P x)).
Proof. exact (MK_COMB (@lem56784 _5851 _5852 _5853 P x) (@lem56785 _5851 _5852 _5853 P x)). Qed.
Lemma lem56787 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term171 _5851 _5852 _5853 P x) = (term172 _5851 _5852 _5853 P x).
Proof. exact (EQ_MP (@lem56786 _5851 _5852 _5853 P x) (@lem56778 _5851 _5852 _5853 P x)). Qed.
Lemma lem56796 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem56797 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term176 _5851 _5852 _5853 P x) = (term177 _5851 _5852 _5853 P x).
Proof. exact (MK_COMB (@lem56796) (@lem56787 _5851 _5852 _5853 P x)). Qed.
Lemma lem56799 {A : Type'} (P : A -> Prop) : (term5 A P) = (term8 A P).
Proof. exact (EQ_MP (@lem56364 A P) (@lem56363 A P)). Qed.
Lemma lem56800 {_5852 : Type'} (P : _5852 -> Prop) : (term5 _5852 P) = (term8 _5852 P).
Proof. exact (@lem56799 _5852 P). Qed.
Lemma lem56801 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term177 _5851 _5852 _5853 P x) = (term178 _5851 _5852 _5853 P x).
Proof. exact (@lem56800 _5852 (term179 _5851 _5852 _5853 P x)). Qed.
Lemma lem56809 {A B : Type'} (f : A -> B) (y : A) : (term168 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem56810 {_5852 : Type'} (f : _5852 -> Prop) (y : _5852) : (term169 _5852 f y) = (f y).
Proof. exact (@lem56809 _5852 Prop f y). Qed.
Lemma lem56811 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) : (term180 _5851 _5852 _5853 P x x') = (term181 _5851 _5852 _5853 P x x').
Proof. exact (@lem56810 _5852 (term179 _5851 _5852 _5853 P x) x'). Qed.
Lemma lem56812 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (y : _5852) : (term181 _5851 _5852 _5853 P x y) = (term182 _5851 _5852 _5853 P x y).
Proof. exact (eq_refl (term181 _5851 _5852 _5853 P x y)). Qed.
Lemma lem56813 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term183 _5851 _5852 _5853 P x) = (term179 _5851 _5852 _5853 P x).
Proof. exact (fun_ext (fun y : _5852 => @lem56812 _5851 _5852 _5853 P x y)). Qed.
Lemma lem56814 {_5852 : Type'} (x : _5852) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem56815 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) : (term180 _5851 _5852 _5853 P x x') = (term181 _5851 _5852 _5853 P x x').
Proof. exact (MK_COMB (@lem56813 _5851 _5852 _5853 P x) (@lem56814 _5852 x')). Qed.
Lemma lem56816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56817 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) : (term184 _5851 _5852 _5853 P x x') = (term185 _5851 _5852 _5853 P x x').
Proof. exact (MK_COMB (@lem56816) (@lem56815 _5851 _5852 _5853 P x x')). Qed.
Lemma lem56818 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) : (term181 _5851 _5852 _5853 P x x') = (term182 _5851 _5852 _5853 P x x').
Proof. exact (eq_refl (term181 _5851 _5852 _5853 P x x')). Qed.
Lemma lem56819 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) : ((term180 _5851 _5852 _5853 P x x') = (term181 _5851 _5852 _5853 P x x')) = ((term181 _5851 _5852 _5853 P x x') = (term182 _5851 _5852 _5853 P x x')).
Proof. exact (MK_COMB (@lem56817 _5851 _5852 _5853 P x x') (@lem56818 _5851 _5852 _5853 P x x')). Qed.
Lemma lem56820 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) : (term181 _5851 _5852 _5853 P x x') = (term182 _5851 _5852 _5853 P x x').
Proof. exact (EQ_MP (@lem56819 _5851 _5852 _5853 P x x') (@lem56811 _5851 _5852 _5853 P x x')). Qed.
Lemma lem56825 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem56826 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) : (term186 _5851 _5852 _5853 P x x') = (term187 _5851 _5852 _5853 P x x').
Proof. exact (MK_COMB (@lem56825) (@lem56820 _5851 _5852 _5853 P x x')). Qed.
Lemma lem56828 {A : Type'} (P : A -> Prop) : (term5 A P) = (term8 A P).
Proof. exact (EQ_MP (@lem56364 A P) (@lem56363 A P)). Qed.
Lemma lem56829 {_5851 : Type'} (P : _5851 -> Prop) : (term5 _5851 P) = (term8 _5851 P).
Proof. exact (@lem56828 _5851 P). Qed.
Lemma lem56830 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) : (term187 _5851 _5852 _5853 P x x') = (term188 _5851 _5852 _5853 P x x').
Proof. exact (@lem56829 _5851 (term114 _5851 _5852 _5853 P x x')). Qed.
Lemma lem56838 {A B : Type'} (f : A -> B) (y : A) : (term168 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem56839 {_5851 : Type'} (f : _5851 -> Prop) (y : _5851) : (term169 _5851 f y) = (f y).
Proof. exact (@lem56838 _5851 Prop f y). Qed.
Lemma lem56840 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) (x'' : _5851) : (term189 _5851 _5852 _5853 P x x' x'') = (term116 _5851 _5852 _5853 P x x' x'').
Proof. exact (@lem56839 _5851 (term114 _5851 _5852 _5853 P x x') x''). Qed.
Lemma lem56841 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) (z : _5851) : (term116 _5851 _5852 _5853 P x x' z) = (P x x' z).
Proof. exact (eq_refl (term116 _5851 _5852 _5853 P x x' z)). Qed.
Lemma lem56842 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) : (term190 _5851 _5852 _5853 P x x') = (term114 _5851 _5852 _5853 P x x').
Proof. exact (fun_ext (fun z : _5851 => @lem56841 _5851 _5852 _5853 P x x' z)). Qed.
Lemma lem56843 {_5851 : Type'} (x : _5851) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem56844 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) (x'' : _5851) : (term189 _5851 _5852 _5853 P x x' x'') = (term116 _5851 _5852 _5853 P x x' x'').
Proof. exact (MK_COMB (@lem56842 _5851 _5852 _5853 P x x') (@lem56843 _5851 x'')). Qed.
Lemma lem56845 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56846 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) (x'' : _5851) : (term191 _5851 _5852 _5853 P x x' x'') = (term119 _5851 _5852 _5853 P x x' x'').
Proof. exact (MK_COMB (@lem56845) (@lem56844 _5851 _5852 _5853 P x x' x'')). Qed.
Lemma lem56847 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) (x'' : _5851) : (term116 _5851 _5852 _5853 P x x' x'') = (P x x' x'').
Proof. exact (eq_refl (term116 _5851 _5852 _5853 P x x' x'')). Qed.
Lemma lem56848 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) (x'' : _5851) : ((term189 _5851 _5852 _5853 P x x' x'') = (term116 _5851 _5852 _5853 P x x' x'')) = ((term116 _5851 _5852 _5853 P x x' x'') = (P x x' x'')).
Proof. exact (MK_COMB (@lem56846 _5851 _5852 _5853 P x x' x'') (@lem56847 _5851 _5852 _5853 P x x' x'')). Qed.
Lemma lem56849 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) (x'' : _5851) : (term116 _5851 _5852 _5853 P x x' x'') = (P x x' x'').
Proof. exact (EQ_MP (@lem56848 _5851 _5852 _5853 P x x' x'') (@lem56840 _5851 _5852 _5853 P x x' x'')). Qed.
Lemma lem56850 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem56851 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) (x'' : _5851) : (term192 _5851 _5852 _5853 P x x' x'') = (term156 _5851 _5852 _5853 P x x' x'').
Proof. exact (MK_COMB (@lem56850) (@lem56849 _5851 _5852 _5853 P x x' x'')). Qed.
Lemma lem56852 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) : (term193 _5851 _5852 _5853 P x x') = (term157 _5851 _5852 _5853 P x x').
Proof. exact (fun_ext (fun x'' : _5851 => @lem56851 _5851 _5852 _5853 P x x' x'')). Qed.
Lemma lem56853 {_5851 : Type'} : (@all _5851) = (@all _5851).
Proof. exact (eq_refl (@all _5851)). Qed.
Lemma lem56854 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) : (term188 _5851 _5852 _5853 P x x') = (term158 _5851 _5852 _5853 P x x').
Proof. exact (MK_COMB (@lem56853 _5851) (@lem56852 _5851 _5852 _5853 P x x')). Qed.
Lemma lem56861 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) : (term187 _5851 _5852 _5853 P x x') = (term158 _5851 _5852 _5853 P x x').
Proof. exact (TRANS (@lem56830 _5851 _5852 _5853 P x x') (@lem56854 _5851 _5852 _5853 P x x')). Qed.
Lemma lem56862 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) (x' : _5852) : (term186 _5851 _5852 _5853 P x x') = (term158 _5851 _5852 _5853 P x x').
Proof. exact (TRANS (@lem56826 _5851 _5852 _5853 P x x') (@lem56861 _5851 _5852 _5853 P x x')). Qed.
Lemma lem56863 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term194 _5851 _5852 _5853 P x) = (term159 _5851 _5852 _5853 P x).
Proof. exact (fun_ext (fun x' : _5852 => @lem56862 _5851 _5852 _5853 P x x')). Qed.
Lemma lem56864 {_5852 : Type'} : (@all _5852) = (@all _5852).
Proof. exact (eq_refl (@all _5852)). Qed.
Lemma lem56865 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term178 _5851 _5852 _5853 P x) = (term160 _5851 _5852 _5853 P x).
Proof. exact (MK_COMB (@lem56864 _5852) (@lem56863 _5851 _5852 _5853 P x)). Qed.
Lemma lem56872 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term177 _5851 _5852 _5853 P x) = (term160 _5851 _5852 _5853 P x).
Proof. exact (TRANS (@lem56801 _5851 _5852 _5853 P x) (@lem56865 _5851 _5852 _5853 P x)). Qed.
Lemma lem56873 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) (x : _5853) : (term176 _5851 _5852 _5853 P x) = (term160 _5851 _5852 _5853 P x).
Proof. exact (TRANS (@lem56797 _5851 _5852 _5853 P x) (@lem56872 _5851 _5852 _5853 P x)). Qed.
Lemma lem56874 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term195 _5851 _5852 _5853 P) = (term161 _5851 _5852 _5853 P).
Proof. exact (fun_ext (fun x : _5853 => @lem56873 _5851 _5852 _5853 P x)). Qed.
Lemma lem56875 {_5853 : Type'} : (@all _5853) = (@all _5853).
Proof. exact (eq_refl (@all _5853)). Qed.
Lemma lem56876 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term166 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P).
Proof. exact (MK_COMB (@lem56875 _5853) (@lem56874 _5851 _5852 _5853 P)). Qed.
Lemma lem56883 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term165 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P).
Proof. exact (TRANS (@lem56768 _5851 _5852 _5853 P) (@lem56876 _5851 _5852 _5853 P)). Qed.
Lemma lem56884 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : ((term42 _5851 _5852 _5853 P) = (term165 _5851 _5852 _5853 P)) = ((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)).
Proof. exact (MK_COMB (@lem56764 _5851 _5852 _5853 P) (@lem56883 _5851 _5852 _5853 P)). Qed.
Lemma lem56886 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem56887 (x : Prop) : (x = x) = True.
Proof. exact (@lem56886 Prop x). Qed.
Lemma lem56888 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : ((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)) = True.
Proof. exact (@lem56887 (term162 _5851 _5852 _5853 P)). Qed.
Lemma lem56891 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term196 _5851 _5852 _5853 P) = (term196 _5851 _5852 _5853 P).
Proof. exact (eq_refl (term196 _5851 _5852 _5853 P)). Qed.
Lemma lem56892 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term196 _5851 _5852 _5853 P) = (((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)) = True).
Proof. exact (eq_refl (term196 _5851 _5852 _5853 P)). Qed.
Lemma lem56893 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term197 _5851 _5852 _5853 P) = (term197 _5851 _5852 _5853 P).
Proof. exact (eq_refl (term197 _5851 _5852 _5853 P)). Qed.
Lemma lem56894 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : ((term196 _5851 _5852 _5853 P) = (term196 _5851 _5852 _5853 P)) = ((term196 _5851 _5852 _5853 P) = (((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)) = True)).
Proof. exact (MK_COMB (@lem56893 _5851 _5852 _5853 P) (@lem56892 _5851 _5852 _5853 P)). Qed.
Lemma lem56895 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term196 _5851 _5852 _5853 P) = (((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)) = True).
Proof. exact (eq_refl (term196 _5851 _5852 _5853 P)). Qed.
Lemma lem56896 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56897 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term197 _5851 _5852 _5853 P) = (term198 _5851 _5852 _5853 P).
Proof. exact (MK_COMB (@lem56896) (@lem56895 _5851 _5852 _5853 P)). Qed.
Lemma lem56898 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)) = True) = (((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)) = True).
Proof. exact (eq_refl (((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)) = True)). Qed.
Lemma lem56899 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : ((term196 _5851 _5852 _5853 P) = (((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)) = True)) = ((((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)) = True) = (((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)) = True)).
Proof. exact (MK_COMB (@lem56897 _5851 _5852 _5853 P) (@lem56898 _5851 _5852 _5853 P)). Qed.
Lemma lem56900 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : ((term196 _5851 _5852 _5853 P) = (term196 _5851 _5852 _5853 P)) = ((((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)) = True) = (((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)) = True)).
Proof. exact (TRANS (@lem56894 _5851 _5852 _5853 P) (@lem56899 _5851 _5852 _5853 P)). Qed.
Lemma lem56901 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)) = True) = (((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)) = True).
Proof. exact (EQ_MP (@lem56900 _5851 _5852 _5853 P) (@lem56891 _5851 _5852 _5853 P)). Qed.
Lemma lem56902 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : ((term162 _5851 _5852 _5853 P) = (term162 _5851 _5852 _5853 P)) = True.
Proof. exact (EQ_MP (@lem56901 _5851 _5852 _5853 P) (@lem56888 _5851 _5852 _5853 P)). Qed.
Lemma lem56903 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : ((term42 _5851 _5852 _5853 P) = (term165 _5851 _5852 _5853 P)) = True.
Proof. exact (TRANS (@lem56884 _5851 _5852 _5853 P) (@lem56902 _5851 _5852 _5853 P)). Qed.
Lemma lem56904 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : True = ((term42 _5851 _5852 _5853 P) = (term165 _5851 _5852 _5853 P)).
Proof. exact (SYM (@lem56903 _5851 _5852 _5853 P)). Qed.
Lemma lem56905 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term42 _5851 _5852 _5853 P) = (term165 _5851 _5852 _5853 P).
Proof. exact (EQ_MP (@lem56904 _5851 _5852 _5853 P) (@lem0)). Qed.
Lemma lem56906 {_5851 _5852 _5853 : Type'} (P : type1517 _5851 _5852 _5853) : (term38 _5851 _5852 _5853 P) = (term39 _5851 _5852 _5853 P).
Proof. exact (@lem56493 _5851 _5852 _5853 P (@lem56905 _5851 _5852 _5853 P)). Qed.
Lemma lem56911 {_5851 _5852 _5853 : Type'} : term199 _5851 _5852 _5853.
Proof. exact (fun P : type1517 _5851 _5852 _5853 => @lem56906 _5851 _5852 _5853 P). Qed.
