Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_CARTESIAN_PRODUCT_term_abbrevs.
Require Import cartesian_product_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem4399469 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4399470 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem4399469 _83095 p). Qed.
Lemma lem4399471 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem4399472 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem4399471 _83095 p) (@lem4399470 _83095 p)). Qed.
Lemma lem4399473 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem4399472 _83095 p x). Qed.
Lemma lem4399474 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem4399483 {A K : Type'} (k : K -> Prop) : term5 A K k.
Proof. exact (@lem4399444 A K k). Qed.
Lemma lem4399484 {A K : Type'} (k : K -> Prop) : (term5 A K k) = (term6 A K k).
Proof. exact (eq_refl (term5 A K k)). Qed.
Lemma lem4399485 {A K : Type'} (k : K -> Prop) : term6 A K k.
Proof. exact (EQ_MP (@lem4399484 A K k) (@lem4399483 A K k)). Qed.
Lemma lem4399486 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term7 A K k s.
Proof. exact (@lem4399485 A K k s). Qed.
Lemma lem4399487 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term7 A K k s) = ((@cartesian_product A K k s) = (term8 A K k s)).
Proof. exact (eq_refl (term7 A K k s)). Qed.
Lemma lem4399504 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term8 A K k s).
Proof. exact (EQ_MP (@lem4399487 A K k s) (@lem4399486 A K k s)). Qed.
Lemma lem4399505 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term8 A K k s).
Proof. exact (@lem4399504 A K k s). Qed.
Lemma lem4399518 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4399519 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term9 A K x k s) = (term10 A K x k s).
Proof. exact (MK_COMB (@lem4399518 A K x) (@lem4399505 A K k s)). Qed.
Lemma lem4399521 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4399474 _83095 p x) (@lem4399473 _83095 p x)). Qed.
Lemma lem4399522 {A K : Type'} (p : type805 A K) (x : K -> A) : (term11 A K x p) = (p x).
Proof. exact (@lem4399521 (K -> A) p x). Qed.
Lemma lem4399523 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term12 A K x k s) = (term13 A K k s x).
Proof. exact (@lem4399522 A K (term14 A K k s) x). Qed.
Lemma lem4399524 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term13 A K k s f) = (term15 A K k f s).
Proof. exact (eq_refl (term13 A K k s f)). Qed.
Lemma lem4399525 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4399526 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term16 A K GEN_PVAR_140 k s f) = (term17 A K GEN_PVAR_140 k f s).
Proof. exact (MK_COMB (@lem4399525 A K GEN_PVAR_140) (@lem4399524 A K k f s)). Qed.
Lemma lem4399527 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4399528 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term18 A K GEN_PVAR_140 k s f) = (term19 A K GEN_PVAR_140 k s f).
Proof. exact (MK_COMB (@lem4399526 A K GEN_PVAR_140 k f s) (@lem4399527 A K f)). Qed.
Lemma lem4399529 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term20 A K GEN_PVAR_140 k s) = (term21 A K GEN_PVAR_140 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4399528 A K GEN_PVAR_140 k s f)). Qed.
Lemma lem4399530 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4399531 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term22 A K GEN_PVAR_140 k s) = (term23 A K GEN_PVAR_140 k s).
Proof. exact (MK_COMB (@lem4399530 A K) (@lem4399529 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4399532 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term24 A K k s) = (term25 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4399531 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4399533 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4399534 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term26 A K k s) = (term8 A K k s).
Proof. exact (MK_COMB (@lem4399533 A K) (@lem4399532 A K k s)). Qed.
Lemma lem4399535 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4399536 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term12 A K x k s) = (term10 A K x k s).
Proof. exact (MK_COMB (@lem4399535 A K x) (@lem4399534 A K k s)). Qed.
Lemma lem4399537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4399538 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term27 A K x k s) = (term28 A K x k s).
Proof. exact (MK_COMB (@lem4399537) (@lem4399536 A K x k s)). Qed.
Lemma lem4399539 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term13 A K k s x) = (term15 A K k x s).
Proof. exact (eq_refl (term13 A K k s x)). Qed.
Lemma lem4399540 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term12 A K x k s) = (term13 A K k s x)) = ((term10 A K x k s) = (term15 A K k x s)).
Proof. exact (MK_COMB (@lem4399538 A K x k s) (@lem4399539 A K k x s)). Qed.
Lemma lem4399541 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term10 A K x k s) = (term15 A K k x s).
Proof. exact (EQ_MP (@lem4399540 A K k x s) (@lem4399523 A K k s x)). Qed.
Lemma lem4399550 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term9 A K x k s) = (term15 A K k x s).
Proof. exact (TRANS (@lem4399519 A K x k s) (@lem4399541 A K k x s)). Qed.
Lemma lem4399551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4399552 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term29 A K x k s) = (term30 A K k x s).
Proof. exact (MK_COMB (@lem4399551) (@lem4399550 A K k x s)). Qed.
Lemma lem4399561 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term15 A K k x s) = (term15 A K k x s).
Proof. exact (eq_refl (term15 A K k x s)). Qed.
Lemma lem4399562 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term9 A K x k s) = (term15 A K k x s)) = ((term15 A K k x s) = (term15 A K k x s)).
Proof. exact (MK_COMB (@lem4399552 A K k x s) (@lem4399561 A K k x s)). Qed.
Lemma lem4399564 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4399565 (x : Prop) : (x = x) = True.
Proof. exact (@lem4399564 Prop x). Qed.
Lemma lem4399566 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term15 A K k x s) = (term15 A K k x s)) = True.
Proof. exact (@lem4399565 (term15 A K k x s)). Qed.
Lemma lem4399567 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term9 A K x k s) = (term15 A K k x s)) = True.
Proof. exact (TRANS (@lem4399562 A K k x s) (@lem4399566 A K k x s)). Qed.
Lemma lem4399568 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term31 A K k s) = (term32 A K).
Proof. exact (fun_ext (fun x : K -> A => @lem4399567 A K k x s)). Qed.
Lemma lem4399569 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4399570 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term33 A K k s) = (term34 A K).
Proof. exact (MK_COMB (@lem4399569 A K) (@lem4399568 A K k s)). Qed.
Lemma lem4399572 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4399573 {A K : Type'} (t : Prop) : (term36 A K t) = t.
Proof. exact (@lem4399572 (K -> A) t). Qed.
Lemma lem4399574 {A K : Type'} : (term34 A K) = True.
Proof. exact (@lem4399573 A K True). Qed.
Lemma lem4399575 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term33 A K k s) = True.
Proof. exact (TRANS (@lem4399570 A K k s) (@lem4399574 A K)). Qed.
Lemma lem4399576 {A K : Type'} (k : K -> Prop) : (term37 A K k) = (term38 A K).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4399575 A K k s)). Qed.
Lemma lem4399577 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4399578 {A K : Type'} (k : K -> Prop) : (term39 A K k) = (term40 A K).
Proof. exact (MK_COMB (@lem4399577 A K) (@lem4399576 A K k)). Qed.
Lemma lem4399580 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4399581 {A K : Type'} (t : Prop) : (term41 A K t) = t.
Proof. exact (@lem4399580 (type1470 A K) t). Qed.
Lemma lem4399582 {A K : Type'} : (term40 A K) = True.
Proof. exact (@lem4399581 A K True). Qed.
Lemma lem4399583 {A K : Type'} (k : K -> Prop) : (term39 A K k) = True.
Proof. exact (TRANS (@lem4399578 A K k) (@lem4399582 A K)). Qed.
Lemma lem4399584 {A K : Type'} : (term42 A K) = (term43 K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4399583 A K k)). Qed.
Lemma lem4399585 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4399586 {A K : Type'} : (term44 A K) = (term45 K).
Proof. exact (MK_COMB (@lem4399585 K) (@lem4399584 A K)). Qed.
Lemma lem4399588 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4399589 {K : Type'} (t : Prop) : (term46 K t) = t.
Proof. exact (@lem4399588 (K -> Prop) t). Qed.
Lemma lem4399590 {K : Type'} : (term45 K) = True.
Proof. exact (@lem4399589 K True). Qed.
Lemma lem4399591 {A K : Type'} : (term44 A K) = True.
Proof. exact (TRANS (@lem4399586 A K) (@lem4399590 K)). Qed.
Lemma lem4399592 {A K : Type'} : True = (term44 A K).
Proof. exact (SYM (@lem4399591 A K)). Qed.
Lemma lem4399593 {A K : Type'} : term44 A K.
Proof. exact (EQ_MP (@lem4399592 A K) (@lem0)). Qed.
