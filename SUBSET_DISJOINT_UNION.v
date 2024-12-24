Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_DISJOINT_UNION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FORALL_IN_GSPEC_spec.
Require Import IN_ELIM_PAIR_THM_spec.
Require Import SUBSET_spec.
Require Import disjoint_union_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Lemma lem4464465 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4464466 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4464467 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4464466 t1) (@lem4464465 t1)). Qed.
Lemma lem4464468 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4464467 t1 t2). Qed.
Lemma lem4464469 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4464470 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4464469 t1 t2) (@lem4464468 t1 t2)). Qed.
Lemma lem4464471 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4464470 t1 t2 t3). Qed.
Lemma lem4464472 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4464473 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4464472 t1 t2 t3) (@lem4464471 t1 t2 t3)). Qed.
Lemma lem4464474 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4464473 t1 t2 t3)). Qed.
Lemma lem4464475 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term7 _88435 _88436 P.
Proof. exact (@lem3405756 _88435 _88436 P). Qed.
Lemma lem4464476 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term7 _88435 _88436 P) = (term8 _88435 _88436 P).
Proof. exact (eq_refl (term7 _88435 _88436 P)). Qed.
Lemma lem4464477 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term8 _88435 _88436 P.
Proof. exact (EQ_MP (@lem4464476 _88435 _88436 P) (@lem4464475 _88435 _88436 P)). Qed.
Lemma lem4464478 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term9 _88435 _88436 P a.
Proof. exact (@lem4464477 _88435 _88436 P a). Qed.
Lemma lem4464479 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term9 _88435 _88436 P a) = (term10 _88435 _88436 P a).
Proof. exact (eq_refl (term9 _88435 _88436 P a)). Qed.
Lemma lem4464480 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term10 _88435 _88436 P a.
Proof. exact (EQ_MP (@lem4464479 _88435 _88436 P a) (@lem4464478 _88435 _88436 P a)). Qed.
Lemma lem4464481 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : term11 _88435 _88436 P a b.
Proof. exact (@lem4464480 _88435 _88436 P a b). Qed.
Lemma lem4464482 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term11 _88435 _88436 P a b) = ((term12 _88435 _88436 a b P) = (P a b)).
Proof. exact (eq_refl (term11 _88435 _88436 P a b)). Qed.
Lemma lem4464484 {_88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 : Type'} (Q : _89106 -> Prop) : term13 _88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 Q.
Proof. exact (proj2 (@lem3435744 Prop _88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 Q)). Qed.
Lemma lem4464500 {_88961 _88962 _89106 : Type'} (Q : _89106 -> Prop) : term14 _88961 _88962 _89106 Q.
Proof. exact (proj1 (@lem4464484 _88961 _88962 Prop Prop Prop _89106 Prop Prop Prop Prop Q)). Qed.
Lemma lem4464501 {_88961 _88962 _89106 : Type'} (Q : _89106 -> Prop) (P : type1470 _88961 _88962) : term15 _88961 _88962 _89106 Q P.
Proof. exact (@lem4464500 _88961 _88962 _89106 Q P). Qed.
Lemma lem4464502 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) : (term15 _88961 _88962 _89106 Q P) = (term16 _88961 _88962 _89106 P Q).
Proof. exact (eq_refl (term15 _88961 _88962 _89106 Q P)). Qed.
Lemma lem4464503 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) : term16 _88961 _88962 _89106 P Q.
Proof. exact (EQ_MP (@lem4464502 _88961 _88962 _89106 P Q) (@lem4464501 _88961 _88962 _89106 Q P)). Qed.
Lemma lem4464504 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : term17 _88961 _88962 _89106 P Q f.
Proof. exact (@lem4464503 _88961 _88962 _89106 P Q f). Qed.
Lemma lem4464505 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : (term17 _88961 _88962 _89106 P Q f) = ((term18 _88961 _88962 _89106 P f Q) = (term19 _88961 _88962 _89106 P Q f)).
Proof. exact (eq_refl (term17 _88961 _88962 _89106 P Q f)). Qed.
Lemma lem4464514 {A K : Type'} (k : K -> Prop) : term20 A K k.
Proof. exact (@lem4464464 A K k). Qed.
Lemma lem4464515 {A K : Type'} (k : K -> Prop) : (term20 A K k) = (term21 A K k).
Proof. exact (eq_refl (term20 A K k)). Qed.
Lemma lem4464516 {A K : Type'} (k : K -> Prop) : term21 A K k.
Proof. exact (EQ_MP (@lem4464515 A K k) (@lem4464514 A K k)). Qed.
Lemma lem4464517 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term22 A K k s.
Proof. exact (@lem4464516 A K k s). Qed.
Lemma lem4464518 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term22 A K k s) = ((@disjoint_union A K k s) = (term23 A K k s)).
Proof. exact (eq_refl (term22 A K k s)). Qed.
Lemma lem4464520 {A : Type'} (s : A -> Prop) : term24 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4464521 {A : Type'} (s : A -> Prop) : (term24 A s) = (term25 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem4464522 {A : Type'} (s : A -> Prop) : term25 A s.
Proof. exact (EQ_MP (@lem4464521 A s) (@lem4464520 A s)). Qed.
Lemma lem4464523 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term26 A s t.
Proof. exact (@lem4464522 A s t). Qed.
Lemma lem4464524 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = ((@SUBSET A s t) = (term27 A s t)).
Proof. exact (eq_refl (term26 A s t)). Qed.
Lemma lem4464541 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term27 A s t).
Proof. exact (EQ_MP (@lem4464524 A s t) (@lem4464523 A s t)). Qed.
Lemma lem4464542 {A K : Type'} (s : type1223 A K) (t : type1223 A K) : (@SUBSET (prod K A) s t) = (term28 A K s t).
Proof. exact (@lem4464541 (prod K A) s t). Qed.
Lemma lem4464543 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term29 A K s k t) = (term30 A K s k t).
Proof. exact (@lem4464542 A K (@disjoint_union A K k s) (@disjoint_union A K k t)). Qed.
Lemma lem4464551 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (EQ_MP (@lem4464518 A K k s) (@lem4464517 A K k s)). Qed.
Lemma lem4464552 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (@lem4464551 A K k s). Qed.
Lemma lem4464563 {A K : Type'} (x : prod K A) : (@IN (prod K A) x) = (@IN (prod K A) x).
Proof. exact (eq_refl (@IN (prod K A) x)). Qed.
Lemma lem4464564 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : (term31 A K x k s) = (term32 A K x k s).
Proof. exact (MK_COMB (@lem4464563 A K x) (@lem4464552 A K k s)). Qed.
Lemma lem4464565 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4464566 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : (term33 A K x k s) = (term34 A K x k s).
Proof. exact (MK_COMB (@lem4464565) (@lem4464564 A K x k s)). Qed.
Lemma lem4464568 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (EQ_MP (@lem4464518 A K k s) (@lem4464517 A K k s)). Qed.
Lemma lem4464569 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (@lem4464568 A K k s). Qed.
Lemma lem4464570 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@disjoint_union A K k t) = (term23 A K k t).
Proof. exact (@lem4464569 A K k t). Qed.
Lemma lem4464581 {A K : Type'} (x : prod K A) : (@IN (prod K A) x) = (@IN (prod K A) x).
Proof. exact (eq_refl (@IN (prod K A) x)). Qed.
Lemma lem4464582 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term31 A K x k t) = (term32 A K x k t).
Proof. exact (MK_COMB (@lem4464581 A K x) (@lem4464570 A K k t)). Qed.
Lemma lem4464583 {A K : Type'} (s : type1470 A K) (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term35 A K s x k t) = (term36 A K s x k t).
Proof. exact (MK_COMB (@lem4464566 A K x k s) (@lem4464582 A K x k t)). Qed.
Lemma lem4464586 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term37 A K s k t) = (term38 A K s k t).
Proof. exact (fun_ext (fun x : prod K A => @lem4464583 A K s x k t)). Qed.
Lemma lem4464587 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4464588 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term30 A K s k t) = (term39 A K s k t).
Proof. exact (MK_COMB (@lem4464587 A K) (@lem4464586 A K s k t)). Qed.
Lemma lem4464590 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : (term18 _88961 _88962 _89106 P f Q) = (term19 _88961 _88962 _89106 P Q f).
Proof. exact (EQ_MP (@lem4464505 _88961 _88962 _89106 P Q f) (@lem4464504 _88961 _88962 _89106 P Q f)). Qed.
Lemma lem4464591 {A K : Type'} (P : type1470 A K) (Q : type1223 A K) (f : type1466 A K) : (term40 A K P f Q) = (term41 A K P Q f).
Proof. exact (@lem4464590 A K (prod K A) P Q f). Qed.
Lemma lem4464592 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term42 A K s k t) = (term43 A K s k t).
Proof. exact (@lem4464591 A K (term44 A K k s) (term45 A K k t) (@pair K A)). Qed.
Lemma lem4464593 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term46 A K k s i) = (term47 A K k s i).
Proof. exact (eq_refl (term46 A K k s i)). Qed.
Lemma lem4464594 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4464595 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term48 A K k s i x) = (term49 A K k s i x).
Proof. exact (MK_COMB (@lem4464593 A K k s i) (@lem4464594 A x)). Qed.
Lemma lem4464596 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term49 A K k s i x) = (term50 A K k x s i).
Proof. exact (eq_refl (term49 A K k s i x)). Qed.
Lemma lem4464597 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term48 A K k s i x) = (term50 A K k x s i).
Proof. exact (TRANS (@lem4464595 A K k s i x) (@lem4464596 A K k x s i)). Qed.
Lemma lem4464598 {A K : Type'} (GEN_PVAR_143 : prod K A) : (@SETSPEC (prod K A) GEN_PVAR_143) = (@SETSPEC (prod K A) GEN_PVAR_143).
Proof. exact (eq_refl (@SETSPEC (prod K A) GEN_PVAR_143)). Qed.
Lemma lem4464599 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term51 A K GEN_PVAR_143 k s i x) = (term52 A K GEN_PVAR_143 k x s i).
Proof. exact (MK_COMB (@lem4464598 A K GEN_PVAR_143) (@lem4464597 A K k x s i)). Qed.
Lemma lem4464600 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4464601 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term53 A K GEN_PVAR_143 k s i x) = (term54 A K GEN_PVAR_143 k s i x).
Proof. exact (MK_COMB (@lem4464599 A K GEN_PVAR_143 k x s i) (@lem4464600 A K i x)). Qed.
Lemma lem4464602 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term55 A K GEN_PVAR_143 k s i) = (term56 A K GEN_PVAR_143 k s i).
Proof. exact (fun_ext (fun x : A => @lem4464601 A K GEN_PVAR_143 k s i x)). Qed.
Lemma lem4464603 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4464604 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term57 A K GEN_PVAR_143 k s i) = (term58 A K GEN_PVAR_143 k s i).
Proof. exact (MK_COMB (@lem4464603 A) (@lem4464602 A K GEN_PVAR_143 k s i)). Qed.
Lemma lem4464605 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) : (term59 A K GEN_PVAR_143 k s) = (term60 A K GEN_PVAR_143 k s).
Proof. exact (fun_ext (fun i : K => @lem4464604 A K GEN_PVAR_143 k s i)). Qed.
Lemma lem4464606 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4464607 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) : (term61 A K GEN_PVAR_143 k s) = (term62 A K GEN_PVAR_143 k s).
Proof. exact (MK_COMB (@lem4464606 K) (@lem4464605 A K GEN_PVAR_143 k s)). Qed.
Lemma lem4464608 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term63 A K k s) = (term64 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_143 : prod K A => @lem4464607 A K GEN_PVAR_143 k s)). Qed.
Lemma lem4464609 {A K : Type'} : (@GSPEC (prod K A)) = (@GSPEC (prod K A)).
Proof. exact (eq_refl (@GSPEC (prod K A))). Qed.
Lemma lem4464610 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term65 A K k s) = (term23 A K k s).
Proof. exact (MK_COMB (@lem4464609 A K) (@lem4464608 A K k s)). Qed.
Lemma lem4464611 {A K : Type'} (x : prod K A) : (@IN (prod K A) x) = (@IN (prod K A) x).
Proof. exact (eq_refl (@IN (prod K A) x)). Qed.
Lemma lem4464612 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : (term66 A K x k s) = (term32 A K x k s).
Proof. exact (MK_COMB (@lem4464611 A K x) (@lem4464610 A K k s)). Qed.
Lemma lem4464613 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4464614 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : (term67 A K x k s) = (term34 A K x k s).
Proof. exact (MK_COMB (@lem4464613) (@lem4464612 A K x k s)). Qed.
Lemma lem4464615 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term68 A K k t x) = (term32 A K x k t).
Proof. exact (eq_refl (term68 A K k t x)). Qed.
Lemma lem4464616 {A K : Type'} (s : type1470 A K) (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term69 A K s k t x) = (term36 A K s x k t).
Proof. exact (MK_COMB (@lem4464614 A K x k s) (@lem4464615 A K x k t)). Qed.
Lemma lem4464617 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term70 A K s k t) = (term38 A K s k t).
Proof. exact (fun_ext (fun x : prod K A => @lem4464616 A K s x k t)). Qed.
Lemma lem4464618 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4464619 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term42 A K s k t) = (term39 A K s k t).
Proof. exact (MK_COMB (@lem4464618 A K) (@lem4464617 A K s k t)). Qed.
Lemma lem4464620 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4464621 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term71 A K s k t) = (term72 A K s k t).
Proof. exact (MK_COMB (@lem4464620) (@lem4464619 A K s k t)). Qed.
Lemma lem4464622 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term46 A K k s i) = (term47 A K k s i).
Proof. exact (eq_refl (term46 A K k s i)). Qed.
Lemma lem4464623 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4464624 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term48 A K k s i x) = (term49 A K k s i x).
Proof. exact (MK_COMB (@lem4464622 A K k s i) (@lem4464623 A x)). Qed.
Lemma lem4464625 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term49 A K k s i x) = (term50 A K k x s i).
Proof. exact (eq_refl (term49 A K k s i x)). Qed.
Lemma lem4464626 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term48 A K k s i x) = (term50 A K k x s i).
Proof. exact (TRANS (@lem4464624 A K k s i x) (@lem4464625 A K k x s i)). Qed.
Lemma lem4464627 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4464628 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term73 A K k s i x) = (term74 A K k x s i).
Proof. exact (MK_COMB (@lem4464627) (@lem4464626 A K k x s i)). Qed.
Lemma lem4464629 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) : (term75 A K k t i x) = (term76 A K i x k t).
Proof. exact (eq_refl (term75 A K k t i x)). Qed.
Lemma lem4464630 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) : (term77 A K s k t i x) = (term78 A K s i x k t).
Proof. exact (MK_COMB (@lem4464628 A K k x s i) (@lem4464629 A K i x k t)). Qed.
Lemma lem4464631 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) : (term79 A K s k t i) = (term80 A K s i k t).
Proof. exact (fun_ext (fun x : A => @lem4464630 A K s i x k t)). Qed.
Lemma lem4464632 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4464633 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) : (term81 A K s k t i) = (term82 A K s i k t).
Proof. exact (MK_COMB (@lem4464632 A) (@lem4464631 A K s i k t)). Qed.
Lemma lem4464634 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term83 A K s k t) = (term84 A K s k t).
Proof. exact (fun_ext (fun i : K => @lem4464633 A K s i k t)). Qed.
Lemma lem4464635 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4464636 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term43 A K s k t) = (term85 A K s k t).
Proof. exact (MK_COMB (@lem4464635 K) (@lem4464634 A K s k t)). Qed.
Lemma lem4464637 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : ((term42 A K s k t) = (term43 A K s k t)) = ((term39 A K s k t) = (term85 A K s k t)).
Proof. exact (MK_COMB (@lem4464621 A K s k t) (@lem4464636 A K s k t)). Qed.
Lemma lem4464638 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term39 A K s k t) = (term85 A K s k t).
Proof. exact (EQ_MP (@lem4464637 A K s k t) (@lem4464592 A K s k t)). Qed.
Lemma lem4464661 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term30 A K s k t) = (term85 A K s k t).
Proof. exact (TRANS (@lem4464588 A K s k t) (@lem4464638 A K s k t)). Qed.
Lemma lem4464662 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term29 A K s k t) = (term85 A K s k t).
Proof. exact (TRANS (@lem4464543 A K s k t) (@lem4464661 A K s k t)). Qed.
Lemma lem4464663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4464664 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term86 A K s k t) = (term87 A K s k t).
Proof. exact (MK_COMB (@lem4464663) (@lem4464662 A K s k t)). Qed.
Lemma lem4464672 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term27 A s t).
Proof. exact (EQ_MP (@lem4464524 A s t) (@lem4464523 A s t)). Qed.
Lemma lem4464673 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term27 A s t).
Proof. exact (@lem4464672 A s t). Qed.
Lemma lem4464674 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term88 A K s t i) = (term89 A K s t i).
Proof. exact (@lem4464673 A (s i) (t i)). Qed.
Lemma lem4464681 {K : Type'} (i : K) (k : K -> Prop) : (term90 K i k) = (term90 K i k).
Proof. exact (eq_refl (term90 K i k)). Qed.
Lemma lem4464682 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term91 A K k s t i) = (term92 A K k s t i).
Proof. exact (MK_COMB (@lem4464681 K i k) (@lem4464674 A K s t i)). Qed.
Lemma lem4464685 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term93 A K k s t) = (term94 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4464682 A K k s t i)). Qed.
Lemma lem4464686 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4464687 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term95 A K k s t) = (term96 A K k s t).
Proof. exact (MK_COMB (@lem4464686 K) (@lem4464685 A K k s t)). Qed.
Lemma lem4464692 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term29 A K s k t) = (term95 A K k s t)) = ((term85 A K s k t) = (term96 A K k s t)).
Proof. exact (MK_COMB (@lem4464664 A K s k t) (@lem4464687 A K k s t)). Qed.
Lemma lem4464695 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term97 A K k s) = (term98 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4464692 A K k s t)). Qed.
Lemma lem4464696 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4464697 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term99 A K k s) = (term100 A K k s).
Proof. exact (MK_COMB (@lem4464696 A K) (@lem4464695 A K k s)). Qed.
Lemma lem4464702 {A K : Type'} (k : K -> Prop) : (term101 A K k) = (term102 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4464697 A K k s)). Qed.
Lemma lem4464703 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4464704 {A K : Type'} (k : K -> Prop) : (term103 A K k) = (term104 A K k).
Proof. exact (MK_COMB (@lem4464703 A K) (@lem4464702 A K k)). Qed.
Lemma lem4464709 {A K : Type'} : (term105 A K) = (term106 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4464704 A K k)). Qed.
Lemma lem4464710 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4464711 {A K : Type'} : (term107 A K) = (term108 A K).
Proof. exact (MK_COMB (@lem4464710 K) (@lem4464709 A K)). Qed.
Lemma lem4464716 {A K : Type'} : (term108 A K) = (term107 A K).
Proof. exact (SYM (@lem4464711 A K)). Qed.
Lemma lem4464744 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term12 _88435 _88436 a b P) = (P a b).
Proof. exact (EQ_MP (@lem4464482 _88435 _88436 P a b) (@lem4464481 _88435 _88436 P a b)). Qed.
Lemma lem4464745 {A K : Type'} (P : type1470 A K) (a : K) (b : A) : (term12 A K a b P) = (P a b).
Proof. exact (@lem4464744 A K P a b). Qed.
Lemma lem4464746 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term109 A K i x k t) = (term48 A K k t i x).
Proof. exact (@lem4464745 A K (term44 A K k t) i x). Qed.
Lemma lem4464747 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) : (term46 A K k t i) = (term47 A K k t i).
Proof. exact (eq_refl (term46 A K k t i)). Qed.
Lemma lem4464748 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4464749 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term48 A K k t i x) = (term49 A K k t i x).
Proof. exact (MK_COMB (@lem4464747 A K k t i) (@lem4464748 A x)). Qed.
Lemma lem4464750 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term49 A K k t i x) = (term50 A K k x t i).
Proof. exact (eq_refl (term49 A K k t i x)). Qed.
Lemma lem4464751 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term48 A K k t i x) = (term50 A K k x t i).
Proof. exact (TRANS (@lem4464749 A K k t i x) (@lem4464750 A K k x t i)). Qed.
Lemma lem4464752 {A K : Type'} (GEN_PVAR_143 : prod K A) : (@SETSPEC (prod K A) GEN_PVAR_143) = (@SETSPEC (prod K A) GEN_PVAR_143).
Proof. exact (eq_refl (@SETSPEC (prod K A) GEN_PVAR_143)). Qed.
Lemma lem4464753 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term51 A K GEN_PVAR_143 k t i x) = (term52 A K GEN_PVAR_143 k x t i).
Proof. exact (MK_COMB (@lem4464752 A K GEN_PVAR_143) (@lem4464751 A K k x t i)). Qed.
Lemma lem4464754 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4464755 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term53 A K GEN_PVAR_143 k t i x) = (term54 A K GEN_PVAR_143 k t i x).
Proof. exact (MK_COMB (@lem4464753 A K GEN_PVAR_143 k x t i) (@lem4464754 A K i x)). Qed.
Lemma lem4464756 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (t : type1470 A K) (i : K) : (term55 A K GEN_PVAR_143 k t i) = (term56 A K GEN_PVAR_143 k t i).
Proof. exact (fun_ext (fun x : A => @lem4464755 A K GEN_PVAR_143 k t i x)). Qed.
Lemma lem4464757 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4464758 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (t : type1470 A K) (i : K) : (term57 A K GEN_PVAR_143 k t i) = (term58 A K GEN_PVAR_143 k t i).
Proof. exact (MK_COMB (@lem4464757 A) (@lem4464756 A K GEN_PVAR_143 k t i)). Qed.
Lemma lem4464759 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (t : type1470 A K) : (term59 A K GEN_PVAR_143 k t) = (term60 A K GEN_PVAR_143 k t).
Proof. exact (fun_ext (fun i : K => @lem4464758 A K GEN_PVAR_143 k t i)). Qed.
Lemma lem4464760 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4464761 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (t : type1470 A K) : (term61 A K GEN_PVAR_143 k t) = (term62 A K GEN_PVAR_143 k t).
Proof. exact (MK_COMB (@lem4464760 K) (@lem4464759 A K GEN_PVAR_143 k t)). Qed.
Lemma lem4464762 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term63 A K k t) = (term64 A K k t).
Proof. exact (fun_ext (fun GEN_PVAR_143 : prod K A => @lem4464761 A K GEN_PVAR_143 k t)). Qed.
Lemma lem4464763 {A K : Type'} : (@GSPEC (prod K A)) = (@GSPEC (prod K A)).
Proof. exact (eq_refl (@GSPEC (prod K A))). Qed.
Lemma lem4464764 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term65 A K k t) = (term23 A K k t).
Proof. exact (MK_COMB (@lem4464763 A K) (@lem4464762 A K k t)). Qed.
Lemma lem4464765 {A K : Type'} (i : K) (x : A) : (term110 A K i x) = (term110 A K i x).
Proof. exact (eq_refl (term110 A K i x)). Qed.
Lemma lem4464766 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) : (term109 A K i x k t) = (term76 A K i x k t).
Proof. exact (MK_COMB (@lem4464765 A K i x) (@lem4464764 A K k t)). Qed.
Lemma lem4464767 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4464768 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) : (term111 A K i x k t) = (term112 A K i x k t).
Proof. exact (MK_COMB (@lem4464767) (@lem4464766 A K i x k t)). Qed.
Lemma lem4464769 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) : (term46 A K k t i) = (term47 A K k t i).
Proof. exact (eq_refl (term46 A K k t i)). Qed.
Lemma lem4464770 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4464771 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term48 A K k t i x) = (term49 A K k t i x).
Proof. exact (MK_COMB (@lem4464769 A K k t i) (@lem4464770 A x)). Qed.
Lemma lem4464772 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term49 A K k t i x) = (term50 A K k x t i).
Proof. exact (eq_refl (term49 A K k t i x)). Qed.
Lemma lem4464773 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term48 A K k t i x) = (term50 A K k x t i).
Proof. exact (TRANS (@lem4464771 A K k t i x) (@lem4464772 A K k x t i)). Qed.
Lemma lem4464774 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : ((term109 A K i x k t) = (term48 A K k t i x)) = ((term76 A K i x k t) = (term50 A K k x t i)).
Proof. exact (MK_COMB (@lem4464768 A K i x k t) (@lem4464773 A K k x t i)). Qed.
Lemma lem4464775 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term76 A K i x k t) = (term50 A K k x t i).
Proof. exact (EQ_MP (@lem4464774 A K k x t i) (@lem4464746 A K k t i x)). Qed.
Lemma lem4464778 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term74 A K k x s i) = (term74 A K k x s i).
Proof. exact (eq_refl (term74 A K k x s i)). Qed.
Lemma lem4464779 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term78 A K s i x k t) = (term113 A K s k x t i).
Proof. exact (MK_COMB (@lem4464778 A K k x s i) (@lem4464775 A K k x t i)). Qed.
Lemma lem4464782 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term80 A K s i k t) = (term114 A K s k t i).
Proof. exact (fun_ext (fun x : A => @lem4464779 A K s k x t i)). Qed.
Lemma lem4464783 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4464784 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term82 A K s i k t) = (term115 A K s k t i).
Proof. exact (MK_COMB (@lem4464783 A) (@lem4464782 A K s k t i)). Qed.
Lemma lem4464789 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term84 A K s k t) = (term116 A K s k t).
Proof. exact (fun_ext (fun i : K => @lem4464784 A K s k t i)). Qed.
Lemma lem4464790 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4464791 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term85 A K s k t) = (term117 A K s k t).
Proof. exact (MK_COMB (@lem4464790 K) (@lem4464789 A K s k t)). Qed.
Lemma lem4464796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4464797 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term87 A K s k t) = (term118 A K s k t).
Proof. exact (MK_COMB (@lem4464796) (@lem4464791 A K s k t)). Qed.
Lemma lem4464810 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term96 A K k s t) = (term96 A K k s t).
Proof. exact (eq_refl (term96 A K k s t)). Qed.
Lemma lem4464811 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term85 A K s k t) = (term96 A K k s t)) = ((term117 A K s k t) = (term96 A K k s t)).
Proof. exact (MK_COMB (@lem4464797 A K s k t) (@lem4464810 A K k s t)). Qed.
Lemma lem4464814 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term98 A K k s) = (term119 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4464811 A K k s t)). Qed.
Lemma lem4464815 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4464816 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term100 A K k s) = (term120 A K k s).
Proof. exact (MK_COMB (@lem4464815 A K) (@lem4464814 A K k s)). Qed.
Lemma lem4464821 {A K : Type'} (k : K -> Prop) : (term102 A K k) = (term121 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4464816 A K k s)). Qed.
Lemma lem4464822 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4464823 {A K : Type'} (k : K -> Prop) : (term104 A K k) = (term122 A K k).
Proof. exact (MK_COMB (@lem4464822 A K) (@lem4464821 A K k)). Qed.
Lemma lem4464828 {A K : Type'} : (term106 A K) = (term123 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4464823 A K k)). Qed.
Lemma lem4464829 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4464830 {A K : Type'} : (term108 A K) = (term124 A K).
Proof. exact (MK_COMB (@lem4464829 K) (@lem4464828 A K)). Qed.
Lemma lem4464835 {A K : Type'} : (term124 A K) = (term108 A K).
Proof. exact (SYM (@lem4464830 A K)). Qed.
Lemma lem4464907 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4464908 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4464907 K P x). Qed.
Lemma lem4464909 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4464908 K k i). Qed.
Lemma lem4464910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4464911 {K : Type'} (k : K -> Prop) (i : K) : (term125 K i k) = (term126 K k i).
Proof. exact (MK_COMB (@lem4464910) (@lem4464909 K k i)). Qed.
Lemma lem4464913 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4464914 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4464913 A P x). Qed.
Lemma lem4464915 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term127 A K x s i) = (s i x).
Proof. exact (@lem4464914 A (s i) x). Qed.
Lemma lem4464916 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term50 A K k x s i) = (term128 A K k s i x).
Proof. exact (MK_COMB (@lem4464911 K k i) (@lem4464915 A K s i x)). Qed.
Lemma lem4464919 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4464920 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term74 A K k x s i) = (term129 A K k s i x).
Proof. exact (MK_COMB (@lem4464919) (@lem4464916 A K k s i x)). Qed.
Lemma lem4464924 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4464925 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4464924 K P x). Qed.
Lemma lem4464926 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4464925 K k i). Qed.
Lemma lem4464927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4464928 {K : Type'} (k : K -> Prop) (i : K) : (term125 K i k) = (term126 K k i).
Proof. exact (MK_COMB (@lem4464927) (@lem4464926 K k i)). Qed.
Lemma lem4464930 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4464931 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4464930 A P x). Qed.
Lemma lem4464932 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term127 A K x t i) = (t i x).
Proof. exact (@lem4464931 A (t i) x). Qed.
Lemma lem4464933 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term50 A K k x t i) = (term128 A K k t i x).
Proof. exact (MK_COMB (@lem4464928 K k i) (@lem4464932 A K t i x)). Qed.
Lemma lem4464936 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term113 A K s k x t i) = (term130 A K s k t i x).
Proof. exact (MK_COMB (@lem4464920 A K k s i x) (@lem4464933 A K k t i x)). Qed.
Lemma lem4464939 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term114 A K s k t i) = (term131 A K s k t i).
Proof. exact (fun_ext (fun x : A => @lem4464936 A K s k t i x)). Qed.
Lemma lem4464940 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4464941 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term115 A K s k t i) = (term132 A K s k t i).
Proof. exact (MK_COMB (@lem4464940 A) (@lem4464939 A K s k t i)). Qed.
Lemma lem4464946 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term116 A K s k t) = (term133 A K s k t).
Proof. exact (fun_ext (fun i : K => @lem4464941 A K s k t i)). Qed.
Lemma lem4464947 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4464948 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term117 A K s k t) = (term134 A K s k t).
Proof. exact (MK_COMB (@lem4464947 K) (@lem4464946 A K s k t)). Qed.
Lemma lem4464953 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4464954 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term118 A K s k t) = (term135 A K s k t).
Proof. exact (MK_COMB (@lem4464953) (@lem4464948 A K s k t)). Qed.
Lemma lem4464962 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4464963 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4464962 K P x). Qed.
Lemma lem4464964 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4464963 K k i). Qed.
Lemma lem4464965 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4464966 {K : Type'} (k : K -> Prop) (i : K) : (term90 K i k) = (term136 K k i).
Proof. exact (MK_COMB (@lem4464965) (@lem4464964 K k i)). Qed.
Lemma lem4464974 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4464975 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4464974 A P x). Qed.
Lemma lem4464976 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term127 A K x s i) = (s i x).
Proof. exact (@lem4464975 A (s i) x). Qed.
Lemma lem4464977 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4464978 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term137 A K x s i) = (term138 A K s i x).
Proof. exact (MK_COMB (@lem4464977) (@lem4464976 A K s i x)). Qed.
Lemma lem4464980 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4464981 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4464980 A P x). Qed.
Lemma lem4464982 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term127 A K x t i) = (t i x).
Proof. exact (@lem4464981 A (t i) x). Qed.
Lemma lem4464983 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term139 A K s x t i) = (term140 A K s t i x).
Proof. exact (MK_COMB (@lem4464978 A K s i x) (@lem4464982 A K t i x)). Qed.
Lemma lem4464986 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term141 A K s t i) = (term142 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4464983 A K s t i x)). Qed.
Lemma lem4464987 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4464988 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term89 A K s t i) = (term143 A K s t i).
Proof. exact (MK_COMB (@lem4464987 A) (@lem4464986 A K s t i)). Qed.
Lemma lem4464993 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term92 A K k s t i) = (term144 A K k s t i).
Proof. exact (MK_COMB (@lem4464966 K k i) (@lem4464988 A K s t i)). Qed.
Lemma lem4464996 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term94 A K k s t) = (term145 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4464993 A K k s t i)). Qed.
Lemma lem4464997 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4464998 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term96 A K k s t) = (term146 A K k s t).
Proof. exact (MK_COMB (@lem4464997 K) (@lem4464996 A K k s t)). Qed.
Lemma lem4465003 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term117 A K s k t) = (term96 A K k s t)) = ((term134 A K s k t) = (term146 A K k s t)).
Proof. exact (MK_COMB (@lem4464954 A K s k t) (@lem4464998 A K k s t)). Qed.
Lemma lem4465006 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term119 A K k s) = (term147 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4465003 A K k s t)). Qed.
Lemma lem4465007 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4465008 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term120 A K k s) = (term148 A K k s).
Proof. exact (MK_COMB (@lem4465007 A K) (@lem4465006 A K k s)). Qed.
Lemma lem4465013 {A K : Type'} (k : K -> Prop) : (term121 A K k) = (term149 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4465008 A K k s)). Qed.
Lemma lem4465014 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4465015 {A K : Type'} (k : K -> Prop) : (term122 A K k) = (term150 A K k).
Proof. exact (MK_COMB (@lem4465014 A K) (@lem4465013 A K k)). Qed.
Lemma lem4465020 {A K : Type'} : (term123 A K) = (term151 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4465015 A K k)). Qed.
Lemma lem4465021 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4465022 {A K : Type'} : (term124 A K) = (term152 A K).
Proof. exact (MK_COMB (@lem4465021 K) (@lem4465020 A K)). Qed.
Lemma lem4465027 {A K : Type'} : (term152 A K) = (term124 A K).
Proof. exact (SYM (@lem4465022 A K)). Qed.
Lemma lem4465029 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4465030 {A K : Type'} : (term152 A K) = (term154 A K).
Proof. exact (@lem4465029 (term152 A K)). Qed.
Lemma lem4465031 {A K : Type'} : (term154 A K) = (term152 A K).
Proof. exact (SYM (@lem4465030 A K)). Qed.
Lemma lem4465032 {A K : Type'} (h1 : term155 A K) : term155 A K.
Proof. exact (h1). Qed.
Lemma lem4465035 {A K : Type'} (h1 : term154 A K) : term154 A K.
Proof. exact (h1). Qed.
Lemma lem4465036 {A K : Type'} : term156 A K.
Proof. exact (fun h0 : term154 A K => @lem4465035 A K h0). Qed.
Lemma lem4465037 {A K : Type'} (h1 : term156 A K) : term156 A K.
Proof. exact (h1). Qed.
Lemma lem4465038 {A K : Type'} (h1 : term154 A K) : term154 A K.
Proof. exact (h1). Qed.
Lemma lem4465039 {A K : Type'} (h1 : term154 A K) (h2 : term156 A K) : term154 A K.
Proof. exact (@lem4465037 A K h2 (@lem4465038 A K h1)). Qed.
Lemma lem4465040 {A K : Type'} (h1 : term154 A K) : term157 A K.
Proof. exact (fun h0 : term156 A K => @lem4465039 A K h1 h0). Qed.
Lemma lem4465041 {A K : Type'} (h1 : term156 A K) : term156 A K.
Proof. exact (h1). Qed.
Lemma lem4465042 {A K : Type'} (h1 : term154 A K) (h2 : term156 A K) : term154 A K.
Proof. exact (@lem4465040 A K h1 (@lem4465041 A K h2)). Qed.
Lemma lem4465043 {A K : Type'} (h1 : term156 A K) : term156 A K.
Proof. exact (fun h0 : term154 A K => @lem4465042 A K h0 h1). Qed.
Lemma lem4465044 {A K : Type'} : term158 A K.
Proof. exact (fun h0 : term156 A K => @lem4465043 A K h0). Qed.
Lemma lem4465047 {A K : Type'} : term156 A K.
Proof. exact (@lem4465044 A K (@lem4465036 A K)). Qed.
Lemma lem4465048 {A K : Type'} : term156 A K.
Proof. exact (@lem4465047 A K). Qed.
Lemma lem4465050 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4465051 {A K : Type'} : (term154 A K) = (term159 A K).
Proof. exact (@lem4465050 (term155 A K)). Qed.
Lemma lem4465053 (t : Prop) : (term160 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4465054 {A K : Type'} : (term159 A K) = (term152 A K).
Proof. exact (@lem4465053 (term152 A K)). Qed.
Lemma lem4465097 {A K : Type'} : (term154 A K) = (term152 A K).
Proof. exact (TRANS (@lem4465051 A K) (@lem4465054 A K)). Qed.
Lemma lem4465102 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term140 A K s t i x) = (term140 A K s t i x).
Proof. exact (eq_refl (term140 A K s t i x)). Qed.
Lemma lem4465103 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term142 A K s t i) = (term142 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4465102 A K s t i x)). Qed.
Lemma lem4465104 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4465105 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term143 A K s t i) = (term143 A K s t i).
Proof. exact (MK_COMB (@lem4465104 A) (@lem4465103 A K s t i)). Qed.
Lemma lem4465108 {K : Type'} (k : K -> Prop) (i : K) : (term136 K k i) = (term136 K k i).
Proof. exact (eq_refl (term136 K k i)). Qed.
Lemma lem4465109 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term144 A K k s t i) = (term144 A K k s t i).
Proof. exact (MK_COMB (@lem4465108 K k i) (@lem4465105 A K s t i)). Qed.
Lemma lem4465110 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term145 A K k s t) = (term145 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4465109 A K k s t i)). Qed.
Lemma lem4465111 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4465112 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term146 A K k s t) = (term146 A K k s t).
Proof. exact (MK_COMB (@lem4465111 K) (@lem4465110 A K k s t)). Qed.
Lemma lem4465125 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term130 A K s k t i x) = (term130 A K s k t i x).
Proof. exact (eq_refl (term130 A K s k t i x)). Qed.
Lemma lem4465126 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term131 A K s k t i) = (term131 A K s k t i).
Proof. exact (fun_ext (fun x : A => @lem4465125 A K s k t i x)). Qed.
Lemma lem4465127 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4465128 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term132 A K s k t i) = (term132 A K s k t i).
Proof. exact (MK_COMB (@lem4465127 A) (@lem4465126 A K s k t i)). Qed.
Lemma lem4465129 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term133 A K s k t) = (term133 A K s k t).
Proof. exact (fun_ext (fun i : K => @lem4465128 A K s k t i)). Qed.
Lemma lem4465130 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4465131 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term134 A K s k t) = (term134 A K s k t).
Proof. exact (MK_COMB (@lem4465130 K) (@lem4465129 A K s k t)). Qed.
Lemma lem4465132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4465133 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term135 A K s k t) = (term135 A K s k t).
Proof. exact (MK_COMB (@lem4465132) (@lem4465131 A K s k t)). Qed.
Lemma lem4465134 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term134 A K s k t) = (term146 A K k s t)) = ((term134 A K s k t) = (term146 A K k s t)).
Proof. exact (MK_COMB (@lem4465133 A K s k t) (@lem4465112 A K k s t)). Qed.
Lemma lem4465135 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term147 A K k s) = (term147 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4465134 A K k s t)). Qed.
Lemma lem4465136 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4465137 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term148 A K k s) = (term148 A K k s).
Proof. exact (MK_COMB (@lem4465136 A K) (@lem4465135 A K k s)). Qed.
Lemma lem4465138 {A K : Type'} (k : K -> Prop) : (term149 A K k) = (term149 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4465137 A K k s)). Qed.
Lemma lem4465139 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4465140 {A K : Type'} (k : K -> Prop) : (term150 A K k) = (term150 A K k).
Proof. exact (MK_COMB (@lem4465139 A K) (@lem4465138 A K k)). Qed.
Lemma lem4465141 {A K : Type'} : (term151 A K) = (term151 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4465140 A K k)). Qed.
Lemma lem4465142 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4465143 {A K : Type'} : (term152 A K) = (term152 A K).
Proof. exact (MK_COMB (@lem4465142 K) (@lem4465141 A K)). Qed.
Lemma lem4465198 {A K : Type'} : (term154 A K) = (term152 A K).
Proof. exact (TRANS (@lem4465097 A K) (@lem4465143 A K)). Qed.
Lemma lem4465199 {A K : Type'} : (term152 A K) = (term154 A K).
Proof. exact (SYM (@lem4465198 A K)). Qed.
Lemma lem4465201 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4465202 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term134 A K s k t) = (term146 A K k s t)) = (term161 A K k s t).
Proof. exact (@lem4465201 ((term134 A K s k t) = (term146 A K k s t))). Qed.
Lemma lem4465203 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term161 A K k s t) = ((term134 A K s k t) = (term146 A K k s t)).
Proof. exact (SYM (@lem4465202 A K k s t)). Qed.
Lemma lem4465204 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term162 A K k s t) : term162 A K k s t.
Proof. exact (h1). Qed.
Lemma lem4465213 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term163 A K k s i x) = (term164 A K k s i x).
Proof. exact (@lem17045 (k i) (s i x)). Qed.
Lemma lem4465225 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term163 A K k t i x) = (term164 A K k t i x).
Proof. exact (@lem17045 (k i) (t i x)). Qed.
Lemma lem4465228 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term128 A K k t i x) = (term128 A K k t i x).
Proof. exact (eq_refl (term128 A K k t i x)). Qed.
Lemma lem4465230 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term165 A K k s i x) = (term165 A K k s i x).
Proof. exact (eq_refl (term165 A K k s i x)). Qed.
Lemma lem4465231 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term166 A K s k t i x) = (term167 A K s k t i x).
Proof. exact (MK_COMB (@lem4465230 A K k s i x) (@lem4465225 A K k t i x)). Qed.
Lemma lem4465232 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term168 A K s k t i x) = (term166 A K s k t i x).
Proof. exact (@lem17362 (term128 A K k s i x) (term128 A K k t i x)). Qed.
Lemma lem4465233 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term168 A K s k t i x) = (term167 A K s k t i x).
Proof. exact (TRANS (@lem4465232 A K s k t i x) (@lem4465231 A K s k t i x)). Qed.
Lemma lem4465234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4465235 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term169 A K k s i x) = (term170 A K k s i x).
Proof. exact (MK_COMB (@lem4465234) (@lem4465213 A K k s i x)). Qed.
Lemma lem4465236 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term171 A K s k t i x) = (term172 A K s k t i x).
Proof. exact (MK_COMB (@lem4465235 A K k s i x) (@lem4465228 A K k t i x)). Qed.
Lemma lem4465237 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term130 A K s k t i x) = (term171 A K s k t i x).
Proof. exact (@lem17265 (term128 A K k s i x) (term128 A K k t i x)). Qed.
Lemma lem4465238 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term130 A K s k t i x) = (term172 A K s k t i x).
Proof. exact (TRANS (@lem4465237 A K s k t i x) (@lem4465236 A K s k t i x)). Qed.
Lemma lem4465239 {A : Type'} (P : A -> Prop) : (term173 A P) = (term174 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4465240 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term175 A K s k t i) = (term176 A K s k t i).
Proof. exact (@lem4465239 A (term131 A K s k t i)). Qed.
Lemma lem4465241 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term177 A K s k t i x) = (term130 A K s k t i x).
Proof. exact (eq_refl (term177 A K s k t i x)). Qed.
Lemma lem4465242 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4465243 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term178 A K s k t i x) = (term168 A K s k t i x).
Proof. exact (MK_COMB (@lem4465242) (@lem4465241 A K s k t i x)). Qed.
Lemma lem4465244 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term178 A K s k t i x) = (term167 A K s k t i x).
Proof. exact (TRANS (@lem4465243 A K s k t i x) (@lem4465233 A K s k t i x)). Qed.
Lemma lem4465245 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term179 A K s k t i) = (term180 A K s k t i).
Proof. exact (fun_ext (fun x : A => @lem4465244 A K s k t i x)). Qed.
Lemma lem4465246 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4465247 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term176 A K s k t i) = (term181 A K s k t i).
Proof. exact (MK_COMB (@lem4465246 A) (@lem4465245 A K s k t i)). Qed.
Lemma lem4465248 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term175 A K s k t i) = (term181 A K s k t i).
Proof. exact (TRANS (@lem4465240 A K s k t i) (@lem4465247 A K s k t i)). Qed.
Lemma lem4465249 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term131 A K s k t i) = (term182 A K s k t i).
Proof. exact (fun_ext (fun x : A => @lem4465238 A K s k t i x)). Qed.
Lemma lem4465250 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4465251 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term132 A K s k t i) = (term183 A K s k t i).
Proof. exact (MK_COMB (@lem4465250 A) (@lem4465249 A K s k t i)). Qed.
Lemma lem4465252 {K : Type'} (P : K -> Prop) : (term173 K P) = (term174 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4465253 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term184 A K s k t) = (term185 A K s k t).
Proof. exact (@lem4465252 K (term133 A K s k t)). Qed.
Lemma lem4465254 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term186 A K s k t i) = (term132 A K s k t i).
Proof. exact (eq_refl (term186 A K s k t i)). Qed.
Lemma lem4465255 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4465256 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term187 A K s k t i) = (term175 A K s k t i).
Proof. exact (MK_COMB (@lem4465255) (@lem4465254 A K s k t i)). Qed.
Lemma lem4465257 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term187 A K s k t i) = (term181 A K s k t i).
Proof. exact (TRANS (@lem4465256 A K s k t i) (@lem4465248 A K s k t i)). Qed.
Lemma lem4465258 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term188 A K s k t) = (term189 A K s k t).
Proof. exact (fun_ext (fun i : K => @lem4465257 A K s k t i)). Qed.
Lemma lem4465259 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4465260 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term185 A K s k t) = (term190 A K s k t).
Proof. exact (MK_COMB (@lem4465259 K) (@lem4465258 A K s k t)). Qed.
Lemma lem4465261 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term184 A K s k t) = (term190 A K s k t).
Proof. exact (TRANS (@lem4465253 A K s k t) (@lem4465260 A K s k t)). Qed.
Lemma lem4465262 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term133 A K s k t) = (term191 A K s k t).
Proof. exact (fun_ext (fun i : K => @lem4465251 A K s k t i)). Qed.
Lemma lem4465263 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4465264 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term134 A K s k t) = (term192 A K s k t).
Proof. exact (MK_COMB (@lem4465263 K) (@lem4465262 A K s k t)). Qed.
Lemma lem4465275 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term193 A K s t i x) = (term194 A K s t i x).
Proof. exact (@lem17362 (s i x) (t i x)). Qed.
Lemma lem4465280 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term140 A K s t i x) = (term195 A K s t i x).
Proof. exact (@lem17265 (s i x) (t i x)). Qed.
Lemma lem4465281 {A : Type'} (P : A -> Prop) : (term173 A P) = (term174 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4465282 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term196 A K s t i) = (term197 A K s t i).
Proof. exact (@lem4465281 A (term142 A K s t i)). Qed.
Lemma lem4465283 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term198 A K s t i x) = (term140 A K s t i x).
Proof. exact (eq_refl (term198 A K s t i x)). Qed.
Lemma lem4465284 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4465285 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term199 A K s t i x) = (term193 A K s t i x).
Proof. exact (MK_COMB (@lem4465284) (@lem4465283 A K s t i x)). Qed.
Lemma lem4465286 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term199 A K s t i x) = (term194 A K s t i x).
Proof. exact (TRANS (@lem4465285 A K s t i x) (@lem4465275 A K s t i x)). Qed.
Lemma lem4465287 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term200 A K s t i) = (term201 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4465286 A K s t i x)). Qed.
Lemma lem4465288 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4465289 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term197 A K s t i) = (term202 A K s t i).
Proof. exact (MK_COMB (@lem4465288 A) (@lem4465287 A K s t i)). Qed.
Lemma lem4465290 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term196 A K s t i) = (term202 A K s t i).
Proof. exact (TRANS (@lem4465282 A K s t i) (@lem4465289 A K s t i)). Qed.
Lemma lem4465291 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term142 A K s t i) = (term203 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4465280 A K s t i x)). Qed.
Lemma lem4465292 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4465293 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term143 A K s t i) = (term204 A K s t i).
Proof. exact (MK_COMB (@lem4465292 A) (@lem4465291 A K s t i)). Qed.
Lemma lem4465295 {K : Type'} (k : K -> Prop) (i : K) : (term126 K k i) = (term126 K k i).
Proof. exact (eq_refl (term126 K k i)). Qed.
Lemma lem4465296 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term205 A K k s t i) = (term206 A K k s t i).
Proof. exact (MK_COMB (@lem4465295 K k i) (@lem4465290 A K s t i)). Qed.
Lemma lem4465297 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term207 A K k s t i) = (term205 A K k s t i).
Proof. exact (@lem17362 (k i) (term143 A K s t i)). Qed.
Lemma lem4465298 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term207 A K k s t i) = (term206 A K k s t i).
Proof. exact (TRANS (@lem4465297 A K k s t i) (@lem4465296 A K k s t i)). Qed.
Lemma lem4465300 {K : Type'} (k : K -> Prop) (i : K) : (term208 K k i) = (term208 K k i).
Proof. exact (eq_refl (term208 K k i)). Qed.
Lemma lem4465301 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term209 A K k s t i) = (term210 A K k s t i).
Proof. exact (MK_COMB (@lem4465300 K k i) (@lem4465293 A K s t i)). Qed.
Lemma lem4465302 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term144 A K k s t i) = (term209 A K k s t i).
Proof. exact (@lem17265 (k i) (term143 A K s t i)). Qed.
Lemma lem4465303 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term144 A K k s t i) = (term210 A K k s t i).
Proof. exact (TRANS (@lem4465302 A K k s t i) (@lem4465301 A K k s t i)). Qed.
Lemma lem4465304 {K : Type'} (P : K -> Prop) : (term173 K P) = (term174 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4465305 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term211 A K k s t) = (term212 A K k s t).
Proof. exact (@lem4465304 K (term145 A K k s t)). Qed.
Lemma lem4465306 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term213 A K k s t i) = (term144 A K k s t i).
Proof. exact (eq_refl (term213 A K k s t i)). Qed.
Lemma lem4465307 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4465308 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term214 A K k s t i) = (term207 A K k s t i).
Proof. exact (MK_COMB (@lem4465307) (@lem4465306 A K k s t i)). Qed.
Lemma lem4465309 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term214 A K k s t i) = (term206 A K k s t i).
Proof. exact (TRANS (@lem4465308 A K k s t i) (@lem4465298 A K k s t i)). Qed.
Lemma lem4465310 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term215 A K k s t) = (term216 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4465309 A K k s t i)). Qed.
Lemma lem4465311 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4465312 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term212 A K k s t) = (term217 A K k s t).
Proof. exact (MK_COMB (@lem4465311 K) (@lem4465310 A K k s t)). Qed.
Lemma lem4465313 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term211 A K k s t) = (term217 A K k s t).
Proof. exact (TRANS (@lem4465305 A K k s t) (@lem4465312 A K k s t)). Qed.
Lemma lem4465314 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term145 A K k s t) = (term218 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4465303 A K k s t i)). Qed.
Lemma lem4465315 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4465316 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term146 A K k s t) = (term219 A K k s t).
Proof. exact (MK_COMB (@lem4465315 K) (@lem4465314 A K k s t)). Qed.
Lemma lem4465317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4465318 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term220 A K s k t) = (term221 A K s k t).
Proof. exact (MK_COMB (@lem4465317) (@lem4465261 A K s k t)). Qed.
Lemma lem4465319 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term222 A K k s t) = (term223 A K k s t).
Proof. exact (MK_COMB (@lem4465318 A K s k t) (@lem4465316 A K k s t)). Qed.
Lemma lem4465320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4465321 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term224 A K s k t) = (term225 A K s k t).
Proof. exact (MK_COMB (@lem4465320) (@lem4465264 A K s k t)). Qed.
Lemma lem4465322 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term226 A K k s t) = (term227 A K k s t).
Proof. exact (MK_COMB (@lem4465321 A K s k t) (@lem4465313 A K k s t)). Qed.
Lemma lem4465323 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4465324 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term228 A K k s t) = (term229 A K k s t).
Proof. exact (MK_COMB (@lem4465323) (@lem4465322 A K k s t)). Qed.
Lemma lem4465325 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term230 A K k s t) = (term231 A K k s t).
Proof. exact (MK_COMB (@lem4465324 A K k s t) (@lem4465319 A K k s t)). Qed.
Lemma lem4465326 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term162 A K k s t) = (term230 A K k s t).
Proof. exact (@lem17646 (term134 A K s k t) (term146 A K k s t)). Qed.
Lemma lem4465327 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term162 A K k s t) = (term231 A K k s t).
Proof. exact (TRANS (@lem4465326 A K k s t) (@lem4465325 A K k s t)). Qed.
Lemma lem4465606 {A : Type'} (P : Prop) (Q : A -> Prop) : (term232 A P Q) = (term233 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4465607 {A : Type'} (P : Prop) (Q : A -> Prop) : (term232 A P Q) = (term233 A P Q).
Proof. exact (@lem4465606 A P Q). Qed.
Lemma lem4465608 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term234 A K k s t i) = (term235 A K k s t i).
Proof. exact (@lem4465607 A (k i) (term201 A K s t i)). Qed.
Lemma lem4465609 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term236 A K s t i x) = (term194 A K s t i x).
Proof. exact (eq_refl (term236 A K s t i x)). Qed.
Lemma lem4465610 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term237 A K s t i) = (term201 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4465609 A K s t i x)). Qed.
Lemma lem4465611 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4465612 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term238 A K s t i) = (term202 A K s t i).
Proof. exact (MK_COMB (@lem4465611 A) (@lem4465610 A K s t i)). Qed.
Lemma lem4465613 {K : Type'} (k : K -> Prop) (i : K) : (term126 K k i) = (term126 K k i).
Proof. exact (eq_refl (term126 K k i)). Qed.
Lemma lem4465614 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term234 A K k s t i) = (term206 A K k s t i).
Proof. exact (MK_COMB (@lem4465613 K k i) (@lem4465612 A K s t i)). Qed.
Lemma lem4465615 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4465616 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term239 A K k s t i) = (term240 A K k s t i).
Proof. exact (MK_COMB (@lem4465615) (@lem4465614 A K k s t i)). Qed.
Lemma lem4465617 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term236 A K s t i x) = (term194 A K s t i x).
Proof. exact (eq_refl (term236 A K s t i x)). Qed.
Lemma lem4465618 {K : Type'} (k : K -> Prop) (i : K) : (term126 K k i) = (term126 K k i).
Proof. exact (eq_refl (term126 K k i)). Qed.
Lemma lem4465619 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term241 A K k s t i x) = (term242 A K k s t i x).
Proof. exact (MK_COMB (@lem4465618 K k i) (@lem4465617 A K s t i x)). Qed.
Lemma lem4465620 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term243 A K k s t i) = (term244 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4465619 A K k s t i x)). Qed.
Lemma lem4465621 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4465622 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term235 A K k s t i) = (term245 A K k s t i).
Proof. exact (MK_COMB (@lem4465621 A) (@lem4465620 A K k s t i)). Qed.
Lemma lem4465623 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : ((term234 A K k s t i) = (term235 A K k s t i)) = ((term206 A K k s t i) = (term245 A K k s t i)).
Proof. exact (MK_COMB (@lem4465616 A K k s t i) (@lem4465622 A K k s t i)). Qed.
Lemma lem4465624 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term206 A K k s t i) = (term245 A K k s t i).
Proof. exact (EQ_MP (@lem4465623 A K k s t i) (@lem4465608 A K k s t i)). Qed.
Lemma lem4465625 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term216 A K k s t) = (term246 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4465624 A K k s t i)). Qed.
Lemma lem4465626 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4465627 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term217 A K k s t) = (term247 A K k s t).
Proof. exact (MK_COMB (@lem4465626 K) (@lem4465625 A K k s t)). Qed.
Lemma lem4465628 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term225 A K s k t) = (term225 A K s k t).
Proof. exact (eq_refl (term225 A K s k t)). Qed.
Lemma lem4465629 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term227 A K k s t) = (term248 A K k s t).
Proof. exact (MK_COMB (@lem4465628 A K s k t) (@lem4465627 A K k s t)). Qed.
Lemma lem4465631 {A : Type'} (P : Prop) (Q : A -> Prop) : (term232 A P Q) = (term233 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4465632 {K : Type'} (P : Prop) (Q : K -> Prop) : (term232 K P Q) = (term233 K P Q).
Proof. exact (@lem4465631 K P Q). Qed.
Lemma lem4465633 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term249 A K k s t) = (term250 A K k s t).
Proof. exact (@lem4465632 K (term192 A K s k t) (term246 A K k s t)). Qed.
Lemma lem4465634 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term251 A K k s t i) = (term245 A K k s t i).
Proof. exact (eq_refl (term251 A K k s t i)). Qed.
Lemma lem4465635 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term252 A K k s t) = (term246 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4465634 A K k s t i)). Qed.
Lemma lem4465636 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4465637 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term253 A K k s t) = (term247 A K k s t).
Proof. exact (MK_COMB (@lem4465636 K) (@lem4465635 A K k s t)). Qed.
Lemma lem4465638 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term225 A K s k t) = (term225 A K s k t).
Proof. exact (eq_refl (term225 A K s k t)). Qed.
Lemma lem4465639 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term249 A K k s t) = (term248 A K k s t).
Proof. exact (MK_COMB (@lem4465638 A K s k t) (@lem4465637 A K k s t)). Qed.
Lemma lem4465640 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4465641 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term254 A K k s t) = (term255 A K k s t).
Proof. exact (MK_COMB (@lem4465640) (@lem4465639 A K k s t)). Qed.
Lemma lem4465642 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term251 A K k s t i) = (term245 A K k s t i).
Proof. exact (eq_refl (term251 A K k s t i)). Qed.
Lemma lem4465643 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term225 A K s k t) = (term225 A K s k t).
Proof. exact (eq_refl (term225 A K s k t)). Qed.
Lemma lem4465644 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term256 A K k s t i) = (term257 A K k s t i).
Proof. exact (MK_COMB (@lem4465643 A K s k t) (@lem4465642 A K k s t i)). Qed.
Lemma lem4465645 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term258 A K k s t) = (term259 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4465644 A K k s t i)). Qed.
Lemma lem4465646 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4465647 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term250 A K k s t) = (term260 A K k s t).
Proof. exact (MK_COMB (@lem4465646 K) (@lem4465645 A K k s t)). Qed.
Lemma lem4465648 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term249 A K k s t) = (term250 A K k s t)) = ((term248 A K k s t) = (term260 A K k s t)).
Proof. exact (MK_COMB (@lem4465641 A K k s t) (@lem4465647 A K k s t)). Qed.
Lemma lem4465649 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term248 A K k s t) = (term260 A K k s t).
Proof. exact (EQ_MP (@lem4465648 A K k s t) (@lem4465633 A K k s t)). Qed.
Lemma lem4465651 {A : Type'} (P : Prop) (Q : A -> Prop) : (term232 A P Q) = (term233 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4465652 {A : Type'} (P : Prop) (Q : A -> Prop) : (term232 A P Q) = (term233 A P Q).
Proof. exact (@lem4465651 A P Q). Qed.
Lemma lem4465653 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term261 A K k s t i) = (term262 A K k s t i).
Proof. exact (@lem4465652 A (term192 A K s k t) (term244 A K k s t i)). Qed.
Lemma lem4465654 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term263 A K k s t i x) = (term242 A K k s t i x).
Proof. exact (eq_refl (term263 A K k s t i x)). Qed.
Lemma lem4465655 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term264 A K k s t i) = (term244 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4465654 A K k s t i x)). Qed.
Lemma lem4465656 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4465657 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term265 A K k s t i) = (term245 A K k s t i).
Proof. exact (MK_COMB (@lem4465656 A) (@lem4465655 A K k s t i)). Qed.
Lemma lem4465658 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term225 A K s k t) = (term225 A K s k t).
Proof. exact (eq_refl (term225 A K s k t)). Qed.
Lemma lem4465659 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term261 A K k s t i) = (term257 A K k s t i).
Proof. exact (MK_COMB (@lem4465658 A K s k t) (@lem4465657 A K k s t i)). Qed.
Lemma lem4465660 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4465661 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term266 A K k s t i) = (term267 A K k s t i).
Proof. exact (MK_COMB (@lem4465660) (@lem4465659 A K k s t i)). Qed.
Lemma lem4465662 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term263 A K k s t i x) = (term242 A K k s t i x).
Proof. exact (eq_refl (term263 A K k s t i x)). Qed.
Lemma lem4465663 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term225 A K s k t) = (term225 A K s k t).
Proof. exact (eq_refl (term225 A K s k t)). Qed.
Lemma lem4465664 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term268 A K k s t i x) = (term269 A K k s t i x).
Proof. exact (MK_COMB (@lem4465663 A K s k t) (@lem4465662 A K k s t i x)). Qed.
Lemma lem4465665 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term270 A K k s t i) = (term271 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4465664 A K k s t i x)). Qed.
Lemma lem4465666 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4465667 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term262 A K k s t i) = (term272 A K k s t i).
Proof. exact (MK_COMB (@lem4465666 A) (@lem4465665 A K k s t i)). Qed.
Lemma lem4465668 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : ((term261 A K k s t i) = (term262 A K k s t i)) = ((term257 A K k s t i) = (term272 A K k s t i)).
Proof. exact (MK_COMB (@lem4465661 A K k s t i) (@lem4465667 A K k s t i)). Qed.
Lemma lem4465669 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term257 A K k s t i) = (term272 A K k s t i).
Proof. exact (EQ_MP (@lem4465668 A K k s t i) (@lem4465653 A K k s t i)). Qed.
Lemma lem4465670 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term259 A K k s t) = (term273 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4465669 A K k s t i)). Qed.
Lemma lem4465671 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4465672 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term260 A K k s t) = (term274 A K k s t).
Proof. exact (MK_COMB (@lem4465671 K) (@lem4465670 A K k s t)). Qed.
Lemma lem4465673 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term248 A K k s t) = (term274 A K k s t).
Proof. exact (TRANS (@lem4465649 A K k s t) (@lem4465672 A K k s t)). Qed.
Lemma lem4465674 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term227 A K k s t) = (term274 A K k s t).
Proof. exact (TRANS (@lem4465629 A K k s t) (@lem4465673 A K k s t)). Qed.
Lemma lem4465675 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4465676 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term229 A K k s t) = (term275 A K k s t).
Proof. exact (MK_COMB (@lem4465675) (@lem4465674 A K k s t)). Qed.
Lemma lem4465678 {A : Type'} (P : A -> Prop) (Q : Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4465679 {K : Type'} (P : K -> Prop) (Q : Prop) : (term276 K P Q) = (term277 K P Q).
Proof. exact (@lem4465678 K P Q). Qed.
Lemma lem4465680 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term278 A K k s t) = (term279 A K k s t).
Proof. exact (@lem4465679 K (term189 A K s k t) (term219 A K k s t)). Qed.
Lemma lem4465681 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term280 A K s k t i) = (term181 A K s k t i).
Proof. exact (eq_refl (term280 A K s k t i)). Qed.
Lemma lem4465682 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term281 A K s k t) = (term189 A K s k t).
Proof. exact (fun_ext (fun i : K => @lem4465681 A K s k t i)). Qed.
Lemma lem4465683 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4465684 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term282 A K s k t) = (term190 A K s k t).
Proof. exact (MK_COMB (@lem4465683 K) (@lem4465682 A K s k t)). Qed.
Lemma lem4465685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4465686 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term283 A K s k t) = (term221 A K s k t).
Proof. exact (MK_COMB (@lem4465685) (@lem4465684 A K s k t)). Qed.
Lemma lem4465687 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term219 A K k s t) = (term219 A K k s t).
Proof. exact (eq_refl (term219 A K k s t)). Qed.
Lemma lem4465688 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term278 A K k s t) = (term223 A K k s t).
Proof. exact (MK_COMB (@lem4465686 A K s k t) (@lem4465687 A K k s t)). Qed.
Lemma lem4465689 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4465690 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term284 A K k s t) = (term285 A K k s t).
Proof. exact (MK_COMB (@lem4465689) (@lem4465688 A K k s t)). Qed.
Lemma lem4465691 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term280 A K s k t i) = (term181 A K s k t i).
Proof. exact (eq_refl (term280 A K s k t i)). Qed.
Lemma lem4465692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4465693 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term286 A K s k t i) = (term287 A K s k t i).
Proof. exact (MK_COMB (@lem4465692) (@lem4465691 A K s k t i)). Qed.
Lemma lem4465694 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term219 A K k s t) = (term219 A K k s t).
Proof. exact (eq_refl (term219 A K k s t)). Qed.
Lemma lem4465695 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term288 A K i k s t) = (term289 A K i k s t).
Proof. exact (MK_COMB (@lem4465693 A K s k t i) (@lem4465694 A K k s t)). Qed.
Lemma lem4465696 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term290 A K k s t) = (term291 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4465695 A K i k s t)). Qed.
Lemma lem4465697 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4465698 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term279 A K k s t) = (term292 A K k s t).
Proof. exact (MK_COMB (@lem4465697 K) (@lem4465696 A K k s t)). Qed.
Lemma lem4465699 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term278 A K k s t) = (term279 A K k s t)) = ((term223 A K k s t) = (term292 A K k s t)).
Proof. exact (MK_COMB (@lem4465690 A K k s t) (@lem4465698 A K k s t)). Qed.
Lemma lem4465700 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term223 A K k s t) = (term292 A K k s t).
Proof. exact (EQ_MP (@lem4465699 A K k s t) (@lem4465680 A K k s t)). Qed.
Lemma lem4465702 {A : Type'} (P : A -> Prop) (Q : Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4465703 {A : Type'} (P : A -> Prop) (Q : Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (@lem4465702 A P Q). Qed.
Lemma lem4465704 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term293 A K i k s t) = (term294 A K i k s t).
Proof. exact (@lem4465703 A (term180 A K s k t i) (term219 A K k s t)). Qed.
Lemma lem4465705 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term295 A K s k t i x) = (term167 A K s k t i x).
Proof. exact (eq_refl (term295 A K s k t i x)). Qed.
Lemma lem4465706 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term296 A K s k t i) = (term180 A K s k t i).
Proof. exact (fun_ext (fun x : A => @lem4465705 A K s k t i x)). Qed.
Lemma lem4465707 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4465708 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term297 A K s k t i) = (term181 A K s k t i).
Proof. exact (MK_COMB (@lem4465707 A) (@lem4465706 A K s k t i)). Qed.
Lemma lem4465709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4465710 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term298 A K s k t i) = (term287 A K s k t i).
Proof. exact (MK_COMB (@lem4465709) (@lem4465708 A K s k t i)). Qed.
Lemma lem4465711 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term219 A K k s t) = (term219 A K k s t).
Proof. exact (eq_refl (term219 A K k s t)). Qed.
Lemma lem4465712 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term293 A K i k s t) = (term289 A K i k s t).
Proof. exact (MK_COMB (@lem4465710 A K s k t i) (@lem4465711 A K k s t)). Qed.
Lemma lem4465713 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4465714 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term299 A K i k s t) = (term300 A K i k s t).
Proof. exact (MK_COMB (@lem4465713) (@lem4465712 A K i k s t)). Qed.
Lemma lem4465715 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term295 A K s k t i x) = (term167 A K s k t i x).
Proof. exact (eq_refl (term295 A K s k t i x)). Qed.
Lemma lem4465716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4465717 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term301 A K s k t i x) = (term302 A K s k t i x).
Proof. exact (MK_COMB (@lem4465716) (@lem4465715 A K s k t i x)). Qed.
Lemma lem4465718 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term219 A K k s t) = (term219 A K k s t).
Proof. exact (eq_refl (term219 A K k s t)). Qed.
Lemma lem4465719 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term303 A K i x k s t) = (term304 A K i x k s t).
Proof. exact (MK_COMB (@lem4465717 A K s k t i x) (@lem4465718 A K k s t)). Qed.
Lemma lem4465720 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term305 A K i k s t) = (term306 A K i k s t).
Proof. exact (fun_ext (fun x : A => @lem4465719 A K i x k s t)). Qed.
Lemma lem4465721 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4465722 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term294 A K i k s t) = (term307 A K i k s t).
Proof. exact (MK_COMB (@lem4465721 A) (@lem4465720 A K i k s t)). Qed.
Lemma lem4465723 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term293 A K i k s t) = (term294 A K i k s t)) = ((term289 A K i k s t) = (term307 A K i k s t)).
Proof. exact (MK_COMB (@lem4465714 A K i k s t) (@lem4465722 A K i k s t)). Qed.
Lemma lem4465724 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term289 A K i k s t) = (term307 A K i k s t).
Proof. exact (EQ_MP (@lem4465723 A K i k s t) (@lem4465704 A K i k s t)). Qed.
Lemma lem4465725 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term291 A K k s t) = (term308 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4465724 A K i k s t)). Qed.
Lemma lem4465726 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4465727 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term292 A K k s t) = (term309 A K k s t).
Proof. exact (MK_COMB (@lem4465726 K) (@lem4465725 A K k s t)). Qed.
Lemma lem4465728 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term223 A K k s t) = (term309 A K k s t).
Proof. exact (TRANS (@lem4465700 A K k s t) (@lem4465727 A K k s t)). Qed.
Lemma lem4465729 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term231 A K k s t) = (term310 A K k s t).
Proof. exact (MK_COMB (@lem4465676 A K k s t) (@lem4465728 A K k s t)). Qed.
Lemma lem4465731 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term311 A P Q) = (term312 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4465732 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term311 K P Q) = (term312 K P Q).
Proof. exact (@lem4465731 K P Q). Qed.
Lemma lem4465733 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term313 A K k s t) = (term314 A K k s t).
Proof. exact (@lem4465732 K (term273 A K k s t) (term308 A K k s t)). Qed.
Lemma lem4465734 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term315 A K k s t i) = (term272 A K k s t i).
Proof. exact (eq_refl (term315 A K k s t i)). Qed.
Lemma lem4465735 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term316 A K k s t) = (term273 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4465734 A K k s t i)). Qed.
Lemma lem4465736 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4465737 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term317 A K k s t) = (term274 A K k s t).
Proof. exact (MK_COMB (@lem4465736 K) (@lem4465735 A K k s t)). Qed.
Lemma lem4465738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4465739 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term318 A K k s t) = (term275 A K k s t).
Proof. exact (MK_COMB (@lem4465738) (@lem4465737 A K k s t)). Qed.
Lemma lem4465740 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term319 A K k s t i) = (term307 A K i k s t).
Proof. exact (eq_refl (term319 A K k s t i)). Qed.
Lemma lem4465741 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term320 A K k s t) = (term308 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4465740 A K i k s t)). Qed.
Lemma lem4465742 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4465743 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term321 A K k s t) = (term309 A K k s t).
Proof. exact (MK_COMB (@lem4465742 K) (@lem4465741 A K k s t)). Qed.
Lemma lem4465744 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term313 A K k s t) = (term310 A K k s t).
Proof. exact (MK_COMB (@lem4465739 A K k s t) (@lem4465743 A K k s t)). Qed.
Lemma lem4465745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4465746 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term322 A K k s t) = (term323 A K k s t).
Proof. exact (MK_COMB (@lem4465745) (@lem4465744 A K k s t)). Qed.
Lemma lem4465747 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term315 A K k s t i) = (term272 A K k s t i).
Proof. exact (eq_refl (term315 A K k s t i)). Qed.
Lemma lem4465748 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4465749 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term324 A K k s t i) = (term325 A K k s t i).
Proof. exact (MK_COMB (@lem4465748) (@lem4465747 A K k s t i)). Qed.
Lemma lem4465750 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term319 A K k s t i) = (term307 A K i k s t).
Proof. exact (eq_refl (term319 A K k s t i)). Qed.
Lemma lem4465751 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term326 A K k s t i) = (term327 A K i k s t).
Proof. exact (MK_COMB (@lem4465749 A K k s t i) (@lem4465750 A K i k s t)). Qed.
Lemma lem4465752 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term328 A K k s t) = (term329 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4465751 A K i k s t)). Qed.
Lemma lem4465753 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4465754 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term314 A K k s t) = (term330 A K k s t).
Proof. exact (MK_COMB (@lem4465753 K) (@lem4465752 A K k s t)). Qed.
Lemma lem4465755 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term313 A K k s t) = (term314 A K k s t)) = ((term310 A K k s t) = (term330 A K k s t)).
Proof. exact (MK_COMB (@lem4465746 A K k s t) (@lem4465754 A K k s t)). Qed.
Lemma lem4465756 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term310 A K k s t) = (term330 A K k s t).
Proof. exact (EQ_MP (@lem4465755 A K k s t) (@lem4465733 A K k s t)). Qed.
Lemma lem4465758 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term311 A P Q) = (term312 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4465759 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term311 A P Q) = (term312 A P Q).
Proof. exact (@lem4465758 A P Q). Qed.
Lemma lem4465760 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term331 A K i k s t) = (term332 A K i k s t).
Proof. exact (@lem4465759 A (term271 A K k s t i) (term306 A K i k s t)). Qed.
Lemma lem4465761 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term333 A K k s t i x) = (term269 A K k s t i x).
Proof. exact (eq_refl (term333 A K k s t i x)). Qed.
Lemma lem4465762 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term334 A K k s t i) = (term271 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4465761 A K k s t i x)). Qed.
Lemma lem4465763 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4465764 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term335 A K k s t i) = (term272 A K k s t i).
Proof. exact (MK_COMB (@lem4465763 A) (@lem4465762 A K k s t i)). Qed.
Lemma lem4465765 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4465766 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term336 A K k s t i) = (term325 A K k s t i).
Proof. exact (MK_COMB (@lem4465765) (@lem4465764 A K k s t i)). Qed.
Lemma lem4465767 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term337 A K i k s t x) = (term304 A K i x k s t).
Proof. exact (eq_refl (term337 A K i k s t x)). Qed.
Lemma lem4465768 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term338 A K i k s t) = (term306 A K i k s t).
Proof. exact (fun_ext (fun x : A => @lem4465767 A K i x k s t)). Qed.
Lemma lem4465769 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4465770 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term339 A K i k s t) = (term307 A K i k s t).
Proof. exact (MK_COMB (@lem4465769 A) (@lem4465768 A K i k s t)). Qed.
Lemma lem4465771 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term331 A K i k s t) = (term327 A K i k s t).
Proof. exact (MK_COMB (@lem4465766 A K k s t i) (@lem4465770 A K i k s t)). Qed.
Lemma lem4465772 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4465773 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term340 A K i k s t) = (term341 A K i k s t).
Proof. exact (MK_COMB (@lem4465772) (@lem4465771 A K i k s t)). Qed.
Lemma lem4465774 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term333 A K k s t i x) = (term269 A K k s t i x).
Proof. exact (eq_refl (term333 A K k s t i x)). Qed.
Lemma lem4465775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4465776 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term342 A K k s t i x) = (term343 A K k s t i x).
Proof. exact (MK_COMB (@lem4465775) (@lem4465774 A K k s t i x)). Qed.
Lemma lem4465777 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term337 A K i k s t x) = (term304 A K i x k s t).
Proof. exact (eq_refl (term337 A K i k s t x)). Qed.
Lemma lem4465778 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term344 A K i k s t x) = (term345 A K i x k s t).
Proof. exact (MK_COMB (@lem4465776 A K k s t i x) (@lem4465777 A K i x k s t)). Qed.
Lemma lem4465779 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term346 A K i k s t) = (term347 A K i k s t).
Proof. exact (fun_ext (fun x : A => @lem4465778 A K i x k s t)). Qed.
Lemma lem4465780 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4465781 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term332 A K i k s t) = (term348 A K i k s t).
Proof. exact (MK_COMB (@lem4465780 A) (@lem4465779 A K i k s t)). Qed.
Lemma lem4465782 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term331 A K i k s t) = (term332 A K i k s t)) = ((term327 A K i k s t) = (term348 A K i k s t)).
Proof. exact (MK_COMB (@lem4465773 A K i k s t) (@lem4465781 A K i k s t)). Qed.
Lemma lem4465783 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term327 A K i k s t) = (term348 A K i k s t).
Proof. exact (EQ_MP (@lem4465782 A K i k s t) (@lem4465760 A K i k s t)). Qed.
Lemma lem4465784 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term329 A K k s t) = (term349 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4465783 A K i k s t)). Qed.
Lemma lem4465785 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4465786 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term330 A K k s t) = (term350 A K k s t).
Proof. exact (MK_COMB (@lem4465785 K) (@lem4465784 A K k s t)). Qed.
Lemma lem4465787 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term310 A K k s t) = (term350 A K k s t).
Proof. exact (TRANS (@lem4465756 A K k s t) (@lem4465786 A K k s t)). Qed.
Lemma lem4465789 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term231 A K k s t) = (term350 A K k s t).
Proof. exact (TRANS (@lem4465729 A K k s t) (@lem4465787 A K k s t)). Qed.
Lemma lem4465790 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term162 A K k s t) = (term350 A K k s t).
Proof. exact (TRANS (@lem4465327 A K k s t) (@lem4465789 A K k s t)). Qed.
Lemma lem4465791 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term162 A K k s t) : term350 A K k s t.
Proof. exact (EQ_MP (@lem4465790 A K k s t) (@lem4465204 A K k s t h1)). Qed.
Lemma lem4465792 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term348 A K i k s t) : term348 A K i k s t.
Proof. exact (h1). Qed.
Lemma lem4465793 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term345 A K i x k s t) : term345 A K i x k s t.
Proof. exact (h1). Qed.
Lemma lem4465808 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term195 A K s t i x) = (term195 A K s t i x).
Proof. exact (eq_refl (term195 A K s t i x)). Qed.
Lemma lem4465809 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term203 A K s t i) = (term203 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4465808 A K s t i x)). Qed.
Lemma lem4465810 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4465811 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term204 A K s t i) = (term204 A K s t i).
Proof. exact (MK_COMB (@lem4465810 A) (@lem4465809 A K s t i)). Qed.
Lemma lem4465818 {K : Type'} (k : K -> Prop) (i : K) : (term208 K k i) = (term208 K k i).
Proof. exact (eq_refl (term208 K k i)). Qed.
Lemma lem4465819 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term210 A K k s t i) = (term210 A K k s t i).
Proof. exact (MK_COMB (@lem4465818 K k i) (@lem4465811 A K s t i)). Qed.
Lemma lem4465820 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term218 A K k s t) = (term218 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4465819 A K k s t i)). Qed.
Lemma lem4465821 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4465822 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term219 A K k s t) = (term219 A K k s t).
Proof. exact (MK_COMB (@lem4465821 K) (@lem4465820 A K k s t)). Qed.
Lemma lem4465853 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term302 A K s k t i x) = (term302 A K s k t i x).
Proof. exact (eq_refl (term302 A K s k t i x)). Qed.
Lemma lem4465854 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term304 A K i x k s t) = (term304 A K i x k s t).
Proof. exact (MK_COMB (@lem4465853 A K s k t i x) (@lem4465822 A K k s t)). Qed.
Lemma lem4465875 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term242 A K k s t i x) = (term242 A K k s t i x).
Proof. exact (eq_refl (term242 A K k s t i x)). Qed.
Lemma lem4465904 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) (x : A) : (term172 A K s k t i x) = (term172 A K s k t i x).
Proof. exact (eq_refl (term172 A K s k t i x)). Qed.
Lemma lem4465905 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term182 A K s k t i) = (term182 A K s k t i).
Proof. exact (fun_ext (fun x : A => @lem4465904 A K s k t i x)). Qed.
Lemma lem4465906 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4465907 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (i : K) : (term183 A K s k t i) = (term183 A K s k t i).
Proof. exact (MK_COMB (@lem4465906 A) (@lem4465905 A K s k t i)). Qed.
Lemma lem4465908 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term191 A K s k t) = (term191 A K s k t).
Proof. exact (fun_ext (fun i : K => @lem4465907 A K s k t i)). Qed.
Lemma lem4465909 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4465910 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term192 A K s k t) = (term192 A K s k t).
Proof. exact (MK_COMB (@lem4465909 K) (@lem4465908 A K s k t)). Qed.
Lemma lem4465911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4465912 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term225 A K s k t) = (term225 A K s k t).
Proof. exact (MK_COMB (@lem4465911) (@lem4465910 A K s k t)). Qed.
Lemma lem4465913 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term269 A K k s t i x) = (term269 A K k s t i x).
Proof. exact (MK_COMB (@lem4465912 A K s k t) (@lem4465875 A K k s t i x)). Qed.
Lemma lem4465914 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4465915 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term343 A K k s t i x) = (term343 A K k s t i x).
Proof. exact (MK_COMB (@lem4465914) (@lem4465913 A K k s t i x)). Qed.
Lemma lem4465916 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term345 A K i x k s t) = (term345 A K i x k s t).
Proof. exact (MK_COMB (@lem4465915 A K k s t i x) (@lem4465854 A K i x k s t)). Qed.
Lemma lem4465917 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term345 A K i x k s t) : term345 A K i x k s t.
Proof. exact (EQ_MP (@lem4465916 A K i x k s t) (@lem4465793 A K i x k s t h1)). Qed.
Lemma lem4465918 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term269 A K k s t i x.
Proof. exact (h1). Qed.
Lemma lem4465919 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term304 A K i x k s t.
Proof. exact (h1). Qed.
Lemma lem4465920 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term242 A K k s t i x.
Proof. exact (proj2 (@lem4465918 A K k s t i x h1)). Qed.
Lemma lem4465921 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term192 A K s k t.
Proof. exact (proj1 (@lem4465918 A K k s t i x h1)). Qed.
Lemma lem4465922 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term194 A K s t i x.
Proof. exact (proj2 (@lem4465920 A K k s t i x h1)). Qed.
Lemma lem4465926 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term219 A K k s t.
Proof. exact (proj2 (@lem4465919 A K i x k s t h1)). Qed.
Lemma lem4465927 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term167 A K s k t i x.
Proof. exact (proj1 (@lem4465919 A K i x k s t h1)). Qed.
Lemma lem4465928 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term164 A K k t i x.
Proof. exact (proj2 (@lem4465927 A K i x k s t h1)). Qed.
Lemma lem4465929 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term128 A K k s i x.
Proof. exact (proj1 (@lem4465927 A K i x k s t h1)). Qed.
Lemma lem4465957 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term172 A K s k t i x) = (term351 A K k s t i x).
Proof. exact (@lem19490 (k i) (term164 A K k s i x) (t i x)). Qed.
Lemma lem4465958 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term182 A K s k t i) = (term352 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4465957 A K k s t i x)). Qed.
Lemma lem4465959 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4465960 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term183 A K s k t i) = (term353 A K k s t i).
Proof. exact (MK_COMB (@lem4465959 A) (@lem4465958 A K k s t i)). Qed.
Lemma lem4465961 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term191 A K s k t) = (term354 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4465960 A K k s t i)). Qed.
Lemma lem4465962 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4465964 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term192 A K s k t) = (term355 A K k s t).
Proof. exact (MK_COMB (@lem4465962 K) (@lem4465961 A K k s t)). Qed.
Lemma lem4465965 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term355 A K k s t.
Proof. exact (EQ_MP (@lem4465964 A K k s t) (@lem4465921 A K k s t i x h1)). Qed.
Lemma lem4466033 {K : Type'} (k : K -> Prop) (i : K) (h1 : term356 K k i) : term356 K k i.
Proof. exact (h1). Qed.
Lemma lem4466035 {A : Type'} (P : Prop) (Q : A -> Prop) : (term357 A P Q) = (term358 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4466036 {A : Type'} (P : Prop) (Q : A -> Prop) : (term357 A P Q) = (term358 A P Q).
Proof. exact (@lem4466035 A P Q). Qed.
Lemma lem4466037 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term359 A K k s t i) = (term360 A K k s t i).
Proof. exact (@lem4466036 A (term356 K k i) (term203 A K s t i)). Qed.
Lemma lem4466038 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term361 A K s t i x) = (term195 A K s t i x).
Proof. exact (eq_refl (term361 A K s t i x)). Qed.
Lemma lem4466039 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term362 A K s t i) = (term203 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4466038 A K s t i x)). Qed.
Lemma lem4466040 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4466041 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term363 A K s t i) = (term204 A K s t i).
Proof. exact (MK_COMB (@lem4466040 A) (@lem4466039 A K s t i)). Qed.
Lemma lem4466042 {K : Type'} (k : K -> Prop) (i : K) : (term208 K k i) = (term208 K k i).
Proof. exact (eq_refl (term208 K k i)). Qed.
Lemma lem4466043 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term359 A K k s t i) = (term210 A K k s t i).
Proof. exact (MK_COMB (@lem4466042 K k i) (@lem4466041 A K s t i)). Qed.
Lemma lem4466044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4466045 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term364 A K k s t i) = (term365 A K k s t i).
Proof. exact (MK_COMB (@lem4466044) (@lem4466043 A K k s t i)). Qed.
Lemma lem4466046 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term361 A K s t i x) = (term195 A K s t i x).
Proof. exact (eq_refl (term361 A K s t i x)). Qed.
Lemma lem4466047 {K : Type'} (k : K -> Prop) (i : K) : (term208 K k i) = (term208 K k i).
Proof. exact (eq_refl (term208 K k i)). Qed.
Lemma lem4466048 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term366 A K k s t i x) = (term367 A K k s t i x).
Proof. exact (MK_COMB (@lem4466047 K k i) (@lem4466046 A K s t i x)). Qed.
Lemma lem4466049 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term368 A K k s t i) = (term369 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4466048 A K k s t i x)). Qed.
Lemma lem4466050 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4466051 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term360 A K k s t i) = (term370 A K k s t i).
Proof. exact (MK_COMB (@lem4466050 A) (@lem4466049 A K k s t i)). Qed.
Lemma lem4466052 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : ((term359 A K k s t i) = (term360 A K k s t i)) = ((term210 A K k s t i) = (term370 A K k s t i)).
Proof. exact (MK_COMB (@lem4466045 A K k s t i) (@lem4466051 A K k s t i)). Qed.
Lemma lem4466053 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term210 A K k s t i) = (term370 A K k s t i).
Proof. exact (EQ_MP (@lem4466052 A K k s t i) (@lem4466037 A K k s t i)). Qed.
Lemma lem4466054 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term218 A K k s t) = (term371 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4466053 A K k s t i)). Qed.
Lemma lem4466055 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4466056 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term219 A K k s t) = (term372 A K k s t).
Proof. exact (MK_COMB (@lem4466055 K) (@lem4466054 A K k s t)). Qed.
Lemma lem4466069 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term367 A K k s t i x) = (term367 A K k s t i x).
Proof. exact (eq_refl (term367 A K k s t i x)). Qed.
Lemma lem4466070 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term369 A K k s t i) = (term369 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4466069 A K k s t i x)). Qed.
Lemma lem4466071 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4466072 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term370 A K k s t i) = (term370 A K k s t i).
Proof. exact (MK_COMB (@lem4466071 A) (@lem4466070 A K k s t i)). Qed.
Lemma lem4466073 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term371 A K k s t) = (term371 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4466072 A K k s t i)). Qed.
Lemma lem4466074 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4466075 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term372 A K k s t) = (term372 A K k s t).
Proof. exact (MK_COMB (@lem4466074 K) (@lem4466073 A K k s t)). Qed.
Lemma lem4466076 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term219 A K k s t) = (term372 A K k s t).
Proof. exact (TRANS (@lem4466056 A K k s t) (@lem4466075 A K k s t)). Qed.
Lemma lem4466077 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term372 A K k s t.
Proof. exact (EQ_MP (@lem4466076 A K k s t) (@lem4465926 A K i x k s t h1)). Qed.
Lemma lem4466089 {A K : Type'} (t : type1470 A K) (i : K) (x : A) (h1 : term373 A K t i x) : term373 A K t i x.
Proof. exact (h1). Qed.
Lemma lem4466090 {A K : Type'} (_51674 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term374 A K k s t _51674.
Proof. exact (@lem4465965 A K k s t i x h1 _51674). Qed.
Lemma lem4466091 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51674 : K) : (term374 A K k s t _51674) = (term353 A K k s t _51674).
Proof. exact (eq_refl (term374 A K k s t _51674)). Qed.
Lemma lem4466092 {A K : Type'} (_51674 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term353 A K k s t _51674.
Proof. exact (EQ_MP (@lem4466091 A K k s t _51674) (@lem4466090 A K _51674 k s t i x h1)). Qed.
Lemma lem4466093 {A K : Type'} (_51674 : K) (_51675 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term375 A K k s t _51674 _51675.
Proof. exact (@lem4466092 A K _51674 k s t i x h1 _51675). Qed.
Lemma lem4466094 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51674 : K) (_51675 : A) : (term375 A K k s t _51674 _51675) = (term351 A K k s t _51674 _51675).
Proof. exact (eq_refl (term375 A K k s t _51674 _51675)). Qed.
Lemma lem4466095 {A K : Type'} (_51674 : K) (_51675 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term351 A K k s t _51674 _51675.
Proof. exact (EQ_MP (@lem4466094 A K k s t _51674 _51675) (@lem4466093 A K _51674 _51675 k s t i x h1)). Qed.
Lemma lem4466102 {A K : Type'} (_51678 : K) (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term376 A K k s t _51678.
Proof. exact (@lem4466077 A K i x k s t h1 _51678). Qed.
Lemma lem4466103 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51678 : K) : (term376 A K k s t _51678) = (term370 A K k s t _51678).
Proof. exact (eq_refl (term376 A K k s t _51678)). Qed.
Lemma lem4466104 {A K : Type'} (_51678 : K) (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term370 A K k s t _51678.
Proof. exact (EQ_MP (@lem4466103 A K k s t _51678) (@lem4466102 A K _51678 i x k s t h1)). Qed.
Lemma lem4466105 {A K : Type'} (_51678 : K) (_51679 : A) (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term377 A K k s t _51678 _51679.
Proof. exact (@lem4466104 A K _51678 i x k s t h1 _51679). Qed.
Lemma lem4466106 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51678 : K) (_51679 : A) : (term377 A K k s t _51678 _51679) = (term367 A K k s t _51678 _51679).
Proof. exact (eq_refl (term377 A K k s t _51678 _51679)). Qed.
Lemma lem4466108 {A K : Type'} (_51674 : K) (_51675 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term378 A K k s t _51674 _51675.
Proof. exact (proj2 (@lem4466095 A K _51674 _51675 k s t i x h1)). Qed.
Lemma lem4466115 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term373 A K t i x.
Proof. exact (proj2 (@lem4465922 A K k s t i x h1)). Qed.
Lemma lem4466138 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51674 : K) (_51675 : A) : (term378 A K k s t _51674 _51675) = (term367 A K k s t _51674 _51675).
Proof. exact (@lem4464474 (term356 K k _51674) (term373 A K s _51674 _51675) (t _51674 _51675)). Qed.
Lemma lem4466139 {A K : Type'} (_51674 : K) (_51675 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term367 A K k s t _51674 _51675.
Proof. exact (EQ_MP (@lem4466138 A K k s t _51674 _51675) (@lem4466108 A K _51674 _51675 k s t i x h1)). Qed.
Lemma lem4466155 {K : Type'} (k : K -> Prop) (i : K) (h1 : term356 K k i) : term356 K k i.
Proof. exact (h1). Qed.
Lemma lem4466165 {A K : Type'} (_51678 : K) (_51679 : A) (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term367 A K k s t _51678 _51679.
Proof. exact (EQ_MP (@lem4466106 A K k s t _51678 _51679) (@lem4466105 A K _51678 _51679 i x k s t h1)). Qed.
Lemma lem4466171 {A K : Type'} (t : type1470 A K) (i : K) (x : A) (h1 : term373 A K t i x) : term373 A K t i x.
Proof. exact (h1). Qed.
Lemma lem4466173 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : k i.
Proof. exact (proj1 (@lem4465920 A K k s t i x h1)). Qed.
Lemma lem4466174 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term379 K k i.
Proof. exact (fun h0 : term356 K k i => @lem4466173 A K k s t i x h1). Qed.
Lemma lem4466176 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4466177 {K : Type'} (k : K -> Prop) (i : K) : (term379 K k i) = (k i).
Proof. exact (@lem4466176 (k i)). Qed.
Lemma lem4466178 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : k i.
Proof. exact (EQ_MP (@lem4466177 K k i) (@lem4466174 A K k s t i x h1)). Qed.
Lemma lem4466180 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : s i x.
Proof. exact (proj1 (@lem4465922 A K k s t i x h1)). Qed.
Lemma lem4466181 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term381 A K s i x.
Proof. exact (fun h0 : term373 A K s i x => @lem4466180 A K k s t i x h1). Qed.
Lemma lem4466183 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4466184 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term381 A K s i x) = (s i x).
Proof. exact (@lem4466183 (s i x)). Qed.
Lemma lem4466185 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : s i x.
Proof. exact (EQ_MP (@lem4466184 A K s i x) (@lem4466181 A K k s t i x h1)). Qed.
Lemma lem4466201 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4466202 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_51674 : K) (_51675 : A) : (term195 A K s t _51674 _51675) = (term382 A K t s _51674 _51675).
Proof. exact (@lem4466201 (t _51674 _51675) (term373 A K s _51674 _51675)). Qed.
Lemma lem4466208 {K : Type'} (k : K -> Prop) (_51674 : K) : (term208 K k _51674) = (term208 K k _51674).
Proof. exact (eq_refl (term208 K k _51674)). Qed.
Lemma lem4466209 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51674 : K) (_51675 : A) : (term367 A K k s t _51674 _51675) = (term383 A K k t s _51674 _51675).
Proof. exact (MK_COMB (@lem4466208 K k _51674) (@lem4466202 A K t s _51674 _51675)). Qed.
Lemma lem4466213 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4466214 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51674 : K) (_51675 : A) : (term383 A K k t s _51674 _51675) = (term384 A K t k s _51674 _51675).
Proof. exact (@lem4466213 (t _51674 _51675) (term356 K k _51674) (term373 A K s _51674 _51675)). Qed.
Lemma lem4466230 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51674 : K) (_51675 : A) : (term367 A K k s t _51674 _51675) = (term384 A K t k s _51674 _51675).
Proof. exact (TRANS (@lem4466209 A K k t s _51674 _51675) (@lem4466214 A K t k s _51674 _51675)). Qed.
Lemma lem4466231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4466232 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51674 : K) (_51675 : A) : (term385 A K k s t _51674 _51675) = (term386 A K t k s _51674 _51675).
Proof. exact (MK_COMB (@lem4466231) (@lem4466230 A K t k s _51674 _51675)). Qed.
Lemma lem4466248 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51674 : K) (_51675 : A) : (term384 A K t k s _51674 _51675) = (term384 A K t k s _51674 _51675).
Proof. exact (eq_refl (term384 A K t k s _51674 _51675)). Qed.
Lemma lem4466249 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51674 : K) (_51675 : A) : ((term367 A K k s t _51674 _51675) = (term384 A K t k s _51674 _51675)) = ((term384 A K t k s _51674 _51675) = (term384 A K t k s _51674 _51675)).
Proof. exact (MK_COMB (@lem4466232 A K t k s _51674 _51675) (@lem4466248 A K t k s _51674 _51675)). Qed.
Lemma lem4466251 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4466252 (x : Prop) : (x = x) = True.
Proof. exact (@lem4466251 Prop x). Qed.
Lemma lem4466253 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51674 : K) (_51675 : A) : ((term384 A K t k s _51674 _51675) = (term384 A K t k s _51674 _51675)) = True.
Proof. exact (@lem4466252 (term384 A K t k s _51674 _51675)). Qed.
Lemma lem4466254 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51674 : K) (_51675 : A) : ((term367 A K k s t _51674 _51675) = (term384 A K t k s _51674 _51675)) = True.
Proof. exact (TRANS (@lem4466249 A K t k s _51674 _51675) (@lem4466253 A K t k s _51674 _51675)). Qed.
Lemma lem4466255 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51674 : K) (_51675 : A) : True = ((term367 A K k s t _51674 _51675) = (term384 A K t k s _51674 _51675)).
Proof. exact (SYM (@lem4466254 A K t k s _51674 _51675)). Qed.
Lemma lem4466256 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51674 : K) (_51675 : A) : (term367 A K k s t _51674 _51675) = (term384 A K t k s _51674 _51675).
Proof. exact (EQ_MP (@lem4466255 A K t k s _51674 _51675) (@lem0)). Qed.
Lemma lem4466257 {A K : Type'} (_51674 : K) (_51675 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term384 A K t k s _51674 _51675.
Proof. exact (EQ_MP (@lem4466256 A K t k s _51674 _51675) (@lem4466139 A K _51674 _51675 k s t i x h1)). Qed.
Lemma lem4466259 (b : Prop) (a : Prop) : (a \/ b) = (term387 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4466260 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51674 : K) (_51675 : A) : (term384 A K t k s _51674 _51675) = (term388 A K k s t _51674 _51675).
Proof. exact (@lem4466259 (term164 A K k s _51674 _51675) (t _51674 _51675)). Qed.
Lemma lem4466262 (a : Prop) (b : Prop) : (term389 a b) = (term390 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4466263 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51674 : K) (_51675 : A) : (term391 A K k s _51674 _51675) = (term392 A K k s _51674 _51675).
Proof. exact (@lem4466262 (term356 K k _51674) (term373 A K s _51674 _51675)). Qed.
Lemma lem4466265 (a : Prop) : (term160 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4466266 {K : Type'} (k : K -> Prop) (_51674 : K) : (term393 K k _51674) = (k _51674).
Proof. exact (@lem4466265 (k _51674)). Qed.
Lemma lem4466267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4466268 {K : Type'} (k : K -> Prop) (_51674 : K) : (term394 K k _51674) = (term126 K k _51674).
Proof. exact (MK_COMB (@lem4466267) (@lem4466266 K k _51674)). Qed.
Lemma lem4466270 (a : Prop) : (term160 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4466271 {A K : Type'} (s : type1470 A K) (_51674 : K) (_51675 : A) : (term395 A K s _51674 _51675) = (s _51674 _51675).
Proof. exact (@lem4466270 (s _51674 _51675)). Qed.
Lemma lem4466272 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51674 : K) (_51675 : A) : (term392 A K k s _51674 _51675) = (term128 A K k s _51674 _51675).
Proof. exact (MK_COMB (@lem4466268 K k _51674) (@lem4466271 A K s _51674 _51675)). Qed.
Lemma lem4466273 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51674 : K) (_51675 : A) : (term391 A K k s _51674 _51675) = (term128 A K k s _51674 _51675).
Proof. exact (TRANS (@lem4466263 A K k s _51674 _51675) (@lem4466272 A K k s _51674 _51675)). Qed.
Lemma lem4466274 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4466275 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51674 : K) (_51675 : A) : (term396 A K k s _51674 _51675) = (term129 A K k s _51674 _51675).
Proof. exact (MK_COMB (@lem4466274) (@lem4466273 A K k s _51674 _51675)). Qed.
Lemma lem4466276 {A K : Type'} (t : type1470 A K) (_51674 : K) (_51675 : A) : (t _51674 _51675) = (t _51674 _51675).
Proof. exact (eq_refl (t _51674 _51675)). Qed.
Lemma lem4466277 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51674 : K) (_51675 : A) : (term388 A K k s t _51674 _51675) = (term397 A K k s t _51674 _51675).
Proof. exact (MK_COMB (@lem4466275 A K k s _51674 _51675) (@lem4466276 A K t _51674 _51675)). Qed.
Lemma lem4466278 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51674 : K) (_51675 : A) : (term384 A K t k s _51674 _51675) = (term397 A K k s t _51674 _51675).
Proof. exact (TRANS (@lem4466260 A K k s t _51674 _51675) (@lem4466277 A K k s t _51674 _51675)). Qed.
Lemma lem4466280 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term128 A K k s i x.
Proof. exact (conj (@lem4466178 A K k s t i x h1) (@lem4466185 A K k s t i x h1)). Qed.
Lemma lem4466282 {A K : Type'} (_51674 : K) (_51675 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term397 A K k s t _51674 _51675.
Proof. exact (EQ_MP (@lem4466278 A K k s t _51674 _51675) (@lem4466257 A K _51674 _51675 k s t i x h1)). Qed.
Lemma lem4466283 {A K : Type'} (_51674 : K) (_51675 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term397 A K k s t _51674 _51675.
Proof. exact (@lem4466282 A K _51674 _51675 k s t i x h1). Qed.
Lemma lem4466284 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term397 A K k s t i x.
Proof. exact (@lem4466283 A K i x k s t i x h1). Qed.
Lemma lem4466287 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : t i x.
Proof. exact (@lem4466284 A K k s t i x h1 (@lem4466280 A K k s t i x h1)). Qed.
Lemma lem4466288 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term381 A K t i x.
Proof. exact (fun h0 : term373 A K t i x => @lem4466287 A K k s t i x h1). Qed.
Lemma lem4466290 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4466291 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term381 A K t i x) = (t i x).
Proof. exact (@lem4466290 (t i x)). Qed.
Lemma lem4466292 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : t i x.
Proof. exact (EQ_MP (@lem4466291 A K t i x) (@lem4466288 A K k s t i x h1)). Qed.
Lemma lem4466295 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4466297 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term373 A K t i x) = (term398 A K t i x).
Proof. exact (@lem4466295 (t i x)). Qed.
Lemma lem4466300 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term398 A K t i x.
Proof. exact (EQ_MP (@lem4466297 A K t i x) (@lem4466115 A K k s t i x h1)). Qed.
Lemma lem4466303 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : False.
Proof. exact (@lem4466300 A K k s t i x h1 (@lem4466292 A K k s t i x h1)). Qed.
Lemma lem4466304 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : term399.
Proof. exact (fun h0 : ~ False => @lem4466303 A K k s t i x h1). Qed.
Lemma lem4466306 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4466307 : term399 = False.
Proof. exact (@lem4466306 False). Qed.
Lemma lem4466308 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term269 A K k s t i x) : False.
Proof. exact (EQ_MP (@lem4466307) (@lem4466304 A K k s t i x h1)). Qed.
Lemma lem4466310 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : k i.
Proof. exact (proj1 (@lem4465929 A K i x k s t h1)). Qed.
Lemma lem4466311 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term379 K k i.
Proof. exact (fun h0 : term356 K k i => @lem4466310 A K i x k s t h1). Qed.
Lemma lem4466313 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4466314 {K : Type'} (k : K -> Prop) (i : K) : (term379 K k i) = (k i).
Proof. exact (@lem4466313 (k i)). Qed.
Lemma lem4466315 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : k i.
Proof. exact (EQ_MP (@lem4466314 K k i) (@lem4466311 A K i x k s t h1)). Qed.
Lemma lem4466318 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4466320 {K : Type'} (k : K -> Prop) (i : K) : (term356 K k i) = (term400 K k i).
Proof. exact (@lem4466318 (k i)). Qed.
Lemma lem4466323 {K : Type'} (k : K -> Prop) (i : K) (h1 : term356 K k i) : term400 K k i.
Proof. exact (EQ_MP (@lem4466320 K k i) (@lem4466155 K k i h1)). Qed.
Lemma lem4466326 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term356 K k i) (h2 : term304 A K i x k s t) : False.
Proof. exact (@lem4466323 K k i h1 (@lem4466315 A K i x k s t h2)). Qed.
Lemma lem4466327 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term356 K k i) (h2 : term304 A K i x k s t) : term399.
Proof. exact (fun h0 : ~ False => @lem4466326 A K i x k s t h1 h2). Qed.
Lemma lem4466329 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4466330 : term399 = False.
Proof. exact (@lem4466329 False). Qed.
Lemma lem4466331 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term356 K k i) (h2 : term304 A K i x k s t) : False.
Proof. exact (EQ_MP (@lem4466330) (@lem4466327 A K i x k s t h1 h2)). Qed.
Lemma lem4466333 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : k i.
Proof. exact (proj1 (@lem4465929 A K i x k s t h1)). Qed.
Lemma lem4466334 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term379 K k i.
Proof. exact (fun h0 : term356 K k i => @lem4466333 A K i x k s t h1). Qed.
Lemma lem4466336 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4466337 {K : Type'} (k : K -> Prop) (i : K) : (term379 K k i) = (k i).
Proof. exact (@lem4466336 (k i)). Qed.
Lemma lem4466338 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : k i.
Proof. exact (EQ_MP (@lem4466337 K k i) (@lem4466334 A K i x k s t h1)). Qed.
Lemma lem4466340 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : s i x.
Proof. exact (proj2 (@lem4465929 A K i x k s t h1)). Qed.
Lemma lem4466341 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term381 A K s i x.
Proof. exact (fun h0 : term373 A K s i x => @lem4466340 A K i x k s t h1). Qed.
Lemma lem4466343 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4466344 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term381 A K s i x) = (s i x).
Proof. exact (@lem4466343 (s i x)). Qed.
Lemma lem4466345 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : s i x.
Proof. exact (EQ_MP (@lem4466344 A K s i x) (@lem4466341 A K i x k s t h1)). Qed.
Lemma lem4466361 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4466362 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_51678 : K) (_51679 : A) : (term195 A K s t _51678 _51679) = (term382 A K t s _51678 _51679).
Proof. exact (@lem4466361 (t _51678 _51679) (term373 A K s _51678 _51679)). Qed.
Lemma lem4466368 {K : Type'} (k : K -> Prop) (_51678 : K) : (term208 K k _51678) = (term208 K k _51678).
Proof. exact (eq_refl (term208 K k _51678)). Qed.
Lemma lem4466369 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51678 : K) (_51679 : A) : (term367 A K k s t _51678 _51679) = (term383 A K k t s _51678 _51679).
Proof. exact (MK_COMB (@lem4466368 K k _51678) (@lem4466362 A K t s _51678 _51679)). Qed.
Lemma lem4466373 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4466374 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51678 : K) (_51679 : A) : (term383 A K k t s _51678 _51679) = (term384 A K t k s _51678 _51679).
Proof. exact (@lem4466373 (t _51678 _51679) (term356 K k _51678) (term373 A K s _51678 _51679)). Qed.
Lemma lem4466390 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51678 : K) (_51679 : A) : (term367 A K k s t _51678 _51679) = (term384 A K t k s _51678 _51679).
Proof. exact (TRANS (@lem4466369 A K k t s _51678 _51679) (@lem4466374 A K t k s _51678 _51679)). Qed.
Lemma lem4466391 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4466392 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51678 : K) (_51679 : A) : (term385 A K k s t _51678 _51679) = (term386 A K t k s _51678 _51679).
Proof. exact (MK_COMB (@lem4466391) (@lem4466390 A K t k s _51678 _51679)). Qed.
Lemma lem4466408 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51678 : K) (_51679 : A) : (term384 A K t k s _51678 _51679) = (term384 A K t k s _51678 _51679).
Proof. exact (eq_refl (term384 A K t k s _51678 _51679)). Qed.
Lemma lem4466409 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51678 : K) (_51679 : A) : ((term367 A K k s t _51678 _51679) = (term384 A K t k s _51678 _51679)) = ((term384 A K t k s _51678 _51679) = (term384 A K t k s _51678 _51679)).
Proof. exact (MK_COMB (@lem4466392 A K t k s _51678 _51679) (@lem4466408 A K t k s _51678 _51679)). Qed.
Lemma lem4466411 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4466412 (x : Prop) : (x = x) = True.
Proof. exact (@lem4466411 Prop x). Qed.
Lemma lem4466413 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51678 : K) (_51679 : A) : ((term384 A K t k s _51678 _51679) = (term384 A K t k s _51678 _51679)) = True.
Proof. exact (@lem4466412 (term384 A K t k s _51678 _51679)). Qed.
Lemma lem4466414 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51678 : K) (_51679 : A) : ((term367 A K k s t _51678 _51679) = (term384 A K t k s _51678 _51679)) = True.
Proof. exact (TRANS (@lem4466409 A K t k s _51678 _51679) (@lem4466413 A K t k s _51678 _51679)). Qed.
Lemma lem4466415 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51678 : K) (_51679 : A) : True = ((term367 A K k s t _51678 _51679) = (term384 A K t k s _51678 _51679)).
Proof. exact (SYM (@lem4466414 A K t k s _51678 _51679)). Qed.
Lemma lem4466416 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51678 : K) (_51679 : A) : (term367 A K k s t _51678 _51679) = (term384 A K t k s _51678 _51679).
Proof. exact (EQ_MP (@lem4466415 A K t k s _51678 _51679) (@lem0)). Qed.
Lemma lem4466417 {A K : Type'} (_51678 : K) (_51679 : A) (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term384 A K t k s _51678 _51679.
Proof. exact (EQ_MP (@lem4466416 A K t k s _51678 _51679) (@lem4466165 A K _51678 _51679 i x k s t h1)). Qed.
Lemma lem4466419 (b : Prop) (a : Prop) : (a \/ b) = (term387 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4466420 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51678 : K) (_51679 : A) : (term384 A K t k s _51678 _51679) = (term388 A K k s t _51678 _51679).
Proof. exact (@lem4466419 (term164 A K k s _51678 _51679) (t _51678 _51679)). Qed.
Lemma lem4466422 (a : Prop) (b : Prop) : (term389 a b) = (term390 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4466423 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51678 : K) (_51679 : A) : (term391 A K k s _51678 _51679) = (term392 A K k s _51678 _51679).
Proof. exact (@lem4466422 (term356 K k _51678) (term373 A K s _51678 _51679)). Qed.
Lemma lem4466425 (a : Prop) : (term160 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4466426 {K : Type'} (k : K -> Prop) (_51678 : K) : (term393 K k _51678) = (k _51678).
Proof. exact (@lem4466425 (k _51678)). Qed.
Lemma lem4466427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4466428 {K : Type'} (k : K -> Prop) (_51678 : K) : (term394 K k _51678) = (term126 K k _51678).
Proof. exact (MK_COMB (@lem4466427) (@lem4466426 K k _51678)). Qed.
Lemma lem4466430 (a : Prop) : (term160 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4466431 {A K : Type'} (s : type1470 A K) (_51678 : K) (_51679 : A) : (term395 A K s _51678 _51679) = (s _51678 _51679).
Proof. exact (@lem4466430 (s _51678 _51679)). Qed.
Lemma lem4466432 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51678 : K) (_51679 : A) : (term392 A K k s _51678 _51679) = (term128 A K k s _51678 _51679).
Proof. exact (MK_COMB (@lem4466428 K k _51678) (@lem4466431 A K s _51678 _51679)). Qed.
Lemma lem4466433 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51678 : K) (_51679 : A) : (term391 A K k s _51678 _51679) = (term128 A K k s _51678 _51679).
Proof. exact (TRANS (@lem4466423 A K k s _51678 _51679) (@lem4466432 A K k s _51678 _51679)). Qed.
Lemma lem4466434 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4466435 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51678 : K) (_51679 : A) : (term396 A K k s _51678 _51679) = (term129 A K k s _51678 _51679).
Proof. exact (MK_COMB (@lem4466434) (@lem4466433 A K k s _51678 _51679)). Qed.
Lemma lem4466436 {A K : Type'} (t : type1470 A K) (_51678 : K) (_51679 : A) : (t _51678 _51679) = (t _51678 _51679).
Proof. exact (eq_refl (t _51678 _51679)). Qed.
Lemma lem4466437 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51678 : K) (_51679 : A) : (term388 A K k s t _51678 _51679) = (term397 A K k s t _51678 _51679).
Proof. exact (MK_COMB (@lem4466435 A K k s _51678 _51679) (@lem4466436 A K t _51678 _51679)). Qed.
Lemma lem4466438 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51678 : K) (_51679 : A) : (term384 A K t k s _51678 _51679) = (term397 A K k s t _51678 _51679).
Proof. exact (TRANS (@lem4466420 A K k s t _51678 _51679) (@lem4466437 A K k s t _51678 _51679)). Qed.
Lemma lem4466440 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term128 A K k s i x.
Proof. exact (conj (@lem4466338 A K i x k s t h1) (@lem4466345 A K i x k s t h1)). Qed.
Lemma lem4466442 {A K : Type'} (_51678 : K) (_51679 : A) (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term397 A K k s t _51678 _51679.
Proof. exact (EQ_MP (@lem4466438 A K k s t _51678 _51679) (@lem4466417 A K _51678 _51679 i x k s t h1)). Qed.
Lemma lem4466443 {A K : Type'} (_51678 : K) (_51679 : A) (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term397 A K k s t _51678 _51679.
Proof. exact (@lem4466442 A K _51678 _51679 i x k s t h1). Qed.
Lemma lem4466444 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term397 A K k s t i x.
Proof. exact (@lem4466443 A K i x i x k s t h1). Qed.
Lemma lem4466447 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : t i x.
Proof. exact (@lem4466444 A K i x k s t h1 (@lem4466440 A K i x k s t h1)). Qed.
Lemma lem4466448 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : term381 A K t i x.
Proof. exact (fun h0 : term373 A K t i x => @lem4466447 A K i x k s t h1). Qed.
Lemma lem4466450 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4466451 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term381 A K t i x) = (t i x).
Proof. exact (@lem4466450 (t i x)). Qed.
Lemma lem4466452 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : t i x.
Proof. exact (EQ_MP (@lem4466451 A K t i x) (@lem4466448 A K i x k s t h1)). Qed.
Lemma lem4466455 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4466457 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term373 A K t i x) = (term398 A K t i x).
Proof. exact (@lem4466455 (t i x)). Qed.
Lemma lem4466460 {A K : Type'} (t : type1470 A K) (i : K) (x : A) (h1 : term373 A K t i x) : term398 A K t i x.
Proof. exact (EQ_MP (@lem4466457 A K t i x) (@lem4466171 A K t i x h1)). Qed.
Lemma lem4466463 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term373 A K t i x) (h2 : term304 A K i x k s t) : False.
Proof. exact (@lem4466460 A K t i x h1 (@lem4466452 A K i x k s t h2)). Qed.
Lemma lem4466464 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term373 A K t i x) (h2 : term304 A K i x k s t) : term399.
Proof. exact (fun h0 : ~ False => @lem4466463 A K i x k s t h1 h2). Qed.
Lemma lem4466466 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4466467 : term399 = False.
Proof. exact (@lem4466466 False). Qed.
Lemma lem4466468 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term373 A K t i x) (h2 : term304 A K i x k s t) : False.
Proof. exact (EQ_MP (@lem4466467) (@lem4466464 A K i x k s t h1 h2)). Qed.
Lemma lem4466469 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term373 A K t i x) (h2 : term304 A K i x k s t) : (term373 A K t i x) = False.
Proof. exact (prop_ext (fun h3 : term373 A K t i x => @lem4466468 A K i x k s t h1 h2) (fun h3 : False => @lem4466171 A K t i x h1)). Qed.
Lemma lem4466470 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term373 A K t i x) (h2 : term304 A K i x k s t) : False.
Proof. exact (EQ_MP (@lem4466469 A K i x k s t h1 h2) (@lem4466171 A K t i x h1)). Qed.
Lemma lem4466471 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term356 K k i) (h2 : term304 A K i x k s t) : (term356 K k i) = False.
Proof. exact (prop_ext (fun h3 : term356 K k i => @lem4466331 A K i x k s t h1 h2) (fun h3 : False => @lem4466155 K k i h1)). Qed.
Lemma lem4466472 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term356 K k i) (h2 : term304 A K i x k s t) : False.
Proof. exact (EQ_MP (@lem4466471 A K i x k s t h1 h2) (@lem4466155 K k i h1)). Qed.
Lemma lem4466473 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term373 A K t i x) (h2 : term304 A K i x k s t) : (term373 A K t i x) = False.
Proof. exact (prop_ext (fun h3 : term373 A K t i x => @lem4466470 A K i x k s t h1 h2) (fun h3 : False => @lem4466089 A K t i x h1)). Qed.
Lemma lem4466474 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term373 A K t i x) (h2 : term304 A K i x k s t) : False.
Proof. exact (EQ_MP (@lem4466473 A K i x k s t h1 h2) (@lem4466089 A K t i x h1)). Qed.
Lemma lem4466475 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term356 K k i) (h2 : term304 A K i x k s t) : (term356 K k i) = False.
Proof. exact (prop_ext (fun h3 : term356 K k i => @lem4466472 A K i x k s t h1 h2) (fun h3 : False => @lem4466033 K k i h1)). Qed.
Lemma lem4466476 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term356 K k i) (h2 : term304 A K i x k s t) : False.
Proof. exact (EQ_MP (@lem4466475 A K i x k s t h1 h2) (@lem4466033 K k i h1)). Qed.
Lemma lem4466477 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term373 A K t i x) (h2 : term304 A K i x k s t) : (term373 A K t i x) = False.
Proof. exact (prop_ext (fun h3 : term373 A K t i x => @lem4466474 A K i x k s t h1 h2) (fun h3 : False => @lem4466089 A K t i x h1)). Qed.
Lemma lem4466478 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term373 A K t i x) (h2 : term304 A K i x k s t) : False.
Proof. exact (EQ_MP (@lem4466477 A K i x k s t h1 h2) (@lem4466089 A K t i x h1)). Qed.
Lemma lem4466479 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term356 K k i) (h2 : term304 A K i x k s t) : (term356 K k i) = False.
Proof. exact (prop_ext (fun h3 : term356 K k i => @lem4466476 A K i x k s t h1 h2) (fun h3 : False => @lem4466033 K k i h1)). Qed.
Lemma lem4466480 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term356 K k i) (h2 : term304 A K i x k s t) : False.
Proof. exact (EQ_MP (@lem4466479 A K i x k s t h1 h2) (@lem4466033 K k i h1)). Qed.
Lemma lem4466481 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term304 A K i x k s t) : False.
Proof. exact (or_elim (@lem4465928 A K i x k s t h1) (fun h0 : term356 K k i => @lem4466480 A K i x k s t h0 h1) (fun h0 : term373 A K t i x => @lem4466478 A K i x k s t h0 h1)). Qed.
Lemma lem4466482 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term345 A K i x k s t) : False.
Proof. exact (or_elim (@lem4465917 A K i x k s t h1) (fun h0 : term269 A K k s t i x => @lem4466308 A K k s t i x h0) (fun h0 : term304 A K i x k s t => @lem4466481 A K i x k s t h0)). Qed.
Lemma lem4466483 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term345 A K i x k s t) : (term345 A K i x k s t) = False.
Proof. exact (prop_ext (fun h2 : term345 A K i x k s t => @lem4466482 A K i x k s t h1) (fun h2 : False => @lem4465917 A K i x k s t h1)). Qed.
Lemma lem4466484 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term345 A K i x k s t) : False.
Proof. exact (EQ_MP (@lem4466483 A K i x k s t h1) (@lem4465917 A K i x k s t h1)). Qed.
Lemma lem4466485 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term348 A K i k s t) : False.
Proof. exact (ex_elim (@lem4465792 A K i k s t h1) (fun x : A => fun h0 : term347 A K i k s t x => @lem4466484 A K i x k s t h0)). Qed.
Lemma lem4466486 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term162 A K k s t) : False.
Proof. exact (ex_elim (@lem4465791 A K k s t h1) (fun i : K => fun h0 : term349 A K k s t i => @lem4466485 A K i k s t h0)). Qed.
Lemma lem4466487 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term162 A K k s t) : (term162 A K k s t) = False.
Proof. exact (prop_ext (fun h2 : term162 A K k s t => @lem4466486 A K k s t h1) (fun h2 : False => @lem4465204 A K k s t h1)). Qed.
Lemma lem4466488 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term162 A K k s t) : False.
Proof. exact (EQ_MP (@lem4466487 A K k s t h1) (@lem4465204 A K k s t h1)). Qed.
Lemma lem4466489 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term161 A K k s t.
Proof. exact (fun h0 : term162 A K k s t => @lem4466488 A K k s t h0). Qed.
Lemma lem4466490 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term134 A K s k t) = (term146 A K k s t).
Proof. exact (EQ_MP (@lem4465203 A K k s t) (@lem4466489 A K k s t)). Qed.
Lemma lem4466495 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term148 A K k s.
Proof. exact (fun t : type1470 A K => @lem4466490 A K k s t). Qed.
Lemma lem4466500 {A K : Type'} (k : K -> Prop) : term150 A K k.
Proof. exact (fun s : type1470 A K => @lem4466495 A K k s). Qed.
Lemma lem4466505 {A K : Type'} : term152 A K.
Proof. exact (fun k : K -> Prop => @lem4466500 A K k). Qed.
Lemma lem4466506 {A K : Type'} : term154 A K.
Proof. exact (EQ_MP (@lem4465199 A K) (@lem4466505 A K)). Qed.
Lemma lem4466508 {A K : Type'} : term154 A K.
Proof. exact (@lem4465048 A K (@lem4466506 A K)). Qed.
Lemma lem4466509 {A K : Type'} (h1 : term155 A K) : False.
Proof. exact (@lem4466508 A K (@lem4465032 A K h1)). Qed.
Lemma lem4466510 {A K : Type'} (h1 : term155 A K) : (term155 A K) = False.
Proof. exact (prop_ext (fun h2 : term155 A K => @lem4466509 A K h1) (fun h2 : False => @lem4465032 A K h1)). Qed.
Lemma lem4466511 {A K : Type'} (h1 : term155 A K) : False.
Proof. exact (EQ_MP (@lem4466510 A K h1) (@lem4465032 A K h1)). Qed.
Lemma lem4466512 {A K : Type'} : term154 A K.
Proof. exact (fun h0 : term155 A K => @lem4466511 A K h0). Qed.
Lemma lem4466513 {A K : Type'} : term152 A K.
Proof. exact (EQ_MP (@lem4465031 A K) (@lem4466512 A K)). Qed.
Lemma lem4466515 {A K : Type'} : term124 A K.
Proof. exact (EQ_MP (@lem4465027 A K) (@lem4466513 A K)). Qed.
Lemma lem4466516 {A K : Type'} : term108 A K.
Proof. exact (EQ_MP (@lem4464835 A K) (@lem4466515 A K)). Qed.
Lemma lem4466517 {A K : Type'} : term107 A K.
Proof. exact (EQ_MP (@lem4464716 A K) (@lem4466516 A K)). Qed.
