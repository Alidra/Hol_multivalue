Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJOINT_UNION_EQ_EMPTY_term_abbrevs.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_ELIM_PAIR_THM_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import disjoint_union_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm82_spec.
Lemma lem4490499 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4490500 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4490501 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem4490500 A x) (@lem4490499 A x)). Qed.
Lemma lem4490502 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4490504 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term3 _88435 _88436 P.
Proof. exact (@lem3405756 _88435 _88436 P). Qed.
Lemma lem4490505 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term3 _88435 _88436 P) = (term4 _88435 _88436 P).
Proof. exact (eq_refl (term3 _88435 _88436 P)). Qed.
Lemma lem4490506 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term4 _88435 _88436 P.
Proof. exact (EQ_MP (@lem4490505 _88435 _88436 P) (@lem4490504 _88435 _88436 P)). Qed.
Lemma lem4490507 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term5 _88435 _88436 P a.
Proof. exact (@lem4490506 _88435 _88436 P a). Qed.
Lemma lem4490508 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term5 _88435 _88436 P a) = (term6 _88435 _88436 P a).
Proof. exact (eq_refl (term5 _88435 _88436 P a)). Qed.
Lemma lem4490509 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term6 _88435 _88436 P a.
Proof. exact (EQ_MP (@lem4490508 _88435 _88436 P a) (@lem4490507 _88435 _88436 P a)). Qed.
Lemma lem4490510 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : term7 _88435 _88436 P a b.
Proof. exact (@lem4490509 _88435 _88436 P a b). Qed.
Lemma lem4490511 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term7 _88435 _88436 P a b) = ((term8 _88435 _88436 a b P) = (P a b)).
Proof. exact (eq_refl (term7 _88435 _88436 P a b)). Qed.
Lemma lem4490513 {A K : Type'} (k : K -> Prop) : term9 A K k.
Proof. exact (@lem4464464 A K k). Qed.
Lemma lem4490514 {A K : Type'} (k : K -> Prop) : (term9 A K k) = (term10 A K k).
Proof. exact (eq_refl (term9 A K k)). Qed.
Lemma lem4490515 {A K : Type'} (k : K -> Prop) : term10 A K k.
Proof. exact (EQ_MP (@lem4490514 A K k) (@lem4490513 A K k)). Qed.
Lemma lem4490516 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term11 A K k s.
Proof. exact (@lem4490515 A K k s). Qed.
Lemma lem4490517 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term11 A K k s) = ((@disjoint_union A K k s) = (term12 A K k s)).
Proof. exact (eq_refl (term11 A K k s)). Qed.
Lemma lem4490519 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term13 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4490520 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term13 _5106 _5107 P) = ((term14 _5106 _5107 P) = (term15 _5106 _5107 P)).
Proof. exact (eq_refl (term13 _5106 _5107 P)). Qed.
Lemma lem4490522 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4490523 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem4490524 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (EQ_MP (@lem4490523 A s) (@lem4490522 A s)). Qed.
Lemma lem4490525 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term18 A s t.
Proof. exact (@lem4490524 A s t). Qed.
Lemma lem4490526 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = ((s = t) = (term19 A s t)).
Proof. exact (eq_refl (term18 A s t)). Qed.
Lemma lem4490547 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem4490526 A s t) (@lem4490525 A s t)). Qed.
Lemma lem4490548 {A K : Type'} (s : type1223 A K) (t : type1223 A K) : (s = t) = (term20 A K s t).
Proof. exact (@lem4490547 (prod K A) s t). Qed.
Lemma lem4490549 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@disjoint_union A K k s) = (@EMPTY (prod K A))) = (term21 A K k s).
Proof. exact (@lem4490548 A K (@disjoint_union A K k s) (@EMPTY (prod K A))). Qed.
Lemma lem4490555 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term14 _5106 _5107 P) = (term15 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4490520 _5106 _5107 P) (@lem4490519 _5106 _5107 P)). Qed.
Lemma lem4490556 {A K : Type'} (P : type1223 A K) : (term14 A K P) = (term15 A K P).
Proof. exact (@lem4490555 A K P). Qed.
Lemma lem4490557 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term22 A K k s) = (term23 A K k s).
Proof. exact (@lem4490556 A K (term24 A K k s)). Qed.
Lemma lem4490558 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term25 A K k s x) = ((term26 A K x k s) = (@IN (prod K A) x (@EMPTY (prod K A)))).
Proof. exact (eq_refl (term25 A K k s x)). Qed.
Lemma lem4490559 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term27 A K k s) = (term24 A K k s).
Proof. exact (fun_ext (fun x : prod K A => @lem4490558 A K k s x)). Qed.
Lemma lem4490560 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4490561 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term22 A K k s) = (term21 A K k s).
Proof. exact (MK_COMB (@lem4490560 A K) (@lem4490559 A K k s)). Qed.
Lemma lem4490562 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4490563 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term28 A K k s) = (term29 A K k s).
Proof. exact (MK_COMB (@lem4490562) (@lem4490561 A K k s)). Qed.
Lemma lem4490564 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term30 A K k s p1 p2) = ((term31 A K p1 p2 k s) = (term32 A K p1 p2)).
Proof. exact (eq_refl (term30 A K k s p1 p2)). Qed.
Lemma lem4490565 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term33 A K k s p1) = (term34 A K k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4490564 A K k s p1 p2)). Qed.
Lemma lem4490566 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4490567 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term35 A K k s p1) = (term36 A K k s p1).
Proof. exact (MK_COMB (@lem4490566 A) (@lem4490565 A K k s p1)). Qed.
Lemma lem4490568 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term37 A K k s) = (term38 A K k s).
Proof. exact (fun_ext (fun p1 : K => @lem4490567 A K k s p1)). Qed.
Lemma lem4490569 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4490570 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term23 A K k s) = (term39 A K k s).
Proof. exact (MK_COMB (@lem4490569 K) (@lem4490568 A K k s)). Qed.
Lemma lem4490571 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term22 A K k s) = (term23 A K k s)) = ((term21 A K k s) = (term39 A K k s)).
Proof. exact (MK_COMB (@lem4490563 A K k s) (@lem4490570 A K k s)). Qed.
Lemma lem4490572 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term21 A K k s) = (term39 A K k s).
Proof. exact (EQ_MP (@lem4490571 A K k s) (@lem4490557 A K k s)). Qed.
Lemma lem4490579 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@disjoint_union A K k s) = (@EMPTY (prod K A))) = (term39 A K k s).
Proof. exact (TRANS (@lem4490549 A K k s) (@lem4490572 A K k s)). Qed.
Lemma lem4490591 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term12 A K k s).
Proof. exact (EQ_MP (@lem4490517 A K k s) (@lem4490516 A K k s)). Qed.
Lemma lem4490592 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term12 A K k s).
Proof. exact (@lem4490591 A K k s). Qed.
Lemma lem4490603 {A K : Type'} (p1 : K) (p2 : A) : (term40 A K p1 p2) = (term40 A K p1 p2).
Proof. exact (eq_refl (term40 A K p1 p2)). Qed.
Lemma lem4490604 {A K : Type'} (p1 : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) : (term31 A K p1 p2 k s) = (term41 A K p1 p2 k s).
Proof. exact (MK_COMB (@lem4490603 A K p1 p2) (@lem4490592 A K k s)). Qed.
Lemma lem4490606 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term8 _88435 _88436 a b P) = (P a b).
Proof. exact (EQ_MP (@lem4490511 _88435 _88436 P a b) (@lem4490510 _88435 _88436 P a b)). Qed.
Lemma lem4490607 {A K : Type'} (P : type1470 A K) (a : K) (b : A) : (term8 A K a b P) = (P a b).
Proof. exact (@lem4490606 A K P a b). Qed.
Lemma lem4490608 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term42 A K p1 p2 k s) = (term43 A K k s p1 p2).
Proof. exact (@lem4490607 A K (term44 A K k s) p1 p2). Qed.
Lemma lem4490609 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term45 A K k s i) = (term46 A K k s i).
Proof. exact (eq_refl (term45 A K k s i)). Qed.
Lemma lem4490610 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4490611 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term43 A K k s i x) = (term47 A K k s i x).
Proof. exact (MK_COMB (@lem4490609 A K k s i) (@lem4490610 A x)). Qed.
Lemma lem4490612 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term47 A K k s i x) = (term48 A K k x s i).
Proof. exact (eq_refl (term47 A K k s i x)). Qed.
Lemma lem4490613 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term43 A K k s i x) = (term48 A K k x s i).
Proof. exact (TRANS (@lem4490611 A K k s i x) (@lem4490612 A K k x s i)). Qed.
Lemma lem4490614 {A K : Type'} (GEN_PVAR_143 : prod K A) : (@SETSPEC (prod K A) GEN_PVAR_143) = (@SETSPEC (prod K A) GEN_PVAR_143).
Proof. exact (eq_refl (@SETSPEC (prod K A) GEN_PVAR_143)). Qed.
Lemma lem4490615 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term49 A K GEN_PVAR_143 k s i x) = (term50 A K GEN_PVAR_143 k x s i).
Proof. exact (MK_COMB (@lem4490614 A K GEN_PVAR_143) (@lem4490613 A K k x s i)). Qed.
Lemma lem4490616 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4490617 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term51 A K GEN_PVAR_143 k s i x) = (term52 A K GEN_PVAR_143 k s i x).
Proof. exact (MK_COMB (@lem4490615 A K GEN_PVAR_143 k x s i) (@lem4490616 A K i x)). Qed.
Lemma lem4490618 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term53 A K GEN_PVAR_143 k s i) = (term54 A K GEN_PVAR_143 k s i).
Proof. exact (fun_ext (fun x : A => @lem4490617 A K GEN_PVAR_143 k s i x)). Qed.
Lemma lem4490619 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4490620 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term55 A K GEN_PVAR_143 k s i) = (term56 A K GEN_PVAR_143 k s i).
Proof. exact (MK_COMB (@lem4490619 A) (@lem4490618 A K GEN_PVAR_143 k s i)). Qed.
Lemma lem4490621 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) : (term57 A K GEN_PVAR_143 k s) = (term58 A K GEN_PVAR_143 k s).
Proof. exact (fun_ext (fun i : K => @lem4490620 A K GEN_PVAR_143 k s i)). Qed.
Lemma lem4490622 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4490623 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) : (term59 A K GEN_PVAR_143 k s) = (term60 A K GEN_PVAR_143 k s).
Proof. exact (MK_COMB (@lem4490622 K) (@lem4490621 A K GEN_PVAR_143 k s)). Qed.
Lemma lem4490624 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term61 A K k s) = (term62 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_143 : prod K A => @lem4490623 A K GEN_PVAR_143 k s)). Qed.
Lemma lem4490625 {A K : Type'} : (@GSPEC (prod K A)) = (@GSPEC (prod K A)).
Proof. exact (eq_refl (@GSPEC (prod K A))). Qed.
Lemma lem4490626 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term63 A K k s) = (term12 A K k s).
Proof. exact (MK_COMB (@lem4490625 A K) (@lem4490624 A K k s)). Qed.
Lemma lem4490627 {A K : Type'} (p1 : K) (p2 : A) : (term40 A K p1 p2) = (term40 A K p1 p2).
Proof. exact (eq_refl (term40 A K p1 p2)). Qed.
Lemma lem4490628 {A K : Type'} (p1 : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) : (term42 A K p1 p2 k s) = (term41 A K p1 p2 k s).
Proof. exact (MK_COMB (@lem4490627 A K p1 p2) (@lem4490626 A K k s)). Qed.
Lemma lem4490629 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4490630 {A K : Type'} (p1 : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) : (term64 A K p1 p2 k s) = (term65 A K p1 p2 k s).
Proof. exact (MK_COMB (@lem4490629) (@lem4490628 A K p1 p2 k s)). Qed.
Lemma lem4490631 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term45 A K k s p1) = (term46 A K k s p1).
Proof. exact (eq_refl (term45 A K k s p1)). Qed.
Lemma lem4490632 {A : Type'} (p2 : A) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem4490633 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term43 A K k s p1 p2) = (term47 A K k s p1 p2).
Proof. exact (MK_COMB (@lem4490631 A K k s p1) (@lem4490632 A p2)). Qed.
Lemma lem4490634 {A K : Type'} (k : K -> Prop) (p2 : A) (s : type1470 A K) (p1 : K) : (term47 A K k s p1 p2) = (term48 A K k p2 s p1).
Proof. exact (eq_refl (term47 A K k s p1 p2)). Qed.
Lemma lem4490635 {A K : Type'} (k : K -> Prop) (p2 : A) (s : type1470 A K) (p1 : K) : (term43 A K k s p1 p2) = (term48 A K k p2 s p1).
Proof. exact (TRANS (@lem4490633 A K k s p1 p2) (@lem4490634 A K k p2 s p1)). Qed.
Lemma lem4490636 {A K : Type'} (k : K -> Prop) (p2 : A) (s : type1470 A K) (p1 : K) : ((term42 A K p1 p2 k s) = (term43 A K k s p1 p2)) = ((term41 A K p1 p2 k s) = (term48 A K k p2 s p1)).
Proof. exact (MK_COMB (@lem4490630 A K p1 p2 k s) (@lem4490635 A K k p2 s p1)). Qed.
Lemma lem4490637 {A K : Type'} (k : K -> Prop) (p2 : A) (s : type1470 A K) (p1 : K) : (term41 A K p1 p2 k s) = (term48 A K k p2 s p1).
Proof. exact (EQ_MP (@lem4490636 A K k p2 s p1) (@lem4490608 A K k s p1 p2)). Qed.
Lemma lem4490640 {A K : Type'} (k : K -> Prop) (p2 : A) (s : type1470 A K) (p1 : K) : (term31 A K p1 p2 k s) = (term48 A K k p2 s p1).
Proof. exact (TRANS (@lem4490604 A K p1 p2 k s) (@lem4490637 A K k p2 s p1)). Qed.
Lemma lem4490641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4490642 {A K : Type'} (k : K -> Prop) (p2 : A) (s : type1470 A K) (p1 : K) : (term66 A K p1 p2 k s) = (term67 A K k p2 s p1).
Proof. exact (MK_COMB (@lem4490641) (@lem4490640 A K k p2 s p1)). Qed.
Lemma lem4490644 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4490502 A x (@lem4490501 A x)). Qed.
Lemma lem4490645 {A K : Type'} (x : prod K A) : (@IN (prod K A) x (@EMPTY (prod K A))) = False.
Proof. exact (@lem4490644 (prod K A) x). Qed.
Lemma lem4490646 {A K : Type'} (p1 : K) (p2 : A) : (term32 A K p1 p2) = False.
Proof. exact (@lem4490645 A K (@pair K A p1 p2)). Qed.
Lemma lem4490647 {A K : Type'} (k : K -> Prop) (p2 : A) (s : type1470 A K) (p1 : K) : ((term31 A K p1 p2 k s) = (term32 A K p1 p2)) = ((term48 A K k p2 s p1) = False).
Proof. exact (MK_COMB (@lem4490642 A K k p2 s p1) (@lem4490646 A K p1 p2)). Qed.
Lemma lem4490649 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4490650 {A K : Type'} (k : K -> Prop) (p2 : A) (s : type1470 A K) (p1 : K) : ((term48 A K k p2 s p1) = False) = (term68 A K k p2 s p1).
Proof. exact (@lem4490649 (term48 A K k p2 s p1)). Qed.
Lemma lem4490653 {A K : Type'} (k : K -> Prop) (p2 : A) (s : type1470 A K) (p1 : K) : ((term31 A K p1 p2 k s) = (term32 A K p1 p2)) = (term68 A K k p2 s p1).
Proof. exact (TRANS (@lem4490647 A K k p2 s p1) (@lem4490650 A K k p2 s p1)). Qed.
Lemma lem4490654 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term34 A K k s p1) = (term69 A K k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4490653 A K k p2 s p1)). Qed.
Lemma lem4490655 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4490656 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term36 A K k s p1) = (term70 A K k s p1).
Proof. exact (MK_COMB (@lem4490655 A) (@lem4490654 A K k s p1)). Qed.
Lemma lem4490663 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term38 A K k s) = (term71 A K k s).
Proof. exact (fun_ext (fun p1 : K => @lem4490656 A K k s p1)). Qed.
Lemma lem4490664 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4490665 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term39 A K k s) = (term72 A K k s).
Proof. exact (MK_COMB (@lem4490664 K) (@lem4490663 A K k s)). Qed.
Lemma lem4490672 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@disjoint_union A K k s) = (@EMPTY (prod K A))) = (term72 A K k s).
Proof. exact (TRANS (@lem4490579 A K k s) (@lem4490665 A K k s)). Qed.
Lemma lem4490673 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4490674 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term73 A K k s) = (term74 A K k s).
Proof. exact (MK_COMB (@lem4490673) (@lem4490672 A K k s)). Qed.
Lemma lem4490686 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem4490526 A s t) (@lem4490525 A s t)). Qed.
Lemma lem4490687 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (@lem4490686 A s t). Qed.
Lemma lem4490688 {A K : Type'} (s : type1470 A K) (i : K) : ((s i) = (@EMPTY A)) = (term75 A K s i).
Proof. exact (@lem4490687 A (s i) (@EMPTY A)). Qed.
Lemma lem4490700 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4490502 A x (@lem4490501 A x)). Qed.
Lemma lem4490701 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4490700 A x). Qed.
Lemma lem4490702 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term76 A K x s i) = (term76 A K x s i).
Proof. exact (eq_refl (term76 A K x s i)). Qed.
Lemma lem4490703 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : ((term77 A K x s i) = (@IN A x (@EMPTY A))) = ((term77 A K x s i) = False).
Proof. exact (MK_COMB (@lem4490702 A K x s i) (@lem4490701 A x)). Qed.
Lemma lem4490705 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4490706 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : ((term77 A K x s i) = False) = (term78 A K x s i).
Proof. exact (@lem4490705 (term77 A K x s i)). Qed.
Lemma lem4490707 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : ((term77 A K x s i) = (@IN A x (@EMPTY A))) = (term78 A K x s i).
Proof. exact (TRANS (@lem4490703 A K x s i) (@lem4490706 A K x s i)). Qed.
Lemma lem4490708 {A K : Type'} (s : type1470 A K) (i : K) : (term79 A K s i) = (term80 A K s i).
Proof. exact (fun_ext (fun x : A => @lem4490707 A K x s i)). Qed.
Lemma lem4490709 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4490710 {A K : Type'} (s : type1470 A K) (i : K) : (term75 A K s i) = (term81 A K s i).
Proof. exact (MK_COMB (@lem4490709 A) (@lem4490708 A K s i)). Qed.
Lemma lem4490717 {A K : Type'} (s : type1470 A K) (i : K) : ((s i) = (@EMPTY A)) = (term81 A K s i).
Proof. exact (TRANS (@lem4490688 A K s i) (@lem4490710 A K s i)). Qed.
Lemma lem4490718 {K : Type'} (i : K) (k : K -> Prop) : (term82 K i k) = (term82 K i k).
Proof. exact (eq_refl (term82 K i k)). Qed.
Lemma lem4490719 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term83 A K k s i) = (term84 A K k s i).
Proof. exact (MK_COMB (@lem4490718 K i k) (@lem4490717 A K s i)). Qed.
Lemma lem4490722 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term85 A K k s) = (term86 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4490719 A K k s i)). Qed.
Lemma lem4490723 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4490724 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term87 A K k s) = (term88 A K k s).
Proof. exact (MK_COMB (@lem4490723 K) (@lem4490722 A K k s)). Qed.
Lemma lem4490731 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (((@disjoint_union A K k s) = (@EMPTY (prod K A))) = (term87 A K k s)) = ((term72 A K k s) = (term88 A K k s)).
Proof. exact (MK_COMB (@lem4490674 A K k s) (@lem4490724 A K k s)). Qed.
Lemma lem4490736 {A K : Type'} (k : K -> Prop) : (term89 A K k) = (term90 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4490731 A K k s)). Qed.
Lemma lem4490737 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4490738 {A K : Type'} (k : K -> Prop) : (term91 A K k) = (term92 A K k).
Proof. exact (MK_COMB (@lem4490737 A K) (@lem4490736 A K k)). Qed.
Lemma lem4490745 {A K : Type'} : (term93 A K) = (term94 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4490738 A K k)). Qed.
Lemma lem4490746 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4490747 {A K : Type'} : (term95 A K) = (term96 A K).
Proof. exact (MK_COMB (@lem4490746 K) (@lem4490745 A K)). Qed.
Lemma lem4490754 {A K : Type'} : (term96 A K) = (term95 A K).
Proof. exact (SYM (@lem4490747 A K)). Qed.
Lemma lem4490810 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4490811 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4490810 K P x). Qed.
Lemma lem4490812 {K : Type'} (k : K -> Prop) (p1 : K) : (@IN K p1 k) = (k p1).
Proof. exact (@lem4490811 K k p1). Qed.
Lemma lem4490813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4490814 {K : Type'} (k : K -> Prop) (p1 : K) : (term97 K p1 k) = (term98 K k p1).
Proof. exact (MK_COMB (@lem4490813) (@lem4490812 K k p1)). Qed.
Lemma lem4490816 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4490817 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4490816 A P x). Qed.
Lemma lem4490818 {A K : Type'} (s : type1470 A K) (p1 : K) (p2 : A) : (term77 A K p2 s p1) = (s p1 p2).
Proof. exact (@lem4490817 A (s p1) p2). Qed.
Lemma lem4490819 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term48 A K k p2 s p1) = (term99 A K k s p1 p2).
Proof. exact (MK_COMB (@lem4490814 K k p1) (@lem4490818 A K s p1 p2)). Qed.
Lemma lem4490822 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4490823 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term68 A K k p2 s p1) = (term100 A K k s p1 p2).
Proof. exact (MK_COMB (@lem4490822) (@lem4490819 A K k s p1 p2)). Qed.
Lemma lem4490824 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term69 A K k s p1) = (term101 A K k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4490823 A K k s p1 p2)). Qed.
Lemma lem4490825 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4490826 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term70 A K k s p1) = (term102 A K k s p1).
Proof. exact (MK_COMB (@lem4490825 A) (@lem4490824 A K k s p1)). Qed.
Lemma lem4490831 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term71 A K k s) = (term103 A K k s).
Proof. exact (fun_ext (fun p1 : K => @lem4490826 A K k s p1)). Qed.
Lemma lem4490832 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4490833 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term72 A K k s) = (term104 A K k s).
Proof. exact (MK_COMB (@lem4490832 K) (@lem4490831 A K k s)). Qed.
Lemma lem4490838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4490839 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term74 A K k s) = (term105 A K k s).
Proof. exact (MK_COMB (@lem4490838) (@lem4490833 A K k s)). Qed.
Lemma lem4490847 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4490848 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4490847 K P x). Qed.
Lemma lem4490849 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4490848 K k i). Qed.
Lemma lem4490850 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4490851 {K : Type'} (k : K -> Prop) (i : K) : (term82 K i k) = (term106 K k i).
Proof. exact (MK_COMB (@lem4490850) (@lem4490849 K k i)). Qed.
Lemma lem4490857 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4490858 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4490857 A P x). Qed.
Lemma lem4490859 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term77 A K x s i) = (s i x).
Proof. exact (@lem4490858 A (s i) x). Qed.
Lemma lem4490860 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4490861 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term78 A K x s i) = (term107 A K s i x).
Proof. exact (MK_COMB (@lem4490860) (@lem4490859 A K s i x)). Qed.
Lemma lem4490862 {A K : Type'} (s : type1470 A K) (i : K) : (term80 A K s i) = (term108 A K s i).
Proof. exact (fun_ext (fun x : A => @lem4490861 A K s i x)). Qed.
Lemma lem4490863 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4490864 {A K : Type'} (s : type1470 A K) (i : K) : (term81 A K s i) = (term109 A K s i).
Proof. exact (MK_COMB (@lem4490863 A) (@lem4490862 A K s i)). Qed.
Lemma lem4490869 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term84 A K k s i) = (term110 A K k s i).
Proof. exact (MK_COMB (@lem4490851 K k i) (@lem4490864 A K s i)). Qed.
Lemma lem4490872 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term86 A K k s) = (term111 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4490869 A K k s i)). Qed.
Lemma lem4490873 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4490874 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term88 A K k s) = (term112 A K k s).
Proof. exact (MK_COMB (@lem4490873 K) (@lem4490872 A K k s)). Qed.
Lemma lem4490879 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term72 A K k s) = (term88 A K k s)) = ((term104 A K k s) = (term112 A K k s)).
Proof. exact (MK_COMB (@lem4490839 A K k s) (@lem4490874 A K k s)). Qed.
Lemma lem4490882 {A K : Type'} (k : K -> Prop) : (term90 A K k) = (term113 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4490879 A K k s)). Qed.
Lemma lem4490883 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4490884 {A K : Type'} (k : K -> Prop) : (term92 A K k) = (term114 A K k).
Proof. exact (MK_COMB (@lem4490883 A K) (@lem4490882 A K k)). Qed.
Lemma lem4490889 {A K : Type'} : (term94 A K) = (term115 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4490884 A K k)). Qed.
Lemma lem4490890 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4490891 {A K : Type'} : (term96 A K) = (term116 A K).
Proof. exact (MK_COMB (@lem4490890 K) (@lem4490889 A K)). Qed.
Lemma lem4490896 {A K : Type'} : (term116 A K) = (term96 A K).
Proof. exact (SYM (@lem4490891 A K)). Qed.
Lemma lem4490898 (p : Prop) : p = (term117 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4490899 {A K : Type'} : (term116 A K) = (term118 A K).
Proof. exact (@lem4490898 (term116 A K)). Qed.
Lemma lem4490900 {A K : Type'} : (term118 A K) = (term116 A K).
Proof. exact (SYM (@lem4490899 A K)). Qed.
Lemma lem4490901 {A K : Type'} (h1 : term119 A K) : term119 A K.
Proof. exact (h1). Qed.
Lemma lem4490904 {A K : Type'} (h1 : term118 A K) : term118 A K.
Proof. exact (h1). Qed.
Lemma lem4490905 {A K : Type'} : term120 A K.
Proof. exact (fun h0 : term118 A K => @lem4490904 A K h0). Qed.
Lemma lem4490906 {A K : Type'} (h1 : term120 A K) : term120 A K.
Proof. exact (h1). Qed.
Lemma lem4490907 {A K : Type'} (h1 : term118 A K) : term118 A K.
Proof. exact (h1). Qed.
Lemma lem4490908 {A K : Type'} (h1 : term118 A K) (h2 : term120 A K) : term118 A K.
Proof. exact (@lem4490906 A K h2 (@lem4490907 A K h1)). Qed.
Lemma lem4490909 {A K : Type'} (h1 : term118 A K) : term121 A K.
Proof. exact (fun h0 : term120 A K => @lem4490908 A K h1 h0). Qed.
Lemma lem4490910 {A K : Type'} (h1 : term120 A K) : term120 A K.
Proof. exact (h1). Qed.
Lemma lem4490911 {A K : Type'} (h1 : term118 A K) (h2 : term120 A K) : term118 A K.
Proof. exact (@lem4490909 A K h1 (@lem4490910 A K h2)). Qed.
Lemma lem4490912 {A K : Type'} (h1 : term120 A K) : term120 A K.
Proof. exact (fun h0 : term118 A K => @lem4490911 A K h0 h1). Qed.
Lemma lem4490913 {A K : Type'} : term122 A K.
Proof. exact (fun h0 : term120 A K => @lem4490912 A K h0). Qed.
Lemma lem4490916 {A K : Type'} : term120 A K.
Proof. exact (@lem4490913 A K (@lem4490905 A K)). Qed.
Lemma lem4490917 {A K : Type'} : term120 A K.
Proof. exact (@lem4490916 A K). Qed.
Lemma lem4490919 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4490920 {A K : Type'} : (term118 A K) = (term123 A K).
Proof. exact (@lem4490919 (term119 A K)). Qed.
Lemma lem4490922 (t : Prop) : (term124 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4490923 {A K : Type'} : (term123 A K) = (term116 A K).
Proof. exact (@lem4490922 (term116 A K)). Qed.
Lemma lem4490956 {A K : Type'} : (term118 A K) = (term116 A K).
Proof. exact (TRANS (@lem4490920 A K) (@lem4490923 A K)). Qed.
Lemma lem4490959 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term107 A K s i x) = (term107 A K s i x).
Proof. exact (eq_refl (term107 A K s i x)). Qed.
Lemma lem4490960 {A K : Type'} (s : type1470 A K) (i : K) : (term108 A K s i) = (term108 A K s i).
Proof. exact (fun_ext (fun x : A => @lem4490959 A K s i x)). Qed.
Lemma lem4490961 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4490962 {A K : Type'} (s : type1470 A K) (i : K) : (term109 A K s i) = (term109 A K s i).
Proof. exact (MK_COMB (@lem4490961 A) (@lem4490960 A K s i)). Qed.
Lemma lem4490965 {K : Type'} (k : K -> Prop) (i : K) : (term106 K k i) = (term106 K k i).
Proof. exact (eq_refl (term106 K k i)). Qed.
Lemma lem4490966 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term110 A K k s i) = (term110 A K k s i).
Proof. exact (MK_COMB (@lem4490965 K k i) (@lem4490962 A K s i)). Qed.
Lemma lem4490967 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term111 A K k s) = (term111 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4490966 A K k s i)). Qed.
Lemma lem4490968 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4490969 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term112 A K k s) = (term112 A K k s).
Proof. exact (MK_COMB (@lem4490968 K) (@lem4490967 A K k s)). Qed.
Lemma lem4490976 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term100 A K k s p1 p2) = (term100 A K k s p1 p2).
Proof. exact (eq_refl (term100 A K k s p1 p2)). Qed.
Lemma lem4490977 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term101 A K k s p1) = (term101 A K k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4490976 A K k s p1 p2)). Qed.
Lemma lem4490978 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4490979 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term102 A K k s p1) = (term102 A K k s p1).
Proof. exact (MK_COMB (@lem4490978 A) (@lem4490977 A K k s p1)). Qed.
Lemma lem4490980 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term103 A K k s) = (term103 A K k s).
Proof. exact (fun_ext (fun p1 : K => @lem4490979 A K k s p1)). Qed.
Lemma lem4490981 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4490982 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term104 A K k s) = (term104 A K k s).
Proof. exact (MK_COMB (@lem4490981 K) (@lem4490980 A K k s)). Qed.
Lemma lem4490983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4490984 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term105 A K k s) = (term105 A K k s).
Proof. exact (MK_COMB (@lem4490983) (@lem4490982 A K k s)). Qed.
Lemma lem4490985 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term104 A K k s) = (term112 A K k s)) = ((term104 A K k s) = (term112 A K k s)).
Proof. exact (MK_COMB (@lem4490984 A K k s) (@lem4490969 A K k s)). Qed.
Lemma lem4490986 {A K : Type'} (k : K -> Prop) : (term113 A K k) = (term113 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4490985 A K k s)). Qed.
Lemma lem4490987 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4490988 {A K : Type'} (k : K -> Prop) : (term114 A K k) = (term114 A K k).
Proof. exact (MK_COMB (@lem4490987 A K) (@lem4490986 A K k)). Qed.
Lemma lem4490989 {A K : Type'} : (term115 A K) = (term115 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4490988 A K k)). Qed.
Lemma lem4490990 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4490991 {A K : Type'} : (term116 A K) = (term116 A K).
Proof. exact (MK_COMB (@lem4490990 K) (@lem4490989 A K)). Qed.
Lemma lem4491034 {A K : Type'} : (term118 A K) = (term116 A K).
Proof. exact (TRANS (@lem4490956 A K) (@lem4490991 A K)). Qed.
Lemma lem4491035 {A K : Type'} : (term116 A K) = (term118 A K).
Proof. exact (SYM (@lem4491034 A K)). Qed.
Lemma lem4491037 (p : Prop) : p = (term117 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4491038 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term104 A K k s) = (term112 A K k s)) = (term125 A K k s).
Proof. exact (@lem4491037 ((term104 A K k s) = (term112 A K k s))). Qed.
Lemma lem4491039 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term125 A K k s) = ((term104 A K k s) = (term112 A K k s)).
Proof. exact (SYM (@lem4491038 A K k s)). Qed.
Lemma lem4491040 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term126 A K k s) : term126 A K k s.
Proof. exact (h1). Qed.
Lemma lem4491049 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term100 A K k s p1 p2) = (term127 A K k s p1 p2).
Proof. exact (@lem17045 (k p1) (s p1 p2)). Qed.
Lemma lem4491054 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term128 A K k s p1 p2) = (term99 A K k s p1 p2).
Proof. exact (@lem16933 (term99 A K k s p1 p2)). Qed.
Lemma lem4491055 {A : Type'} (P : A -> Prop) : (term129 A P) = (term130 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4491056 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term131 A K k s p1) = (term132 A K k s p1).
Proof. exact (@lem4491055 A (term101 A K k s p1)). Qed.
Lemma lem4491057 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term133 A K k s p1 p2) = (term100 A K k s p1 p2).
Proof. exact (eq_refl (term133 A K k s p1 p2)). Qed.
Lemma lem4491058 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4491059 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term134 A K k s p1 p2) = (term128 A K k s p1 p2).
Proof. exact (MK_COMB (@lem4491058) (@lem4491057 A K k s p1 p2)). Qed.
Lemma lem4491060 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term134 A K k s p1 p2) = (term99 A K k s p1 p2).
Proof. exact (TRANS (@lem4491059 A K k s p1 p2) (@lem4491054 A K k s p1 p2)). Qed.
Lemma lem4491061 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term135 A K k s p1) = (term136 A K k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4491060 A K k s p1 p2)). Qed.
Lemma lem4491062 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4491063 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term132 A K k s p1) = (term137 A K k s p1).
Proof. exact (MK_COMB (@lem4491062 A) (@lem4491061 A K k s p1)). Qed.
Lemma lem4491064 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term131 A K k s p1) = (term137 A K k s p1).
Proof. exact (TRANS (@lem4491056 A K k s p1) (@lem4491063 A K k s p1)). Qed.
Lemma lem4491065 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term101 A K k s p1) = (term138 A K k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4491049 A K k s p1 p2)). Qed.
Lemma lem4491066 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4491067 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term102 A K k s p1) = (term139 A K k s p1).
Proof. exact (MK_COMB (@lem4491066 A) (@lem4491065 A K k s p1)). Qed.
Lemma lem4491068 {K : Type'} (P : K -> Prop) : (term129 K P) = (term130 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4491069 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term140 A K k s) = (term141 A K k s).
Proof. exact (@lem4491068 K (term103 A K k s)). Qed.
Lemma lem4491070 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term142 A K k s p1) = (term102 A K k s p1).
Proof. exact (eq_refl (term142 A K k s p1)). Qed.
Lemma lem4491071 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4491072 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term143 A K k s p1) = (term131 A K k s p1).
Proof. exact (MK_COMB (@lem4491071) (@lem4491070 A K k s p1)). Qed.
Lemma lem4491073 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term143 A K k s p1) = (term137 A K k s p1).
Proof. exact (TRANS (@lem4491072 A K k s p1) (@lem4491064 A K k s p1)). Qed.
Lemma lem4491074 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term144 A K k s) = (term145 A K k s).
Proof. exact (fun_ext (fun p1 : K => @lem4491073 A K k s p1)). Qed.
Lemma lem4491075 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4491076 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term141 A K k s) = (term146 A K k s).
Proof. exact (MK_COMB (@lem4491075 K) (@lem4491074 A K k s)). Qed.
Lemma lem4491077 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term140 A K k s) = (term146 A K k s).
Proof. exact (TRANS (@lem4491069 A K k s) (@lem4491076 A K k s)). Qed.
Lemma lem4491078 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term103 A K k s) = (term147 A K k s).
Proof. exact (fun_ext (fun p1 : K => @lem4491067 A K k s p1)). Qed.
Lemma lem4491079 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4491080 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term104 A K k s) = (term148 A K k s).
Proof. exact (MK_COMB (@lem4491079 K) (@lem4491078 A K k s)). Qed.
Lemma lem4491083 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term107 A K s i x) = (term107 A K s i x).
Proof. exact (eq_refl (term107 A K s i x)). Qed.
Lemma lem4491086 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term149 A K s i x) = (s i x).
Proof. exact (@lem16933 (s i x)). Qed.
Lemma lem4491087 {A : Type'} (P : A -> Prop) : (term129 A P) = (term130 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4491088 {A K : Type'} (s : type1470 A K) (i : K) : (term150 A K s i) = (term151 A K s i).
Proof. exact (@lem4491087 A (term108 A K s i)). Qed.
Lemma lem4491089 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term152 A K s i x) = (term107 A K s i x).
Proof. exact (eq_refl (term152 A K s i x)). Qed.
Lemma lem4491090 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4491091 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term153 A K s i x) = (term149 A K s i x).
Proof. exact (MK_COMB (@lem4491090) (@lem4491089 A K s i x)). Qed.
Lemma lem4491092 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term153 A K s i x) = (s i x).
Proof. exact (TRANS (@lem4491091 A K s i x) (@lem4491086 A K s i x)). Qed.
Lemma lem4491093 {A K : Type'} (s : type1470 A K) (i : K) : (term154 A K s i) = (term155 A K s i).
Proof. exact (fun_ext (fun x : A => @lem4491092 A K s i x)). Qed.
Lemma lem4491094 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4491095 {A K : Type'} (s : type1470 A K) (i : K) : (term151 A K s i) = (term156 A K s i).
Proof. exact (MK_COMB (@lem4491094 A) (@lem4491093 A K s i)). Qed.
Lemma lem4491096 {A K : Type'} (s : type1470 A K) (i : K) : (term150 A K s i) = (term156 A K s i).
Proof. exact (TRANS (@lem4491088 A K s i) (@lem4491095 A K s i)). Qed.
Lemma lem4491097 {A K : Type'} (s : type1470 A K) (i : K) : (term108 A K s i) = (term108 A K s i).
Proof. exact (fun_ext (fun x : A => @lem4491083 A K s i x)). Qed.
Lemma lem4491098 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4491099 {A K : Type'} (s : type1470 A K) (i : K) : (term109 A K s i) = (term109 A K s i).
Proof. exact (MK_COMB (@lem4491098 A) (@lem4491097 A K s i)). Qed.
Lemma lem4491101 {K : Type'} (k : K -> Prop) (i : K) : (term98 K k i) = (term98 K k i).
Proof. exact (eq_refl (term98 K k i)). Qed.
Lemma lem4491102 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term157 A K k s i) = (term158 A K k s i).
Proof. exact (MK_COMB (@lem4491101 K k i) (@lem4491096 A K s i)). Qed.
Lemma lem4491103 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term159 A K k s i) = (term157 A K k s i).
Proof. exact (@lem17362 (k i) (term109 A K s i)). Qed.
Lemma lem4491104 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term159 A K k s i) = (term158 A K k s i).
Proof. exact (TRANS (@lem4491103 A K k s i) (@lem4491102 A K k s i)). Qed.
Lemma lem4491106 {K : Type'} (k : K -> Prop) (i : K) : (term160 K k i) = (term160 K k i).
Proof. exact (eq_refl (term160 K k i)). Qed.
Lemma lem4491107 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term161 A K k s i) = (term161 A K k s i).
Proof. exact (MK_COMB (@lem4491106 K k i) (@lem4491099 A K s i)). Qed.
Lemma lem4491108 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term110 A K k s i) = (term161 A K k s i).
Proof. exact (@lem17265 (k i) (term109 A K s i)). Qed.
Lemma lem4491109 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term110 A K k s i) = (term161 A K k s i).
Proof. exact (TRANS (@lem4491108 A K k s i) (@lem4491107 A K k s i)). Qed.
Lemma lem4491110 {K : Type'} (P : K -> Prop) : (term129 K P) = (term130 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4491111 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term162 A K k s) = (term163 A K k s).
Proof. exact (@lem4491110 K (term111 A K k s)). Qed.
Lemma lem4491112 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term164 A K k s i) = (term110 A K k s i).
Proof. exact (eq_refl (term164 A K k s i)). Qed.
Lemma lem4491113 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4491114 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term165 A K k s i) = (term159 A K k s i).
Proof. exact (MK_COMB (@lem4491113) (@lem4491112 A K k s i)). Qed.
Lemma lem4491115 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term165 A K k s i) = (term158 A K k s i).
Proof. exact (TRANS (@lem4491114 A K k s i) (@lem4491104 A K k s i)). Qed.
Lemma lem4491116 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term166 A K k s) = (term167 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4491115 A K k s i)). Qed.
Lemma lem4491117 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4491118 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term163 A K k s) = (term168 A K k s).
Proof. exact (MK_COMB (@lem4491117 K) (@lem4491116 A K k s)). Qed.
Lemma lem4491119 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term162 A K k s) = (term168 A K k s).
Proof. exact (TRANS (@lem4491111 A K k s) (@lem4491118 A K k s)). Qed.
Lemma lem4491120 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term111 A K k s) = (term169 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4491109 A K k s i)). Qed.
Lemma lem4491121 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4491122 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term112 A K k s) = (term170 A K k s).
Proof. exact (MK_COMB (@lem4491121 K) (@lem4491120 A K k s)). Qed.
Lemma lem4491123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4491124 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term171 A K k s) = (term172 A K k s).
Proof. exact (MK_COMB (@lem4491123) (@lem4491077 A K k s)). Qed.
Lemma lem4491125 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term173 A K k s) = (term174 A K k s).
Proof. exact (MK_COMB (@lem4491124 A K k s) (@lem4491122 A K k s)). Qed.
Lemma lem4491126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4491127 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term175 A K k s) = (term176 A K k s).
Proof. exact (MK_COMB (@lem4491126) (@lem4491080 A K k s)). Qed.
Lemma lem4491128 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term177 A K k s) = (term178 A K k s).
Proof. exact (MK_COMB (@lem4491127 A K k s) (@lem4491119 A K k s)). Qed.
Lemma lem4491129 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4491130 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term179 A K k s) = (term180 A K k s).
Proof. exact (MK_COMB (@lem4491129) (@lem4491128 A K k s)). Qed.
Lemma lem4491131 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term181 A K k s) = (term182 A K k s).
Proof. exact (MK_COMB (@lem4491130 A K k s) (@lem4491125 A K k s)). Qed.
Lemma lem4491132 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term126 A K k s) = (term181 A K k s).
Proof. exact (@lem17646 (term104 A K k s) (term112 A K k s)). Qed.
Lemma lem4491133 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term126 A K k s) = (term182 A K k s).
Proof. exact (TRANS (@lem4491132 A K k s) (@lem4491131 A K k s)). Qed.
Lemma lem4491139 {A : Type'} (P : Prop) (Q : A -> Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem4491140 {A : Type'} (P : Prop) (Q : A -> Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (@lem4491139 A P Q). Qed.
Lemma lem4491141 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term185 A K k s p1) = (term186 A K k s p1).
Proof. exact (@lem4491140 A (term187 K k p1) (term108 A K s p1)). Qed.
Lemma lem4491142 {A K : Type'} (s : type1470 A K) (p1 : K) (p2 : A) : (term152 A K s p1 p2) = (term107 A K s p1 p2).
Proof. exact (eq_refl (term152 A K s p1 p2)). Qed.
Lemma lem4491143 {K : Type'} (k : K -> Prop) (p1 : K) : (term160 K k p1) = (term160 K k p1).
Proof. exact (eq_refl (term160 K k p1)). Qed.
Lemma lem4491144 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term188 A K k s p1 p2) = (term127 A K k s p1 p2).
Proof. exact (MK_COMB (@lem4491143 K k p1) (@lem4491142 A K s p1 p2)). Qed.
Lemma lem4491145 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term189 A K k s p1) = (term138 A K k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4491144 A K k s p1 p2)). Qed.
Lemma lem4491146 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4491147 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term185 A K k s p1) = (term139 A K k s p1).
Proof. exact (MK_COMB (@lem4491146 A) (@lem4491145 A K k s p1)). Qed.
Lemma lem4491148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4491149 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term190 A K k s p1) = (term191 A K k s p1).
Proof. exact (MK_COMB (@lem4491148) (@lem4491147 A K k s p1)). Qed.
Lemma lem4491150 {A K : Type'} (s : type1470 A K) (p1 : K) (p2 : A) : (term152 A K s p1 p2) = (term107 A K s p1 p2).
Proof. exact (eq_refl (term152 A K s p1 p2)). Qed.
Lemma lem4491151 {A K : Type'} (s : type1470 A K) (p1 : K) : (term192 A K s p1) = (term108 A K s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4491150 A K s p1 p2)). Qed.
Lemma lem4491152 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4491153 {A K : Type'} (s : type1470 A K) (p1 : K) : (term193 A K s p1) = (term109 A K s p1).
Proof. exact (MK_COMB (@lem4491152 A) (@lem4491151 A K s p1)). Qed.
Lemma lem4491154 {K : Type'} (k : K -> Prop) (p1 : K) : (term160 K k p1) = (term160 K k p1).
Proof. exact (eq_refl (term160 K k p1)). Qed.
Lemma lem4491155 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term186 A K k s p1) = (term161 A K k s p1).
Proof. exact (MK_COMB (@lem4491154 K k p1) (@lem4491153 A K s p1)). Qed.
Lemma lem4491156 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : ((term185 A K k s p1) = (term186 A K k s p1)) = ((term139 A K k s p1) = (term161 A K k s p1)).
Proof. exact (MK_COMB (@lem4491149 A K k s p1) (@lem4491155 A K k s p1)). Qed.
Lemma lem4491157 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term139 A K k s p1) = (term161 A K k s p1).
Proof. exact (EQ_MP (@lem4491156 A K k s p1) (@lem4491141 A K k s p1)). Qed.
Lemma lem4491162 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term147 A K k s) = (term169 A K k s).
Proof. exact (fun_ext (fun p1 : K => @lem4491157 A K k s p1)). Qed.
Lemma lem4491163 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4491164 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term148 A K k s) = (term170 A K k s).
Proof. exact (MK_COMB (@lem4491163 K) (@lem4491162 A K k s)). Qed.
Lemma lem4491213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4491214 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term176 A K k s) = (term194 A K k s).
Proof. exact (MK_COMB (@lem4491213) (@lem4491164 A K k s)). Qed.
Lemma lem4491247 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term168 A K k s) = (term168 A K k s).
Proof. exact (eq_refl (term168 A K k s)). Qed.
Lemma lem4491248 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term178 A K k s) = (term195 A K k s).
Proof. exact (MK_COMB (@lem4491214 A K k s) (@lem4491247 A K k s)). Qed.
Lemma lem4491249 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4491250 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term180 A K k s) = (term196 A K k s).
Proof. exact (MK_COMB (@lem4491249) (@lem4491248 A K k s)). Qed.
Lemma lem4491256 {A : Type'} (P : Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem4491257 {A : Type'} (P : Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (@lem4491256 A P Q). Qed.
Lemma lem4491258 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term199 A K k s p1) = (term200 A K k s p1).
Proof. exact (@lem4491257 A (k p1) (term155 A K s p1)). Qed.
Lemma lem4491259 {A K : Type'} (s : type1470 A K) (p1 : K) (p2 : A) : (term201 A K s p1 p2) = (s p1 p2).
Proof. exact (eq_refl (term201 A K s p1 p2)). Qed.
Lemma lem4491260 {K : Type'} (k : K -> Prop) (p1 : K) : (term98 K k p1) = (term98 K k p1).
Proof. exact (eq_refl (term98 K k p1)). Qed.
Lemma lem4491261 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term202 A K k s p1 p2) = (term99 A K k s p1 p2).
Proof. exact (MK_COMB (@lem4491260 K k p1) (@lem4491259 A K s p1 p2)). Qed.
Lemma lem4491262 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term203 A K k s p1) = (term136 A K k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4491261 A K k s p1 p2)). Qed.
Lemma lem4491263 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4491264 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term199 A K k s p1) = (term137 A K k s p1).
Proof. exact (MK_COMB (@lem4491263 A) (@lem4491262 A K k s p1)). Qed.
Lemma lem4491265 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4491266 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term204 A K k s p1) = (term205 A K k s p1).
Proof. exact (MK_COMB (@lem4491265) (@lem4491264 A K k s p1)). Qed.
Lemma lem4491267 {A K : Type'} (s : type1470 A K) (p1 : K) (p2 : A) : (term201 A K s p1 p2) = (s p1 p2).
Proof. exact (eq_refl (term201 A K s p1 p2)). Qed.
Lemma lem4491268 {A K : Type'} (s : type1470 A K) (p1 : K) : (term206 A K s p1) = (term155 A K s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4491267 A K s p1 p2)). Qed.
Lemma lem4491269 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4491270 {A K : Type'} (s : type1470 A K) (p1 : K) : (term207 A K s p1) = (term156 A K s p1).
Proof. exact (MK_COMB (@lem4491269 A) (@lem4491268 A K s p1)). Qed.
Lemma lem4491271 {K : Type'} (k : K -> Prop) (p1 : K) : (term98 K k p1) = (term98 K k p1).
Proof. exact (eq_refl (term98 K k p1)). Qed.
Lemma lem4491272 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term200 A K k s p1) = (term158 A K k s p1).
Proof. exact (MK_COMB (@lem4491271 K k p1) (@lem4491270 A K s p1)). Qed.
Lemma lem4491273 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : ((term199 A K k s p1) = (term200 A K k s p1)) = ((term137 A K k s p1) = (term158 A K k s p1)).
Proof. exact (MK_COMB (@lem4491266 A K k s p1) (@lem4491272 A K k s p1)). Qed.
Lemma lem4491274 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term137 A K k s p1) = (term158 A K k s p1).
Proof. exact (EQ_MP (@lem4491273 A K k s p1) (@lem4491258 A K k s p1)). Qed.
Lemma lem4491279 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term145 A K k s) = (term167 A K k s).
Proof. exact (fun_ext (fun p1 : K => @lem4491274 A K k s p1)). Qed.
Lemma lem4491280 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4491281 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term146 A K k s) = (term168 A K k s).
Proof. exact (MK_COMB (@lem4491280 K) (@lem4491279 A K k s)). Qed.
Lemma lem4491310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4491311 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term172 A K k s) = (term208 A K k s).
Proof. exact (MK_COMB (@lem4491310) (@lem4491281 A K k s)). Qed.
Lemma lem4491364 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term170 A K k s) = (term170 A K k s).
Proof. exact (eq_refl (term170 A K k s)). Qed.
Lemma lem4491365 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term174 A K k s) = (term209 A K k s).
Proof. exact (MK_COMB (@lem4491311 A K k s) (@lem4491364 A K k s)). Qed.
Lemma lem4491366 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term182 A K k s) = (term210 A K k s).
Proof. exact (MK_COMB (@lem4491250 A K k s) (@lem4491365 A K k s)). Qed.
Lemma lem4491368 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term197 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4491369 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term197 A P Q).
Proof. exact (@lem4491368 A P Q). Qed.
Lemma lem4491370 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term200 A K k s i) = (term199 A K k s i).
Proof. exact (@lem4491369 A (k i) (term155 A K s i)). Qed.
Lemma lem4491371 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term201 A K s i x) = (s i x).
Proof. exact (eq_refl (term201 A K s i x)). Qed.
Lemma lem4491372 {A K : Type'} (s : type1470 A K) (i : K) : (term206 A K s i) = (term155 A K s i).
Proof. exact (fun_ext (fun x : A => @lem4491371 A K s i x)). Qed.
Lemma lem4491373 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4491374 {A K : Type'} (s : type1470 A K) (i : K) : (term207 A K s i) = (term156 A K s i).
Proof. exact (MK_COMB (@lem4491373 A) (@lem4491372 A K s i)). Qed.
Lemma lem4491375 {K : Type'} (k : K -> Prop) (i : K) : (term98 K k i) = (term98 K k i).
Proof. exact (eq_refl (term98 K k i)). Qed.
Lemma lem4491376 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term200 A K k s i) = (term158 A K k s i).
Proof. exact (MK_COMB (@lem4491375 K k i) (@lem4491374 A K s i)). Qed.
Lemma lem4491377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4491378 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term211 A K k s i) = (term212 A K k s i).
Proof. exact (MK_COMB (@lem4491377) (@lem4491376 A K k s i)). Qed.
Lemma lem4491379 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term201 A K s i x) = (s i x).
Proof. exact (eq_refl (term201 A K s i x)). Qed.
Lemma lem4491380 {K : Type'} (k : K -> Prop) (i : K) : (term98 K k i) = (term98 K k i).
Proof. exact (eq_refl (term98 K k i)). Qed.
Lemma lem4491381 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term202 A K k s i x) = (term99 A K k s i x).
Proof. exact (MK_COMB (@lem4491380 K k i) (@lem4491379 A K s i x)). Qed.
Lemma lem4491382 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term203 A K k s i) = (term136 A K k s i).
Proof. exact (fun_ext (fun x : A => @lem4491381 A K k s i x)). Qed.
Lemma lem4491383 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4491384 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term199 A K k s i) = (term137 A K k s i).
Proof. exact (MK_COMB (@lem4491383 A) (@lem4491382 A K k s i)). Qed.
Lemma lem4491385 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : ((term200 A K k s i) = (term199 A K k s i)) = ((term158 A K k s i) = (term137 A K k s i)).
Proof. exact (MK_COMB (@lem4491378 A K k s i) (@lem4491384 A K k s i)). Qed.
Lemma lem4491386 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term158 A K k s i) = (term137 A K k s i).
Proof. exact (EQ_MP (@lem4491385 A K k s i) (@lem4491370 A K k s i)). Qed.
Lemma lem4491387 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term167 A K k s) = (term145 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4491386 A K k s i)). Qed.
Lemma lem4491388 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4491389 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term168 A K k s) = (term146 A K k s).
Proof. exact (MK_COMB (@lem4491388 K) (@lem4491387 A K k s)). Qed.
Lemma lem4491390 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term194 A K k s) = (term194 A K k s).
Proof. exact (eq_refl (term194 A K k s)). Qed.
Lemma lem4491391 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term195 A K k s) = (term213 A K k s).
Proof. exact (MK_COMB (@lem4491390 A K k s) (@lem4491389 A K k s)). Qed.
Lemma lem4491393 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term197 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4491394 {K : Type'} (P : Prop) (Q : K -> Prop) : (term198 K P Q) = (term197 K P Q).
Proof. exact (@lem4491393 K P Q). Qed.
Lemma lem4491395 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term214 A K k s) = (term215 A K k s).
Proof. exact (@lem4491394 K (term170 A K k s) (term145 A K k s)). Qed.
Lemma lem4491396 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term216 A K k s i) = (term137 A K k s i).
Proof. exact (eq_refl (term216 A K k s i)). Qed.
Lemma lem4491397 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term217 A K k s) = (term145 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4491396 A K k s i)). Qed.
Lemma lem4491398 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4491399 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term218 A K k s) = (term146 A K k s).
Proof. exact (MK_COMB (@lem4491398 K) (@lem4491397 A K k s)). Qed.
Lemma lem4491400 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term194 A K k s) = (term194 A K k s).
Proof. exact (eq_refl (term194 A K k s)). Qed.
Lemma lem4491401 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term214 A K k s) = (term213 A K k s).
Proof. exact (MK_COMB (@lem4491400 A K k s) (@lem4491399 A K k s)). Qed.
Lemma lem4491402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4491403 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term219 A K k s) = (term220 A K k s).
Proof. exact (MK_COMB (@lem4491402) (@lem4491401 A K k s)). Qed.
Lemma lem4491404 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term216 A K k s i) = (term137 A K k s i).
Proof. exact (eq_refl (term216 A K k s i)). Qed.
Lemma lem4491405 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term194 A K k s) = (term194 A K k s).
Proof. exact (eq_refl (term194 A K k s)). Qed.
Lemma lem4491406 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term221 A K k s i) = (term222 A K k s i).
Proof. exact (MK_COMB (@lem4491405 A K k s) (@lem4491404 A K k s i)). Qed.
Lemma lem4491407 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term223 A K k s) = (term224 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4491406 A K k s i)). Qed.
Lemma lem4491408 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4491409 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term215 A K k s) = (term225 A K k s).
Proof. exact (MK_COMB (@lem4491408 K) (@lem4491407 A K k s)). Qed.
Lemma lem4491410 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term214 A K k s) = (term215 A K k s)) = ((term213 A K k s) = (term225 A K k s)).
Proof. exact (MK_COMB (@lem4491403 A K k s) (@lem4491409 A K k s)). Qed.
Lemma lem4491411 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term213 A K k s) = (term225 A K k s).
Proof. exact (EQ_MP (@lem4491410 A K k s) (@lem4491395 A K k s)). Qed.
Lemma lem4491413 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term197 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4491414 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term197 A P Q).
Proof. exact (@lem4491413 A P Q). Qed.
Lemma lem4491415 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term226 A K k s i) = (term227 A K k s i).
Proof. exact (@lem4491414 A (term170 A K k s) (term136 A K k s i)). Qed.
Lemma lem4491416 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term228 A K k s i x) = (term99 A K k s i x).
Proof. exact (eq_refl (term228 A K k s i x)). Qed.
Lemma lem4491417 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term229 A K k s i) = (term136 A K k s i).
Proof. exact (fun_ext (fun x : A => @lem4491416 A K k s i x)). Qed.
Lemma lem4491418 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4491419 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term230 A K k s i) = (term137 A K k s i).
Proof. exact (MK_COMB (@lem4491418 A) (@lem4491417 A K k s i)). Qed.
Lemma lem4491420 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term194 A K k s) = (term194 A K k s).
Proof. exact (eq_refl (term194 A K k s)). Qed.
Lemma lem4491421 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term226 A K k s i) = (term222 A K k s i).
Proof. exact (MK_COMB (@lem4491420 A K k s) (@lem4491419 A K k s i)). Qed.
Lemma lem4491422 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4491423 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term231 A K k s i) = (term232 A K k s i).
Proof. exact (MK_COMB (@lem4491422) (@lem4491421 A K k s i)). Qed.
Lemma lem4491424 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term228 A K k s i x) = (term99 A K k s i x).
Proof. exact (eq_refl (term228 A K k s i x)). Qed.
Lemma lem4491425 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term194 A K k s) = (term194 A K k s).
Proof. exact (eq_refl (term194 A K k s)). Qed.
Lemma lem4491426 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term233 A K k s i x) = (term234 A K k s i x).
Proof. exact (MK_COMB (@lem4491425 A K k s) (@lem4491424 A K k s i x)). Qed.
Lemma lem4491427 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term235 A K k s i) = (term236 A K k s i).
Proof. exact (fun_ext (fun x : A => @lem4491426 A K k s i x)). Qed.
Lemma lem4491428 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4491429 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term227 A K k s i) = (term237 A K k s i).
Proof. exact (MK_COMB (@lem4491428 A) (@lem4491427 A K k s i)). Qed.
Lemma lem4491430 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : ((term226 A K k s i) = (term227 A K k s i)) = ((term222 A K k s i) = (term237 A K k s i)).
Proof. exact (MK_COMB (@lem4491423 A K k s i) (@lem4491429 A K k s i)). Qed.
Lemma lem4491431 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term222 A K k s i) = (term237 A K k s i).
Proof. exact (EQ_MP (@lem4491430 A K k s i) (@lem4491415 A K k s i)). Qed.
Lemma lem4491432 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term224 A K k s) = (term238 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4491431 A K k s i)). Qed.
Lemma lem4491433 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4491434 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term225 A K k s) = (term239 A K k s).
Proof. exact (MK_COMB (@lem4491433 K) (@lem4491432 A K k s)). Qed.
Lemma lem4491435 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term213 A K k s) = (term239 A K k s).
Proof. exact (TRANS (@lem4491411 A K k s) (@lem4491434 A K k s)). Qed.
Lemma lem4491436 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term195 A K k s) = (term239 A K k s).
Proof. exact (TRANS (@lem4491391 A K k s) (@lem4491435 A K k s)). Qed.
Lemma lem4491437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4491438 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term196 A K k s) = (term240 A K k s).
Proof. exact (MK_COMB (@lem4491437) (@lem4491436 A K k s)). Qed.
Lemma lem4491440 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term197 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4491441 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term197 A P Q).
Proof. exact (@lem4491440 A P Q). Qed.
Lemma lem4491442 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term200 A K k s p1) = (term199 A K k s p1).
Proof. exact (@lem4491441 A (k p1) (term155 A K s p1)). Qed.
Lemma lem4491443 {A K : Type'} (s : type1470 A K) (p1 : K) (p2 : A) : (term201 A K s p1 p2) = (s p1 p2).
Proof. exact (eq_refl (term201 A K s p1 p2)). Qed.
Lemma lem4491444 {A K : Type'} (s : type1470 A K) (p1 : K) : (term206 A K s p1) = (term155 A K s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4491443 A K s p1 p2)). Qed.
Lemma lem4491445 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4491446 {A K : Type'} (s : type1470 A K) (p1 : K) : (term207 A K s p1) = (term156 A K s p1).
Proof. exact (MK_COMB (@lem4491445 A) (@lem4491444 A K s p1)). Qed.
Lemma lem4491447 {K : Type'} (k : K -> Prop) (p1 : K) : (term98 K k p1) = (term98 K k p1).
Proof. exact (eq_refl (term98 K k p1)). Qed.
Lemma lem4491448 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term200 A K k s p1) = (term158 A K k s p1).
Proof. exact (MK_COMB (@lem4491447 K k p1) (@lem4491446 A K s p1)). Qed.
Lemma lem4491449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4491450 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term211 A K k s p1) = (term212 A K k s p1).
Proof. exact (MK_COMB (@lem4491449) (@lem4491448 A K k s p1)). Qed.
Lemma lem4491451 {A K : Type'} (s : type1470 A K) (p1 : K) (p2 : A) : (term201 A K s p1 p2) = (s p1 p2).
Proof. exact (eq_refl (term201 A K s p1 p2)). Qed.
Lemma lem4491452 {K : Type'} (k : K -> Prop) (p1 : K) : (term98 K k p1) = (term98 K k p1).
Proof. exact (eq_refl (term98 K k p1)). Qed.
Lemma lem4491453 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term202 A K k s p1 p2) = (term99 A K k s p1 p2).
Proof. exact (MK_COMB (@lem4491452 K k p1) (@lem4491451 A K s p1 p2)). Qed.
Lemma lem4491454 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term203 A K k s p1) = (term136 A K k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4491453 A K k s p1 p2)). Qed.
Lemma lem4491455 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4491456 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term199 A K k s p1) = (term137 A K k s p1).
Proof. exact (MK_COMB (@lem4491455 A) (@lem4491454 A K k s p1)). Qed.
Lemma lem4491457 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : ((term200 A K k s p1) = (term199 A K k s p1)) = ((term158 A K k s p1) = (term137 A K k s p1)).
Proof. exact (MK_COMB (@lem4491450 A K k s p1) (@lem4491456 A K k s p1)). Qed.
Lemma lem4491458 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term158 A K k s p1) = (term137 A K k s p1).
Proof. exact (EQ_MP (@lem4491457 A K k s p1) (@lem4491442 A K k s p1)). Qed.
Lemma lem4491459 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term167 A K k s) = (term145 A K k s).
Proof. exact (fun_ext (fun p1 : K => @lem4491458 A K k s p1)). Qed.
Lemma lem4491460 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4491461 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term168 A K k s) = (term146 A K k s).
Proof. exact (MK_COMB (@lem4491460 K) (@lem4491459 A K k s)). Qed.
Lemma lem4491462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4491463 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term208 A K k s) = (term172 A K k s).
Proof. exact (MK_COMB (@lem4491462) (@lem4491461 A K k s)). Qed.
Lemma lem4491464 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term170 A K k s) = (term170 A K k s).
Proof. exact (eq_refl (term170 A K k s)). Qed.
Lemma lem4491465 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term209 A K k s) = (term174 A K k s).
Proof. exact (MK_COMB (@lem4491463 A K k s) (@lem4491464 A K k s)). Qed.
Lemma lem4491467 {A : Type'} (P : A -> Prop) (Q : Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4491468 {K : Type'} (P : K -> Prop) (Q : Prop) : (term241 K P Q) = (term242 K P Q).
Proof. exact (@lem4491467 K P Q). Qed.
Lemma lem4491469 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term243 A K k s) = (term244 A K k s).
Proof. exact (@lem4491468 K (term145 A K k s) (term170 A K k s)). Qed.
Lemma lem4491470 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term216 A K k s p1) = (term137 A K k s p1).
Proof. exact (eq_refl (term216 A K k s p1)). Qed.
Lemma lem4491471 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term217 A K k s) = (term145 A K k s).
Proof. exact (fun_ext (fun p1 : K => @lem4491470 A K k s p1)). Qed.
Lemma lem4491472 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4491473 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term218 A K k s) = (term146 A K k s).
Proof. exact (MK_COMB (@lem4491472 K) (@lem4491471 A K k s)). Qed.
Lemma lem4491474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4491475 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term245 A K k s) = (term172 A K k s).
Proof. exact (MK_COMB (@lem4491474) (@lem4491473 A K k s)). Qed.
Lemma lem4491476 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term170 A K k s) = (term170 A K k s).
Proof. exact (eq_refl (term170 A K k s)). Qed.
Lemma lem4491477 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term243 A K k s) = (term174 A K k s).
Proof. exact (MK_COMB (@lem4491475 A K k s) (@lem4491476 A K k s)). Qed.
Lemma lem4491478 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4491479 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term246 A K k s) = (term247 A K k s).
Proof. exact (MK_COMB (@lem4491478) (@lem4491477 A K k s)). Qed.
Lemma lem4491480 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term216 A K k s p1) = (term137 A K k s p1).
Proof. exact (eq_refl (term216 A K k s p1)). Qed.
Lemma lem4491481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4491482 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term248 A K k s p1) = (term249 A K k s p1).
Proof. exact (MK_COMB (@lem4491481) (@lem4491480 A K k s p1)). Qed.
Lemma lem4491483 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term170 A K k s) = (term170 A K k s).
Proof. exact (eq_refl (term170 A K k s)). Qed.
Lemma lem4491484 {A K : Type'} (p1 : K) (k : K -> Prop) (s : type1470 A K) : (term250 A K p1 k s) = (term251 A K p1 k s).
Proof. exact (MK_COMB (@lem4491482 A K k s p1) (@lem4491483 A K k s)). Qed.
Lemma lem4491485 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term252 A K k s) = (term253 A K k s).
Proof. exact (fun_ext (fun p1 : K => @lem4491484 A K p1 k s)). Qed.
Lemma lem4491486 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4491487 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term244 A K k s) = (term254 A K k s).
Proof. exact (MK_COMB (@lem4491486 K) (@lem4491485 A K k s)). Qed.
Lemma lem4491488 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term243 A K k s) = (term244 A K k s)) = ((term174 A K k s) = (term254 A K k s)).
Proof. exact (MK_COMB (@lem4491479 A K k s) (@lem4491487 A K k s)). Qed.
Lemma lem4491489 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term174 A K k s) = (term254 A K k s).
Proof. exact (EQ_MP (@lem4491488 A K k s) (@lem4491469 A K k s)). Qed.
Lemma lem4491491 {A : Type'} (P : A -> Prop) (Q : Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4491492 {A : Type'} (P : A -> Prop) (Q : Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (@lem4491491 A P Q). Qed.
Lemma lem4491493 {A K : Type'} (p1 : K) (k : K -> Prop) (s : type1470 A K) : (term255 A K p1 k s) = (term256 A K p1 k s).
Proof. exact (@lem4491492 A (term136 A K k s p1) (term170 A K k s)). Qed.
Lemma lem4491494 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term228 A K k s p1 p2) = (term99 A K k s p1 p2).
Proof. exact (eq_refl (term228 A K k s p1 p2)). Qed.
Lemma lem4491495 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term229 A K k s p1) = (term136 A K k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4491494 A K k s p1 p2)). Qed.
Lemma lem4491496 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4491497 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term230 A K k s p1) = (term137 A K k s p1).
Proof. exact (MK_COMB (@lem4491496 A) (@lem4491495 A K k s p1)). Qed.
Lemma lem4491498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4491499 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term257 A K k s p1) = (term249 A K k s p1).
Proof. exact (MK_COMB (@lem4491498) (@lem4491497 A K k s p1)). Qed.
Lemma lem4491500 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term170 A K k s) = (term170 A K k s).
Proof. exact (eq_refl (term170 A K k s)). Qed.
Lemma lem4491501 {A K : Type'} (p1 : K) (k : K -> Prop) (s : type1470 A K) : (term255 A K p1 k s) = (term251 A K p1 k s).
Proof. exact (MK_COMB (@lem4491499 A K k s p1) (@lem4491500 A K k s)). Qed.
Lemma lem4491502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4491503 {A K : Type'} (p1 : K) (k : K -> Prop) (s : type1470 A K) : (term258 A K p1 k s) = (term259 A K p1 k s).
Proof. exact (MK_COMB (@lem4491502) (@lem4491501 A K p1 k s)). Qed.
Lemma lem4491504 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term228 A K k s p1 p2) = (term99 A K k s p1 p2).
Proof. exact (eq_refl (term228 A K k s p1 p2)). Qed.
Lemma lem4491505 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4491506 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term260 A K k s p1 p2) = (term261 A K k s p1 p2).
Proof. exact (MK_COMB (@lem4491505) (@lem4491504 A K k s p1 p2)). Qed.
Lemma lem4491507 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term170 A K k s) = (term170 A K k s).
Proof. exact (eq_refl (term170 A K k s)). Qed.
Lemma lem4491508 {A K : Type'} (p1 : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) : (term262 A K p1 p2 k s) = (term263 A K p1 p2 k s).
Proof. exact (MK_COMB (@lem4491506 A K k s p1 p2) (@lem4491507 A K k s)). Qed.
Lemma lem4491509 {A K : Type'} (p1 : K) (k : K -> Prop) (s : type1470 A K) : (term264 A K p1 k s) = (term265 A K p1 k s).
Proof. exact (fun_ext (fun p2 : A => @lem4491508 A K p1 p2 k s)). Qed.
Lemma lem4491510 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4491511 {A K : Type'} (p1 : K) (k : K -> Prop) (s : type1470 A K) : (term256 A K p1 k s) = (term266 A K p1 k s).
Proof. exact (MK_COMB (@lem4491510 A) (@lem4491509 A K p1 k s)). Qed.
Lemma lem4491512 {A K : Type'} (p1 : K) (k : K -> Prop) (s : type1470 A K) : ((term255 A K p1 k s) = (term256 A K p1 k s)) = ((term251 A K p1 k s) = (term266 A K p1 k s)).
Proof. exact (MK_COMB (@lem4491503 A K p1 k s) (@lem4491511 A K p1 k s)). Qed.
Lemma lem4491513 {A K : Type'} (p1 : K) (k : K -> Prop) (s : type1470 A K) : (term251 A K p1 k s) = (term266 A K p1 k s).
Proof. exact (EQ_MP (@lem4491512 A K p1 k s) (@lem4491493 A K p1 k s)). Qed.
Lemma lem4491514 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term253 A K k s) = (term267 A K k s).
Proof. exact (fun_ext (fun p1 : K => @lem4491513 A K p1 k s)). Qed.
Lemma lem4491515 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4491516 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term254 A K k s) = (term268 A K k s).
Proof. exact (MK_COMB (@lem4491515 K) (@lem4491514 A K k s)). Qed.
Lemma lem4491517 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term174 A K k s) = (term268 A K k s).
Proof. exact (TRANS (@lem4491489 A K k s) (@lem4491516 A K k s)). Qed.
Lemma lem4491518 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term209 A K k s) = (term268 A K k s).
Proof. exact (TRANS (@lem4491465 A K k s) (@lem4491517 A K k s)). Qed.
Lemma lem4491519 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term210 A K k s) = (term269 A K k s).
Proof. exact (MK_COMB (@lem4491438 A K k s) (@lem4491518 A K k s)). Qed.
Lemma lem4491521 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4491522 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term270 K P Q) = (term271 K P Q).
Proof. exact (@lem4491521 K P Q). Qed.
Lemma lem4491523 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term272 A K k s) = (term273 A K k s).
Proof. exact (@lem4491522 K (term238 A K k s) (term267 A K k s)). Qed.
Lemma lem4491524 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term274 A K k s i) = (term237 A K k s i).
Proof. exact (eq_refl (term274 A K k s i)). Qed.
Lemma lem4491525 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term275 A K k s) = (term238 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4491524 A K k s i)). Qed.
Lemma lem4491526 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4491527 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term276 A K k s) = (term239 A K k s).
Proof. exact (MK_COMB (@lem4491526 K) (@lem4491525 A K k s)). Qed.
Lemma lem4491528 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4491529 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term277 A K k s) = (term240 A K k s).
Proof. exact (MK_COMB (@lem4491528) (@lem4491527 A K k s)). Qed.
Lemma lem4491530 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term278 A K k s i) = (term266 A K i k s).
Proof. exact (eq_refl (term278 A K k s i)). Qed.
Lemma lem4491531 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term279 A K k s) = (term267 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4491530 A K i k s)). Qed.
Lemma lem4491532 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4491533 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term280 A K k s) = (term268 A K k s).
Proof. exact (MK_COMB (@lem4491532 K) (@lem4491531 A K k s)). Qed.
Lemma lem4491534 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term272 A K k s) = (term269 A K k s).
Proof. exact (MK_COMB (@lem4491529 A K k s) (@lem4491533 A K k s)). Qed.
Lemma lem4491535 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4491536 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term281 A K k s) = (term282 A K k s).
Proof. exact (MK_COMB (@lem4491535) (@lem4491534 A K k s)). Qed.
Lemma lem4491537 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term274 A K k s i) = (term237 A K k s i).
Proof. exact (eq_refl (term274 A K k s i)). Qed.
Lemma lem4491538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4491539 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term283 A K k s i) = (term284 A K k s i).
Proof. exact (MK_COMB (@lem4491538) (@lem4491537 A K k s i)). Qed.
Lemma lem4491540 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term278 A K k s i) = (term266 A K i k s).
Proof. exact (eq_refl (term278 A K k s i)). Qed.
Lemma lem4491541 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term285 A K k s i) = (term286 A K i k s).
Proof. exact (MK_COMB (@lem4491539 A K k s i) (@lem4491540 A K i k s)). Qed.
Lemma lem4491542 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term287 A K k s) = (term288 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4491541 A K i k s)). Qed.
Lemma lem4491543 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4491544 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term273 A K k s) = (term289 A K k s).
Proof. exact (MK_COMB (@lem4491543 K) (@lem4491542 A K k s)). Qed.
Lemma lem4491545 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term272 A K k s) = (term273 A K k s)) = ((term269 A K k s) = (term289 A K k s)).
Proof. exact (MK_COMB (@lem4491536 A K k s) (@lem4491544 A K k s)). Qed.
Lemma lem4491546 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term269 A K k s) = (term289 A K k s).
Proof. exact (EQ_MP (@lem4491545 A K k s) (@lem4491523 A K k s)). Qed.
Lemma lem4491549 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term290 A K k s) = (term290 A K k s).
Proof. exact (eq_refl (term290 A K k s)). Qed.
Lemma lem4491550 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term290 A K k s) = ((term269 A K k s) = (term289 A K k s)).
Proof. exact (eq_refl (term290 A K k s)). Qed.
Lemma lem4491551 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term291 A K k s) = (term291 A K k s).
Proof. exact (eq_refl (term291 A K k s)). Qed.
Lemma lem4491552 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term290 A K k s) = (term290 A K k s)) = ((term290 A K k s) = ((term269 A K k s) = (term289 A K k s))).
Proof. exact (MK_COMB (@lem4491551 A K k s) (@lem4491550 A K k s)). Qed.
Lemma lem4491553 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term290 A K k s) = ((term269 A K k s) = (term289 A K k s)).
Proof. exact (eq_refl (term290 A K k s)). Qed.
Lemma lem4491554 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4491555 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term291 A K k s) = (term292 A K k s).
Proof. exact (MK_COMB (@lem4491554) (@lem4491553 A K k s)). Qed.
Lemma lem4491556 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term269 A K k s) = (term289 A K k s)) = ((term269 A K k s) = (term289 A K k s)).
Proof. exact (eq_refl ((term269 A K k s) = (term289 A K k s))). Qed.
Lemma lem4491557 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term290 A K k s) = ((term269 A K k s) = (term289 A K k s))) = (((term269 A K k s) = (term289 A K k s)) = ((term269 A K k s) = (term289 A K k s))).
Proof. exact (MK_COMB (@lem4491555 A K k s) (@lem4491556 A K k s)). Qed.
Lemma lem4491558 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term290 A K k s) = (term290 A K k s)) = (((term269 A K k s) = (term289 A K k s)) = ((term269 A K k s) = (term289 A K k s))).
Proof. exact (TRANS (@lem4491552 A K k s) (@lem4491557 A K k s)). Qed.
Lemma lem4491559 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term269 A K k s) = (term289 A K k s)) = ((term269 A K k s) = (term289 A K k s)).
Proof. exact (EQ_MP (@lem4491558 A K k s) (@lem4491549 A K k s)). Qed.
Lemma lem4491560 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term269 A K k s) = (term289 A K k s).
Proof. exact (EQ_MP (@lem4491559 A K k s) (@lem4491546 A K k s)). Qed.
Lemma lem4491562 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4491563 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (@lem4491562 A P Q). Qed.
Lemma lem4491564 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term293 A K i k s) = (term294 A K i k s).
Proof. exact (@lem4491563 A (term236 A K k s i) (term265 A K i k s)). Qed.
Lemma lem4491565 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) : (term295 A K k s i p2) = (term234 A K k s i p2).
Proof. exact (eq_refl (term295 A K k s i p2)). Qed.
Lemma lem4491566 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term296 A K k s i) = (term236 A K k s i).
Proof. exact (fun_ext (fun p2 : A => @lem4491565 A K k s i p2)). Qed.
Lemma lem4491567 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4491568 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term297 A K k s i) = (term237 A K k s i).
Proof. exact (MK_COMB (@lem4491567 A) (@lem4491566 A K k s i)). Qed.
Lemma lem4491569 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4491570 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term298 A K k s i) = (term284 A K k s i).
Proof. exact (MK_COMB (@lem4491569) (@lem4491568 A K k s i)). Qed.
Lemma lem4491571 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) : (term299 A K i k s p2) = (term263 A K i p2 k s).
Proof. exact (eq_refl (term299 A K i k s p2)). Qed.
Lemma lem4491572 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term300 A K i k s) = (term265 A K i k s).
Proof. exact (fun_ext (fun p2 : A => @lem4491571 A K i p2 k s)). Qed.
Lemma lem4491573 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4491574 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term301 A K i k s) = (term266 A K i k s).
Proof. exact (MK_COMB (@lem4491573 A) (@lem4491572 A K i k s)). Qed.
Lemma lem4491575 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term293 A K i k s) = (term286 A K i k s).
Proof. exact (MK_COMB (@lem4491570 A K k s i) (@lem4491574 A K i k s)). Qed.
Lemma lem4491576 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4491577 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term302 A K i k s) = (term303 A K i k s).
Proof. exact (MK_COMB (@lem4491576) (@lem4491575 A K i k s)). Qed.
Lemma lem4491578 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) : (term295 A K k s i p2) = (term234 A K k s i p2).
Proof. exact (eq_refl (term295 A K k s i p2)). Qed.
Lemma lem4491579 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4491580 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) : (term304 A K k s i p2) = (term305 A K k s i p2).
Proof. exact (MK_COMB (@lem4491579) (@lem4491578 A K k s i p2)). Qed.
Lemma lem4491581 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) : (term299 A K i k s p2) = (term263 A K i p2 k s).
Proof. exact (eq_refl (term299 A K i k s p2)). Qed.
Lemma lem4491582 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) : (term306 A K i k s p2) = (term307 A K i p2 k s).
Proof. exact (MK_COMB (@lem4491580 A K k s i p2) (@lem4491581 A K i p2 k s)). Qed.
Lemma lem4491583 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term308 A K i k s) = (term309 A K i k s).
Proof. exact (fun_ext (fun p2 : A => @lem4491582 A K i p2 k s)). Qed.
Lemma lem4491584 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4491585 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term294 A K i k s) = (term310 A K i k s).
Proof. exact (MK_COMB (@lem4491584 A) (@lem4491583 A K i k s)). Qed.
Lemma lem4491586 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : ((term293 A K i k s) = (term294 A K i k s)) = ((term286 A K i k s) = (term310 A K i k s)).
Proof. exact (MK_COMB (@lem4491577 A K i k s) (@lem4491585 A K i k s)). Qed.
Lemma lem4491587 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term286 A K i k s) = (term310 A K i k s).
Proof. exact (EQ_MP (@lem4491586 A K i k s) (@lem4491564 A K i k s)). Qed.
Lemma lem4491590 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term311 A K i k s) = (term311 A K i k s).
Proof. exact (eq_refl (term311 A K i k s)). Qed.
Lemma lem4491591 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term311 A K i k s) = ((term286 A K i k s) = (term310 A K i k s)).
Proof. exact (eq_refl (term311 A K i k s)). Qed.
Lemma lem4491592 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term312 A K i k s) = (term312 A K i k s).
Proof. exact (eq_refl (term312 A K i k s)). Qed.
Lemma lem4491593 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : ((term311 A K i k s) = (term311 A K i k s)) = ((term311 A K i k s) = ((term286 A K i k s) = (term310 A K i k s))).
Proof. exact (MK_COMB (@lem4491592 A K i k s) (@lem4491591 A K i k s)). Qed.
Lemma lem4491594 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term311 A K i k s) = ((term286 A K i k s) = (term310 A K i k s)).
Proof. exact (eq_refl (term311 A K i k s)). Qed.
Lemma lem4491595 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4491596 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term312 A K i k s) = (term313 A K i k s).
Proof. exact (MK_COMB (@lem4491595) (@lem4491594 A K i k s)). Qed.
Lemma lem4491597 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : ((term286 A K i k s) = (term310 A K i k s)) = ((term286 A K i k s) = (term310 A K i k s)).
Proof. exact (eq_refl ((term286 A K i k s) = (term310 A K i k s))). Qed.
Lemma lem4491598 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : ((term311 A K i k s) = ((term286 A K i k s) = (term310 A K i k s))) = (((term286 A K i k s) = (term310 A K i k s)) = ((term286 A K i k s) = (term310 A K i k s))).
Proof. exact (MK_COMB (@lem4491596 A K i k s) (@lem4491597 A K i k s)). Qed.
Lemma lem4491599 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : ((term311 A K i k s) = (term311 A K i k s)) = (((term286 A K i k s) = (term310 A K i k s)) = ((term286 A K i k s) = (term310 A K i k s))).
Proof. exact (TRANS (@lem4491593 A K i k s) (@lem4491598 A K i k s)). Qed.
Lemma lem4491600 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : ((term286 A K i k s) = (term310 A K i k s)) = ((term286 A K i k s) = (term310 A K i k s)).
Proof. exact (EQ_MP (@lem4491599 A K i k s) (@lem4491590 A K i k s)). Qed.
Lemma lem4491601 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term286 A K i k s) = (term310 A K i k s).
Proof. exact (EQ_MP (@lem4491600 A K i k s) (@lem4491587 A K i k s)). Qed.
Lemma lem4491602 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term288 A K k s) = (term314 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4491601 A K i k s)). Qed.
Lemma lem4491603 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4491604 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term289 A K k s) = (term315 A K k s).
Proof. exact (MK_COMB (@lem4491603 K) (@lem4491602 A K k s)). Qed.
Lemma lem4491605 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term269 A K k s) = (term315 A K k s).
Proof. exact (TRANS (@lem4491560 A K k s) (@lem4491604 A K k s)). Qed.
Lemma lem4491606 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term210 A K k s) = (term315 A K k s).
Proof. exact (TRANS (@lem4491519 A K k s) (@lem4491605 A K k s)). Qed.
Lemma lem4491607 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term182 A K k s) = (term315 A K k s).
Proof. exact (TRANS (@lem4491366 A K k s) (@lem4491606 A K k s)). Qed.
Lemma lem4491608 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term126 A K k s) = (term315 A K k s).
Proof. exact (TRANS (@lem4491133 A K k s) (@lem4491607 A K k s)). Qed.
Lemma lem4491609 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term126 A K k s) : term315 A K k s.
Proof. exact (EQ_MP (@lem4491608 A K k s) (@lem4491040 A K k s h1)). Qed.
Lemma lem4491610 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : term310 A K i k s) : term310 A K i k s.
Proof. exact (h1). Qed.
Lemma lem4491611 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term307 A K i p2 k s) : term307 A K i p2 k s.
Proof. exact (h1). Qed.
Lemma lem4491618 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term107 A K s i x) = (term107 A K s i x).
Proof. exact (eq_refl (term107 A K s i x)). Qed.
Lemma lem4491619 {A K : Type'} (s : type1470 A K) (i : K) : (term108 A K s i) = (term108 A K s i).
Proof. exact (fun_ext (fun x : A => @lem4491618 A K s i x)). Qed.
Lemma lem4491620 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4491621 {A K : Type'} (s : type1470 A K) (i : K) : (term109 A K s i) = (term109 A K s i).
Proof. exact (MK_COMB (@lem4491620 A) (@lem4491619 A K s i)). Qed.
Lemma lem4491628 {K : Type'} (k : K -> Prop) (i : K) : (term160 K k i) = (term160 K k i).
Proof. exact (eq_refl (term160 K k i)). Qed.
Lemma lem4491629 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term161 A K k s i) = (term161 A K k s i).
Proof. exact (MK_COMB (@lem4491628 K k i) (@lem4491621 A K s i)). Qed.
Lemma lem4491630 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term169 A K k s) = (term169 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4491629 A K k s i)). Qed.
Lemma lem4491631 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4491632 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term170 A K k s) = (term170 A K k s).
Proof. exact (MK_COMB (@lem4491631 K) (@lem4491630 A K k s)). Qed.
Lemma lem4491645 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) : (term261 A K k s i p2) = (term261 A K k s i p2).
Proof. exact (eq_refl (term261 A K k s i p2)). Qed.
Lemma lem4491646 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) : (term263 A K i p2 k s) = (term263 A K i p2 k s).
Proof. exact (MK_COMB (@lem4491645 A K k s i p2) (@lem4491632 A K k s)). Qed.
Lemma lem4491657 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) : (term99 A K k s i p2) = (term99 A K k s i p2).
Proof. exact (eq_refl (term99 A K k s i p2)). Qed.
Lemma lem4491664 {A K : Type'} (s : type1470 A K) (p1 : K) (p2 : A) : (term107 A K s p1 p2) = (term107 A K s p1 p2).
Proof. exact (eq_refl (term107 A K s p1 p2)). Qed.
Lemma lem4491665 {A K : Type'} (s : type1470 A K) (p1 : K) : (term108 A K s p1) = (term108 A K s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4491664 A K s p1 p2)). Qed.
Lemma lem4491666 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4491667 {A K : Type'} (s : type1470 A K) (p1 : K) : (term109 A K s p1) = (term109 A K s p1).
Proof. exact (MK_COMB (@lem4491666 A) (@lem4491665 A K s p1)). Qed.
Lemma lem4491674 {K : Type'} (k : K -> Prop) (p1 : K) : (term160 K k p1) = (term160 K k p1).
Proof. exact (eq_refl (term160 K k p1)). Qed.
Lemma lem4491675 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term161 A K k s p1) = (term161 A K k s p1).
Proof. exact (MK_COMB (@lem4491674 K k p1) (@lem4491667 A K s p1)). Qed.
Lemma lem4491676 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term169 A K k s) = (term169 A K k s).
Proof. exact (fun_ext (fun p1 : K => @lem4491675 A K k s p1)). Qed.
Lemma lem4491677 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4491678 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term170 A K k s) = (term170 A K k s).
Proof. exact (MK_COMB (@lem4491677 K) (@lem4491676 A K k s)). Qed.
Lemma lem4491679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4491680 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term194 A K k s) = (term194 A K k s).
Proof. exact (MK_COMB (@lem4491679) (@lem4491678 A K k s)). Qed.
Lemma lem4491681 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) : (term234 A K k s i p2) = (term234 A K k s i p2).
Proof. exact (MK_COMB (@lem4491680 A K k s) (@lem4491657 A K k s i p2)). Qed.
Lemma lem4491682 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4491683 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) : (term305 A K k s i p2) = (term305 A K k s i p2).
Proof. exact (MK_COMB (@lem4491682) (@lem4491681 A K k s i p2)). Qed.
Lemma lem4491684 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) : (term307 A K i p2 k s) = (term307 A K i p2 k s).
Proof. exact (MK_COMB (@lem4491683 A K k s i p2) (@lem4491646 A K i p2 k s)). Qed.
Lemma lem4491685 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term307 A K i p2 k s) : term307 A K i p2 k s.
Proof. exact (EQ_MP (@lem4491684 A K i p2 k s) (@lem4491611 A K i p2 k s h1)). Qed.
Lemma lem4491686 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : term234 A K k s i p2.
Proof. exact (h1). Qed.
Lemma lem4491687 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : term263 A K i p2 k s.
Proof. exact (h1). Qed.
Lemma lem4491688 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : term99 A K k s i p2.
Proof. exact (proj2 (@lem4491686 A K k s i p2 h1)). Qed.
Lemma lem4491689 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : term170 A K k s.
Proof. exact (proj1 (@lem4491686 A K k s i p2 h1)). Qed.
Lemma lem4491692 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : term170 A K k s.
Proof. exact (proj2 (@lem4491687 A K i p2 k s h1)). Qed.
Lemma lem4491693 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : term99 A K k s i p2.
Proof. exact (proj1 (@lem4491687 A K i p2 k s h1)). Qed.
Lemma lem4491697 {A : Type'} (P : Prop) (Q : A -> Prop) : (term184 A P Q) = (term183 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4491698 {A : Type'} (P : Prop) (Q : A -> Prop) : (term184 A P Q) = (term183 A P Q).
Proof. exact (@lem4491697 A P Q). Qed.
Lemma lem4491699 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term186 A K k s p1) = (term185 A K k s p1).
Proof. exact (@lem4491698 A (term187 K k p1) (term108 A K s p1)). Qed.
Lemma lem4491700 {A K : Type'} (s : type1470 A K) (p1 : K) (p2 : A) : (term152 A K s p1 p2) = (term107 A K s p1 p2).
Proof. exact (eq_refl (term152 A K s p1 p2)). Qed.
Lemma lem4491701 {A K : Type'} (s : type1470 A K) (p1 : K) : (term192 A K s p1) = (term108 A K s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4491700 A K s p1 p2)). Qed.
Lemma lem4491702 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4491703 {A K : Type'} (s : type1470 A K) (p1 : K) : (term193 A K s p1) = (term109 A K s p1).
Proof. exact (MK_COMB (@lem4491702 A) (@lem4491701 A K s p1)). Qed.
Lemma lem4491704 {K : Type'} (k : K -> Prop) (p1 : K) : (term160 K k p1) = (term160 K k p1).
Proof. exact (eq_refl (term160 K k p1)). Qed.
Lemma lem4491705 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term186 A K k s p1) = (term161 A K k s p1).
Proof. exact (MK_COMB (@lem4491704 K k p1) (@lem4491703 A K s p1)). Qed.
Lemma lem4491706 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4491707 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term316 A K k s p1) = (term317 A K k s p1).
Proof. exact (MK_COMB (@lem4491706) (@lem4491705 A K k s p1)). Qed.
Lemma lem4491708 {A K : Type'} (s : type1470 A K) (p1 : K) (p2 : A) : (term152 A K s p1 p2) = (term107 A K s p1 p2).
Proof. exact (eq_refl (term152 A K s p1 p2)). Qed.
Lemma lem4491709 {K : Type'} (k : K -> Prop) (p1 : K) : (term160 K k p1) = (term160 K k p1).
Proof. exact (eq_refl (term160 K k p1)). Qed.
Lemma lem4491710 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term188 A K k s p1 p2) = (term127 A K k s p1 p2).
Proof. exact (MK_COMB (@lem4491709 K k p1) (@lem4491708 A K s p1 p2)). Qed.
Lemma lem4491711 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term189 A K k s p1) = (term138 A K k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4491710 A K k s p1 p2)). Qed.
Lemma lem4491712 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4491713 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term185 A K k s p1) = (term139 A K k s p1).
Proof. exact (MK_COMB (@lem4491712 A) (@lem4491711 A K k s p1)). Qed.
Lemma lem4491714 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : ((term186 A K k s p1) = (term185 A K k s p1)) = ((term161 A K k s p1) = (term139 A K k s p1)).
Proof. exact (MK_COMB (@lem4491707 A K k s p1) (@lem4491713 A K k s p1)). Qed.
Lemma lem4491715 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term161 A K k s p1) = (term139 A K k s p1).
Proof. exact (EQ_MP (@lem4491714 A K k s p1) (@lem4491699 A K k s p1)). Qed.
Lemma lem4491716 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term169 A K k s) = (term147 A K k s).
Proof. exact (fun_ext (fun p1 : K => @lem4491715 A K k s p1)). Qed.
Lemma lem4491717 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4491718 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term170 A K k s) = (term148 A K k s).
Proof. exact (MK_COMB (@lem4491717 K) (@lem4491716 A K k s)). Qed.
Lemma lem4491725 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term127 A K k s p1 p2) = (term127 A K k s p1 p2).
Proof. exact (eq_refl (term127 A K k s p1 p2)). Qed.
Lemma lem4491726 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term138 A K k s p1) = (term138 A K k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4491725 A K k s p1 p2)). Qed.
Lemma lem4491727 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4491728 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term139 A K k s p1) = (term139 A K k s p1).
Proof. exact (MK_COMB (@lem4491727 A) (@lem4491726 A K k s p1)). Qed.
Lemma lem4491729 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term147 A K k s) = (term147 A K k s).
Proof. exact (fun_ext (fun p1 : K => @lem4491728 A K k s p1)). Qed.
Lemma lem4491730 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4491731 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term148 A K k s) = (term148 A K k s).
Proof. exact (MK_COMB (@lem4491730 K) (@lem4491729 A K k s)). Qed.
Lemma lem4491732 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term170 A K k s) = (term148 A K k s).
Proof. exact (TRANS (@lem4491718 A K k s) (@lem4491731 A K k s)). Qed.
Lemma lem4491733 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : term148 A K k s.
Proof. exact (EQ_MP (@lem4491732 A K k s) (@lem4491689 A K k s i p2 h1)). Qed.
Lemma lem4491743 {A : Type'} (P : Prop) (Q : A -> Prop) : (term184 A P Q) = (term183 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4491744 {A : Type'} (P : Prop) (Q : A -> Prop) : (term184 A P Q) = (term183 A P Q).
Proof. exact (@lem4491743 A P Q). Qed.
Lemma lem4491745 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term186 A K k s i) = (term185 A K k s i).
Proof. exact (@lem4491744 A (term187 K k i) (term108 A K s i)). Qed.
Lemma lem4491746 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term152 A K s i x) = (term107 A K s i x).
Proof. exact (eq_refl (term152 A K s i x)). Qed.
Lemma lem4491747 {A K : Type'} (s : type1470 A K) (i : K) : (term192 A K s i) = (term108 A K s i).
Proof. exact (fun_ext (fun x : A => @lem4491746 A K s i x)). Qed.
Lemma lem4491748 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4491749 {A K : Type'} (s : type1470 A K) (i : K) : (term193 A K s i) = (term109 A K s i).
Proof. exact (MK_COMB (@lem4491748 A) (@lem4491747 A K s i)). Qed.
Lemma lem4491750 {K : Type'} (k : K -> Prop) (i : K) : (term160 K k i) = (term160 K k i).
Proof. exact (eq_refl (term160 K k i)). Qed.
Lemma lem4491751 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term186 A K k s i) = (term161 A K k s i).
Proof. exact (MK_COMB (@lem4491750 K k i) (@lem4491749 A K s i)). Qed.
Lemma lem4491752 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4491753 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term316 A K k s i) = (term317 A K k s i).
Proof. exact (MK_COMB (@lem4491752) (@lem4491751 A K k s i)). Qed.
Lemma lem4491754 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term152 A K s i x) = (term107 A K s i x).
Proof. exact (eq_refl (term152 A K s i x)). Qed.
Lemma lem4491755 {K : Type'} (k : K -> Prop) (i : K) : (term160 K k i) = (term160 K k i).
Proof. exact (eq_refl (term160 K k i)). Qed.
Lemma lem4491756 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term188 A K k s i x) = (term127 A K k s i x).
Proof. exact (MK_COMB (@lem4491755 K k i) (@lem4491754 A K s i x)). Qed.
Lemma lem4491757 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term189 A K k s i) = (term138 A K k s i).
Proof. exact (fun_ext (fun x : A => @lem4491756 A K k s i x)). Qed.
Lemma lem4491758 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4491759 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term185 A K k s i) = (term139 A K k s i).
Proof. exact (MK_COMB (@lem4491758 A) (@lem4491757 A K k s i)). Qed.
Lemma lem4491760 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : ((term186 A K k s i) = (term185 A K k s i)) = ((term161 A K k s i) = (term139 A K k s i)).
Proof. exact (MK_COMB (@lem4491753 A K k s i) (@lem4491759 A K k s i)). Qed.
Lemma lem4491761 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term161 A K k s i) = (term139 A K k s i).
Proof. exact (EQ_MP (@lem4491760 A K k s i) (@lem4491745 A K k s i)). Qed.
Lemma lem4491762 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term169 A K k s) = (term147 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4491761 A K k s i)). Qed.
Lemma lem4491763 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4491764 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term170 A K k s) = (term148 A K k s).
Proof. exact (MK_COMB (@lem4491763 K) (@lem4491762 A K k s)). Qed.
Lemma lem4491771 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term127 A K k s i x) = (term127 A K k s i x).
Proof. exact (eq_refl (term127 A K k s i x)). Qed.
Lemma lem4491772 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term138 A K k s i) = (term138 A K k s i).
Proof. exact (fun_ext (fun x : A => @lem4491771 A K k s i x)). Qed.
Lemma lem4491773 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4491774 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term139 A K k s i) = (term139 A K k s i).
Proof. exact (MK_COMB (@lem4491773 A) (@lem4491772 A K k s i)). Qed.
Lemma lem4491775 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term147 A K k s) = (term147 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4491774 A K k s i)). Qed.
Lemma lem4491776 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4491777 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term148 A K k s) = (term148 A K k s).
Proof. exact (MK_COMB (@lem4491776 K) (@lem4491775 A K k s)). Qed.
Lemma lem4491778 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term170 A K k s) = (term148 A K k s).
Proof. exact (TRANS (@lem4491764 A K k s) (@lem4491777 A K k s)). Qed.
Lemma lem4491779 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : term148 A K k s.
Proof. exact (EQ_MP (@lem4491778 A K k s) (@lem4491692 A K i p2 k s h1)). Qed.
Lemma lem4491788 {A K : Type'} (_52307 : K) (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : term318 A K k s _52307.
Proof. exact (@lem4491733 A K k s i p2 h1 _52307). Qed.
Lemma lem4491789 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_52307 : K) : (term318 A K k s _52307) = (term139 A K k s _52307).
Proof. exact (eq_refl (term318 A K k s _52307)). Qed.
Lemma lem4491790 {A K : Type'} (_52307 : K) (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : term139 A K k s _52307.
Proof. exact (EQ_MP (@lem4491789 A K k s _52307) (@lem4491788 A K _52307 k s i p2 h1)). Qed.
Lemma lem4491791 {A K : Type'} (_52307 : K) (_52308 : A) (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : term319 A K k s _52307 _52308.
Proof. exact (@lem4491790 A K _52307 k s i p2 h1 _52308). Qed.
Lemma lem4491792 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_52307 : K) (_52308 : A) : (term319 A K k s _52307 _52308) = (term127 A K k s _52307 _52308).
Proof. exact (eq_refl (term319 A K k s _52307 _52308)). Qed.
Lemma lem4491794 {A K : Type'} (_52309 : K) (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : term318 A K k s _52309.
Proof. exact (@lem4491779 A K i p2 k s h1 _52309). Qed.
Lemma lem4491795 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_52309 : K) : (term318 A K k s _52309) = (term139 A K k s _52309).
Proof. exact (eq_refl (term318 A K k s _52309)). Qed.
Lemma lem4491796 {A K : Type'} (_52309 : K) (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : term139 A K k s _52309.
Proof. exact (EQ_MP (@lem4491795 A K k s _52309) (@lem4491794 A K _52309 i p2 k s h1)). Qed.
Lemma lem4491797 {A K : Type'} (_52309 : K) (_52310 : A) (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : term319 A K k s _52309 _52310.
Proof. exact (@lem4491796 A K _52309 i p2 k s h1 _52310). Qed.
Lemma lem4491798 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_52309 : K) (_52310 : A) : (term319 A K k s _52309 _52310) = (term127 A K k s _52309 _52310).
Proof. exact (eq_refl (term319 A K k s _52309 _52310)). Qed.
Lemma lem4491805 {A K : Type'} (_52307 : K) (_52308 : A) (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : term127 A K k s _52307 _52308.
Proof. exact (EQ_MP (@lem4491792 A K k s _52307 _52308) (@lem4491791 A K _52307 _52308 k s i p2 h1)). Qed.
Lemma lem4491815 {A K : Type'} (_52309 : K) (_52310 : A) (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : term127 A K k s _52309 _52310.
Proof. exact (EQ_MP (@lem4491798 A K k s _52309 _52310) (@lem4491797 A K _52309 _52310 i p2 k s h1)). Qed.
Lemma lem4491821 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : k i.
Proof. exact (proj1 (@lem4491688 A K k s i p2 h1)). Qed.
Lemma lem4491822 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : term320 K k i.
Proof. exact (fun h0 : term187 K k i => @lem4491821 A K k s i p2 h1). Qed.
Lemma lem4491824 (p : Prop) : (term321 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4491825 {K : Type'} (k : K -> Prop) (i : K) : (term320 K k i) = (k i).
Proof. exact (@lem4491824 (k i)). Qed.
Lemma lem4491826 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : k i.
Proof. exact (EQ_MP (@lem4491825 K k i) (@lem4491822 A K k s i p2 h1)). Qed.
Lemma lem4491828 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : s i p2.
Proof. exact (proj2 (@lem4491688 A K k s i p2 h1)). Qed.
Lemma lem4491829 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : term322 A K s i p2.
Proof. exact (fun h0 : term107 A K s i p2 => @lem4491828 A K k s i p2 h1). Qed.
Lemma lem4491831 (p : Prop) : (term321 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4491832 {A K : Type'} (s : type1470 A K) (i : K) (p2 : A) : (term322 A K s i p2) = (s i p2).
Proof. exact (@lem4491831 (s i p2)). Qed.
Lemma lem4491833 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : s i p2.
Proof. exact (EQ_MP (@lem4491832 A K s i p2) (@lem4491829 A K k s i p2 h1)). Qed.
Lemma lem4491835 (a : Prop) (b : Prop) : (term323 a b) = (term324 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4491836 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_52307 : K) (_52308 : A) : (term127 A K k s _52307 _52308) = (term100 A K k s _52307 _52308).
Proof. exact (@lem4491835 (k _52307) (s _52307 _52308)). Qed.
Lemma lem4491838 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4491839 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_52307 : K) (_52308 : A) : (term100 A K k s _52307 _52308) = (term325 A K k s _52307 _52308).
Proof. exact (@lem4491838 (term99 A K k s _52307 _52308)). Qed.
Lemma lem4491840 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_52307 : K) (_52308 : A) : (term127 A K k s _52307 _52308) = (term325 A K k s _52307 _52308).
Proof. exact (TRANS (@lem4491836 A K k s _52307 _52308) (@lem4491839 A K k s _52307 _52308)). Qed.
Lemma lem4491842 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : term99 A K k s i p2.
Proof. exact (conj (@lem4491826 A K k s i p2 h1) (@lem4491833 A K k s i p2 h1)). Qed.
Lemma lem4491844 {A K : Type'} (_52307 : K) (_52308 : A) (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : term325 A K k s _52307 _52308.
Proof. exact (EQ_MP (@lem4491840 A K k s _52307 _52308) (@lem4491805 A K _52307 _52308 k s i p2 h1)). Qed.
Lemma lem4491845 {A K : Type'} (_52307 : K) (_52308 : A) (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : term325 A K k s _52307 _52308.
Proof. exact (@lem4491844 A K _52307 _52308 k s i p2 h1). Qed.
Lemma lem4491846 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : term325 A K k s i p2.
Proof. exact (@lem4491845 A K i p2 k s i p2 h1). Qed.
Lemma lem4491849 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : False.
Proof. exact (@lem4491846 A K k s i p2 h1 (@lem4491842 A K k s i p2 h1)). Qed.
Lemma lem4491850 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : term326.
Proof. exact (fun h0 : ~ False => @lem4491849 A K k s i p2 h1). Qed.
Lemma lem4491852 (p : Prop) : (term321 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4491853 : term326 = False.
Proof. exact (@lem4491852 False). Qed.
Lemma lem4491854 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (p2 : A) (h1 : term234 A K k s i p2) : False.
Proof. exact (EQ_MP (@lem4491853) (@lem4491850 A K k s i p2 h1)). Qed.
Lemma lem4491856 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : k i.
Proof. exact (proj1 (@lem4491693 A K i p2 k s h1)). Qed.
Lemma lem4491857 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : term320 K k i.
Proof. exact (fun h0 : term187 K k i => @lem4491856 A K i p2 k s h1). Qed.
Lemma lem4491859 (p : Prop) : (term321 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4491860 {K : Type'} (k : K -> Prop) (i : K) : (term320 K k i) = (k i).
Proof. exact (@lem4491859 (k i)). Qed.
Lemma lem4491861 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : k i.
Proof. exact (EQ_MP (@lem4491860 K k i) (@lem4491857 A K i p2 k s h1)). Qed.
Lemma lem4491863 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : s i p2.
Proof. exact (proj2 (@lem4491693 A K i p2 k s h1)). Qed.
Lemma lem4491864 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : term322 A K s i p2.
Proof. exact (fun h0 : term107 A K s i p2 => @lem4491863 A K i p2 k s h1). Qed.
Lemma lem4491866 (p : Prop) : (term321 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4491867 {A K : Type'} (s : type1470 A K) (i : K) (p2 : A) : (term322 A K s i p2) = (s i p2).
Proof. exact (@lem4491866 (s i p2)). Qed.
Lemma lem4491868 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : s i p2.
Proof. exact (EQ_MP (@lem4491867 A K s i p2) (@lem4491864 A K i p2 k s h1)). Qed.
Lemma lem4491870 (a : Prop) (b : Prop) : (term323 a b) = (term324 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4491871 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_52309 : K) (_52310 : A) : (term127 A K k s _52309 _52310) = (term100 A K k s _52309 _52310).
Proof. exact (@lem4491870 (k _52309) (s _52309 _52310)). Qed.
Lemma lem4491873 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4491874 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_52309 : K) (_52310 : A) : (term100 A K k s _52309 _52310) = (term325 A K k s _52309 _52310).
Proof. exact (@lem4491873 (term99 A K k s _52309 _52310)). Qed.
Lemma lem4491875 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_52309 : K) (_52310 : A) : (term127 A K k s _52309 _52310) = (term325 A K k s _52309 _52310).
Proof. exact (TRANS (@lem4491871 A K k s _52309 _52310) (@lem4491874 A K k s _52309 _52310)). Qed.
Lemma lem4491877 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : term99 A K k s i p2.
Proof. exact (conj (@lem4491861 A K i p2 k s h1) (@lem4491868 A K i p2 k s h1)). Qed.
Lemma lem4491879 {A K : Type'} (_52309 : K) (_52310 : A) (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : term325 A K k s _52309 _52310.
Proof. exact (EQ_MP (@lem4491875 A K k s _52309 _52310) (@lem4491815 A K _52309 _52310 i p2 k s h1)). Qed.
Lemma lem4491880 {A K : Type'} (_52309 : K) (_52310 : A) (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : term325 A K k s _52309 _52310.
Proof. exact (@lem4491879 A K _52309 _52310 i p2 k s h1). Qed.
Lemma lem4491881 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : term325 A K k s i p2.
Proof. exact (@lem4491880 A K i p2 i p2 k s h1). Qed.
Lemma lem4491884 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : False.
Proof. exact (@lem4491881 A K i p2 k s h1 (@lem4491877 A K i p2 k s h1)). Qed.
Lemma lem4491885 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : term326.
Proof. exact (fun h0 : ~ False => @lem4491884 A K i p2 k s h1). Qed.
Lemma lem4491887 (p : Prop) : (term321 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4491888 : term326 = False.
Proof. exact (@lem4491887 False). Qed.
Lemma lem4491889 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term263 A K i p2 k s) : False.
Proof. exact (EQ_MP (@lem4491888) (@lem4491885 A K i p2 k s h1)). Qed.
Lemma lem4491890 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term307 A K i p2 k s) : False.
Proof. exact (or_elim (@lem4491685 A K i p2 k s h1) (fun h0 : term234 A K k s i p2 => @lem4491854 A K k s i p2 h0) (fun h0 : term263 A K i p2 k s => @lem4491889 A K i p2 k s h0)). Qed.
Lemma lem4491891 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term307 A K i p2 k s) : (term307 A K i p2 k s) = False.
Proof. exact (prop_ext (fun h2 : term307 A K i p2 k s => @lem4491890 A K i p2 k s h1) (fun h2 : False => @lem4491685 A K i p2 k s h1)). Qed.
Lemma lem4491892 {A K : Type'} (i : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) (h1 : term307 A K i p2 k s) : False.
Proof. exact (EQ_MP (@lem4491891 A K i p2 k s h1) (@lem4491685 A K i p2 k s h1)). Qed.
Lemma lem4491893 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : term310 A K i k s) : False.
Proof. exact (ex_elim (@lem4491610 A K i k s h1) (fun p2 : A => fun h0 : term309 A K i k s p2 => @lem4491892 A K i p2 k s h0)). Qed.
Lemma lem4491894 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term126 A K k s) : False.
Proof. exact (ex_elim (@lem4491609 A K k s h1) (fun i : K => fun h0 : term314 A K k s i => @lem4491893 A K i k s h0)). Qed.
Lemma lem4491895 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term126 A K k s) : (term126 A K k s) = False.
Proof. exact (prop_ext (fun h2 : term126 A K k s => @lem4491894 A K k s h1) (fun h2 : False => @lem4491040 A K k s h1)). Qed.
Lemma lem4491896 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term126 A K k s) : False.
Proof. exact (EQ_MP (@lem4491895 A K k s h1) (@lem4491040 A K k s h1)). Qed.
Lemma lem4491897 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term125 A K k s.
Proof. exact (fun h0 : term126 A K k s => @lem4491896 A K k s h0). Qed.
Lemma lem4491898 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term104 A K k s) = (term112 A K k s).
Proof. exact (EQ_MP (@lem4491039 A K k s) (@lem4491897 A K k s)). Qed.
Lemma lem4491903 {A K : Type'} (k : K -> Prop) : term114 A K k.
Proof. exact (fun s : type1470 A K => @lem4491898 A K k s). Qed.
Lemma lem4491908 {A K : Type'} : term116 A K.
Proof. exact (fun k : K -> Prop => @lem4491903 A K k). Qed.
Lemma lem4491909 {A K : Type'} : term118 A K.
Proof. exact (EQ_MP (@lem4491035 A K) (@lem4491908 A K)). Qed.
Lemma lem4491911 {A K : Type'} : term118 A K.
Proof. exact (@lem4490917 A K (@lem4491909 A K)). Qed.
Lemma lem4491912 {A K : Type'} (h1 : term119 A K) : False.
Proof. exact (@lem4491911 A K (@lem4490901 A K h1)). Qed.
Lemma lem4491913 {A K : Type'} (h1 : term119 A K) : (term119 A K) = False.
Proof. exact (prop_ext (fun h2 : term119 A K => @lem4491912 A K h1) (fun h2 : False => @lem4490901 A K h1)). Qed.
Lemma lem4491914 {A K : Type'} (h1 : term119 A K) : False.
Proof. exact (EQ_MP (@lem4491913 A K h1) (@lem4490901 A K h1)). Qed.
Lemma lem4491915 {A K : Type'} : term118 A K.
Proof. exact (fun h0 : term119 A K => @lem4491914 A K h0). Qed.
Lemma lem4491916 {A K : Type'} : term116 A K.
Proof. exact (EQ_MP (@lem4490900 A K) (@lem4491915 A K)). Qed.
Lemma lem4491918 {A K : Type'} : term96 A K.
Proof. exact (EQ_MP (@lem4490896 A K) (@lem4491916 A K)). Qed.
Lemma lem4491919 {A K : Type'} : term95 A K.
Proof. exact (EQ_MP (@lem4490754 A K) (@lem4491918 A K)). Qed.
