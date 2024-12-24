Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIFF_UNIONS_PAIRWISE_DISJOINT_term_abbrevs.
Require Import DISJOINT_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EMPTY_UNIONS_spec.
Require Import FORALL_IN_GSPEC_spec.
Require Import INTER_UNIONS_spec.
Require Import IN_DIFF_spec.
Require Import UNIONS_UNION_spec.
Require Import pairwise_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1857_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211738_spec.
Require Import thm3211739_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem4825482 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3205495 A s). Qed.
Lemma lem4825483 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem4825484 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem4825483 A s) (@lem4825482 A s)). Qed.
Lemma lem4825485 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem4825484 A s t). Qed.
Lemma lem4825486 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem4825487 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term3 A s t.
Proof. exact (EQ_MP (@lem4825486 A s t) (@lem4825485 A s t)). Qed.
Lemma lem4825488 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term4 A s t x.
Proof. exact (@lem4825487 A s t x). Qed.
Lemma lem4825489 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A s t x) = ((term5 A x s t) = (term6 A s x t)).
Proof. exact (eq_refl (term4 A s t x)). Qed.
Lemma lem4825491 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3196110 A s). Qed.
Lemma lem4825492 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem4825493 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem4825492 A s) (@lem4825491 A s)). Qed.
Lemma lem4825494 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem4825493 A s t). Qed.
Lemma lem4825495 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = ((@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A))).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem4825497 {_110510 : Type'} (s : _110510 -> Prop) : term10 _110510 s.
Proof. exact (@lem4794393 _110510 s). Qed.
Lemma lem4825498 {_110510 : Type'} (s : _110510 -> Prop) : (term10 _110510 s) = (term11 _110510 s).
Proof. exact (eq_refl (term10 _110510 s)). Qed.
Lemma lem4825499 {_110510 : Type'} (s : _110510 -> Prop) : term11 _110510 s.
Proof. exact (EQ_MP (@lem4825498 _110510 s) (@lem4825497 _110510 s)). Qed.
Lemma lem4825500 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : term12 _110510 s r.
Proof. exact (@lem4825499 _110510 s r). Qed.
Lemma lem4825501 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (term12 _110510 s r) = ((@pairwise _110510 r s) = (term13 _110510 s r)).
Proof. exact (eq_refl (term12 _110510 s r)). Qed.
Lemma lem4825526 {_88905 _89106 : Type'} (Q : _89106 -> Prop) : term14 _88905 _89106 Q.
Proof. exact (proj1 (@lem3435744 _88905 Prop Prop Prop Prop Prop _89106 Prop Prop Prop Prop Q)). Qed.
Lemma lem4825527 {_88905 _89106 : Type'} (Q : _89106 -> Prop) (P : _88905 -> Prop) : term15 _88905 _89106 Q P.
Proof. exact (@lem4825526 _88905 _89106 Q P). Qed.
Lemma lem4825528 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) : (term15 _88905 _89106 Q P) = (term16 _88905 _89106 P Q).
Proof. exact (eq_refl (term15 _88905 _89106 Q P)). Qed.
Lemma lem4825529 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) : term16 _88905 _89106 P Q.
Proof. exact (EQ_MP (@lem4825528 _88905 _89106 P Q) (@lem4825527 _88905 _89106 Q P)). Qed.
Lemma lem4825530 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : term17 _88905 _89106 P Q f.
Proof. exact (@lem4825529 _88905 _89106 P Q f). Qed.
Lemma lem4825531 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term17 _88905 _89106 P Q f) = ((term18 _88905 _89106 P f Q) = (term19 _88905 _89106 P Q f)).
Proof. exact (eq_refl (term17 _88905 _89106 P Q f)). Qed.
Lemma lem4825533 {_86951 : Type'} (s : type686 _86951) : term20 _86951 s.
Proof. exact (@lem3329633 _86951 s). Qed.
Lemma lem4825534 {_86951 : Type'} (s : type686 _86951) : (term20 _86951 s) = (((@UNIONS _86951 s) = (@EMPTY _86951)) = (term21 _86951 s)).
Proof. exact (eq_refl (term20 _86951 s)). Qed.
Lemma lem4825536 {_87026 : Type'} : term22 _87026.
Proof. exact (proj2 (@lem3341279 Prop _87026)). Qed.
Lemma lem4825537 {_87026 : Type'} (s : type686 _87026) : term23 _87026 s.
Proof. exact (@lem4825536 _87026 s). Qed.
Lemma lem4825538 {_87026 : Type'} (s : type686 _87026) : (term23 _87026 s) = (term24 _87026 s).
Proof. exact (eq_refl (term23 _87026 s)). Qed.
Lemma lem4825539 {_87026 : Type'} (s : type686 _87026) : term24 _87026 s.
Proof. exact (EQ_MP (@lem4825538 _87026 s) (@lem4825537 _87026 s)). Qed.
Lemma lem4825540 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : term25 _87026 s t.
Proof. exact (@lem4825539 _87026 s t). Qed.
Lemma lem4825541 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term25 _87026 s t) = ((term26 _87026 t s) = (term27 _87026 s t)).
Proof. exact (eq_refl (term25 _87026 s t)). Qed.
Lemma lem4825543 {_86990 : Type'} : term28 _86990.
Proof. exact (proj1 (@lem3341279 _86990 Prop)). Qed.
Lemma lem4825544 {_86990 : Type'} (s : type686 _86990) : term29 _86990 s.
Proof. exact (@lem4825543 _86990 s). Qed.
Lemma lem4825545 {_86990 : Type'} (s : type686 _86990) : (term29 _86990 s) = (term30 _86990 s).
Proof. exact (eq_refl (term29 _86990 s)). Qed.
Lemma lem4825546 {_86990 : Type'} (s : type686 _86990) : term30 _86990 s.
Proof. exact (EQ_MP (@lem4825545 _86990 s) (@lem4825544 _86990 s)). Qed.
Lemma lem4825547 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : term31 _86990 s t.
Proof. exact (@lem4825546 _86990 s t). Qed.
Lemma lem4825548 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term31 _86990 s t) = ((term32 _86990 s t) = (term33 _86990 s t)).
Proof. exact (eq_refl (term31 _86990 s t)). Qed.
Lemma lem4825550 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3196110 A s). Qed.
Lemma lem4825551 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem4825552 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem4825551 A s) (@lem4825550 A s)). Qed.
Lemma lem4825553 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem4825552 A s t). Qed.
Lemma lem4825554 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = ((@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A))).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem4825558 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (h1 : (term34 _87099 s t) = (term35 _87099 s t)) : (term34 _87099 s t) = (term35 _87099 s t).
Proof. exact (h1). Qed.
Lemma lem4825559 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (h1 : (term34 _87099 s t) = (term35 _87099 s t)) : (term35 _87099 s t) = (term34 _87099 s t).
Proof. exact (SYM (@lem4825558 _87099 s t h1)). Qed.
Lemma lem4825560 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (h1 : (term35 _87099 s t) = (term34 _87099 s t)) : (term35 _87099 s t) = (term34 _87099 s t).
Proof. exact (h1). Qed.
Lemma lem4825561 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (h1 : (term35 _87099 s t) = (term34 _87099 s t)) : (term34 _87099 s t) = (term35 _87099 s t).
Proof. exact (SYM (@lem4825560 _87099 s t h1)). Qed.
Lemma lem4825562 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) : ((term34 _87099 s t) = (term35 _87099 s t)) = ((term35 _87099 s t) = (term34 _87099 s t)).
Proof. exact (prop_ext (fun h1 : (term34 _87099 s t) = (term35 _87099 s t) => @lem4825559 _87099 s t h1) (fun h1 : (term35 _87099 s t) = (term34 _87099 s t) => @lem4825561 _87099 s t h1)). Qed.
Lemma lem4825563 {_87099 : Type'} (s : type686 _87099) : (term36 _87099 s) = (term37 _87099 s).
Proof. exact (fun_ext (fun t : type686 _87099 => @lem4825562 _87099 s t)). Qed.
Lemma lem4825564 {_87099 : Type'} : (@all ((_87099 -> Prop) -> Prop)) = (@all ((_87099 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87099 -> Prop) -> Prop))). Qed.
Lemma lem4825565 {_87099 : Type'} (s : type686 _87099) : (term38 _87099 s) = (term39 _87099 s).
Proof. exact (MK_COMB (@lem4825564 _87099) (@lem4825563 _87099 s)). Qed.
Lemma lem4825566 {_87099 : Type'} : (term40 _87099) = (term41 _87099).
Proof. exact (fun_ext (fun s : type686 _87099 => @lem4825565 _87099 s)). Qed.
Lemma lem4825567 {_87099 : Type'} : (@all ((_87099 -> Prop) -> Prop)) = (@all ((_87099 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87099 -> Prop) -> Prop))). Qed.
Lemma lem4825568 {_87099 : Type'} : (term42 _87099) = (term43 _87099).
Proof. exact (MK_COMB (@lem4825567 _87099) (@lem4825566 _87099)). Qed.
Lemma lem4825569 {_87099 : Type'} : term43 _87099.
Proof. exact (EQ_MP (@lem4825568 _87099) (@lem3345333 _87099)). Qed.
Lemma lem4825570 {_87099 : Type'} (s : type686 _87099) : term44 _87099 s.
Proof. exact (@lem4825569 _87099 s). Qed.
Lemma lem4825571 {_87099 : Type'} (s : type686 _87099) : (term44 _87099 s) = (term39 _87099 s).
Proof. exact (eq_refl (term44 _87099 s)). Qed.
Lemma lem4825572 {_87099 : Type'} (s : type686 _87099) : term39 _87099 s.
Proof. exact (EQ_MP (@lem4825571 _87099 s) (@lem4825570 _87099 s)). Qed.
Lemma lem4825573 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) : term45 _87099 s t.
Proof. exact (@lem4825572 _87099 s t). Qed.
Lemma lem4825574 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) : (term45 _87099 s t) = ((term35 _87099 s t) = (term34 _87099 s t)).
Proof. exact (eq_refl (term45 _87099 s t)). Qed.
Lemma lem4825576 (t1 : Prop) : term46 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4825577 (t1 : Prop) : (term46 t1) = (term47 t1).
Proof. exact (eq_refl (term46 t1)). Qed.
Lemma lem4825578 (t1 : Prop) : term47 t1.
Proof. exact (EQ_MP (@lem4825577 t1) (@lem4825576 t1)). Qed.
Lemma lem4825579 (t1 : Prop) (t2 : Prop) : term48 t1 t2.
Proof. exact (@lem4825578 t1 t2). Qed.
Lemma lem4825580 (t1 : Prop) (t2 : Prop) : (term48 t1 t2) = (term49 t1 t2).
Proof. exact (eq_refl (term48 t1 t2)). Qed.
Lemma lem4825581 (t1 : Prop) (t2 : Prop) : term49 t1 t2.
Proof. exact (EQ_MP (@lem4825580 t1 t2) (@lem4825579 t1 t2)). Qed.
Lemma lem4825582 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term50 t1 t2 t3.
Proof. exact (@lem4825581 t1 t2 t3). Qed.
Lemma lem4825583 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term50 t1 t2 t3) = ((term51 t1 t2 t3) = (term52 t1 t2 t3)).
Proof. exact (eq_refl (term50 t1 t2 t3)). Qed.
Lemma lem4825584 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term51 t1 t2 t3) = (term52 t1 t2 t3).
Proof. exact (EQ_MP (@lem4825583 t1 t2 t3) (@lem4825582 t1 t2 t3)). Qed.
Lemma lem4825585 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term52 t1 t2 t3) = (term51 t1 t2 t3).
Proof. exact (SYM (@lem4825584 t1 t2 t3)). Qed.
Lemma lem4825593 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term53 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4825594 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) : (s = t) = (term53 _110927 s t).
Proof. exact (@lem4825593 _110927 s t). Qed.
Lemma lem4825595 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : ((@UNION _110927 t u) = s) = (term54 _110927 t u s).
Proof. exact (@lem4825594 _110927 (@UNION _110927 t u) s). Qed.
Lemma lem4825604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4825605 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term55 _110927 t u s) = (term56 _110927 t u s).
Proof. exact (MK_COMB (@lem4825604) (@lem4825595 _110927 t u s)). Qed.
Lemma lem4825607 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem4825608 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) : (@DISJOINT _110927 s t) = ((@INTER _110927 s t) = (@EMPTY _110927)).
Proof. exact (@lem4825607 _110927 s t). Qed.
Lemma lem4825609 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (@DISJOINT _110927 t u) = ((@INTER _110927 t u) = (@EMPTY _110927)).
Proof. exact (@lem4825608 _110927 t u). Qed.
Lemma lem4825613 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term53 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4825614 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) : (s = t) = (term53 _110927 s t).
Proof. exact (@lem4825613 _110927 s t). Qed.
Lemma lem4825615 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : ((@INTER _110927 t u) = (@EMPTY _110927)) = (term57 _110927 t u).
Proof. exact (@lem4825614 _110927 (@INTER _110927 t u) (@EMPTY _110927)). Qed.
Lemma lem4825620 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (@DISJOINT _110927 t u) = (term57 _110927 t u).
Proof. exact (TRANS (@lem4825609 _110927 t u) (@lem4825615 _110927 t u)). Qed.
Lemma lem4825625 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term58 _110927 s t u) = (term59 _110927 s t u).
Proof. exact (MK_COMB (@lem4825605 _110927 t u s) (@lem4825620 _110927 t u)). Qed.
Lemma lem4825628 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4825629 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term60 _110927 s t u) = (term61 _110927 s t u).
Proof. exact (MK_COMB (@lem4825628) (@lem4825625 _110927 s t u)). Qed.
Lemma lem4825633 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term53 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4825634 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) : (s = t) = (term53 _110927 s t).
Proof. exact (@lem4825633 _110927 s t). Qed.
Lemma lem4825635 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : ((@DIFF _110927 s t) = u) = (term62 _110927 s t u).
Proof. exact (@lem4825634 _110927 (@DIFF _110927 s t) u). Qed.
Lemma lem4825644 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term63 _110927 s t u) = (term64 _110927 s t u).
Proof. exact (MK_COMB (@lem4825629 _110927 s t u) (@lem4825635 _110927 s t u)). Qed.
Lemma lem4825647 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term64 _110927 s t u) = (term63 _110927 s t u).
Proof. exact (SYM (@lem4825644 _110927 s t u)). Qed.
Lemma lem4825659 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term65 A x s t) = (term66 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem4825660 {_110927 : Type'} (s : _110927 -> Prop) (x : _110927) (t : _110927 -> Prop) : (term65 _110927 x s t) = (term66 _110927 s x t).
Proof. exact (@lem4825659 _110927 s x t). Qed.
Lemma lem4825661 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) (u : _110927 -> Prop) : (term65 _110927 x t u) = (term66 _110927 t x u).
Proof. exact (@lem4825660 _110927 t x u). Qed.
Lemma lem4825665 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4825666 {_110927 : Type'} (P : _110927 -> Prop) (x : _110927) : (@IN _110927 x P) = (P x).
Proof. exact (@lem4825665 _110927 P x). Qed.
Lemma lem4825667 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) : (@IN _110927 x t) = (t x).
Proof. exact (@lem4825666 _110927 t x). Qed.
Lemma lem4825668 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4825669 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) : (term67 _110927 x t) = (term68 _110927 t x).
Proof. exact (MK_COMB (@lem4825668) (@lem4825667 _110927 t x)). Qed.
Lemma lem4825671 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4825672 {_110927 : Type'} (P : _110927 -> Prop) (x : _110927) : (@IN _110927 x P) = (P x).
Proof. exact (@lem4825671 _110927 P x). Qed.
Lemma lem4825673 {_110927 : Type'} (u : _110927 -> Prop) (x : _110927) : (@IN _110927 x u) = (u x).
Proof. exact (@lem4825672 _110927 u x). Qed.
Lemma lem4825674 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term66 _110927 t x u) = (term69 _110927 t u x).
Proof. exact (MK_COMB (@lem4825669 _110927 t x) (@lem4825673 _110927 u x)). Qed.
Lemma lem4825677 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term65 _110927 x t u) = (term69 _110927 t u x).
Proof. exact (TRANS (@lem4825661 _110927 t x u) (@lem4825674 _110927 t u x)). Qed.
Lemma lem4825678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4825679 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term70 _110927 x t u) = (term71 _110927 t u x).
Proof. exact (MK_COMB (@lem4825678) (@lem4825677 _110927 t u x)). Qed.
Lemma lem4825681 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4825682 {_110927 : Type'} (P : _110927 -> Prop) (x : _110927) : (@IN _110927 x P) = (P x).
Proof. exact (@lem4825681 _110927 P x). Qed.
Lemma lem4825683 {_110927 : Type'} (s : _110927 -> Prop) (x : _110927) : (@IN _110927 x s) = (s x).
Proof. exact (@lem4825682 _110927 s x). Qed.
Lemma lem4825684 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : ((term65 _110927 x t u) = (@IN _110927 x s)) = ((term69 _110927 t u x) = (s x)).
Proof. exact (MK_COMB (@lem4825679 _110927 t u x) (@lem4825683 _110927 s x)). Qed.
Lemma lem4825687 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term72 _110927 t u s) = (term73 _110927 t u s).
Proof. exact (fun_ext (fun x : _110927 => @lem4825684 _110927 t u s x)). Qed.
Lemma lem4825688 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4825689 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term54 _110927 t u s) = (term74 _110927 t u s).
Proof. exact (MK_COMB (@lem4825688 _110927) (@lem4825687 _110927 t u s)). Qed.
Lemma lem4825694 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4825695 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term56 _110927 t u s) = (term75 _110927 t u s).
Proof. exact (MK_COMB (@lem4825694) (@lem4825689 _110927 t u s)). Qed.
Lemma lem4825703 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term76 A x s t) = (term77 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem4825704 {_110927 : Type'} (s : _110927 -> Prop) (x : _110927) (t : _110927 -> Prop) : (term76 _110927 x s t) = (term77 _110927 s x t).
Proof. exact (@lem4825703 _110927 s x t). Qed.
Lemma lem4825705 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) (u : _110927 -> Prop) : (term76 _110927 x t u) = (term77 _110927 t x u).
Proof. exact (@lem4825704 _110927 t x u). Qed.
Lemma lem4825709 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4825710 {_110927 : Type'} (P : _110927 -> Prop) (x : _110927) : (@IN _110927 x P) = (P x).
Proof. exact (@lem4825709 _110927 P x). Qed.
Lemma lem4825711 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) : (@IN _110927 x t) = (t x).
Proof. exact (@lem4825710 _110927 t x). Qed.
Lemma lem4825712 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4825713 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) : (term78 _110927 x t) = (term79 _110927 t x).
Proof. exact (MK_COMB (@lem4825712) (@lem4825711 _110927 t x)). Qed.
Lemma lem4825715 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4825716 {_110927 : Type'} (P : _110927 -> Prop) (x : _110927) : (@IN _110927 x P) = (P x).
Proof. exact (@lem4825715 _110927 P x). Qed.
Lemma lem4825717 {_110927 : Type'} (u : _110927 -> Prop) (x : _110927) : (@IN _110927 x u) = (u x).
Proof. exact (@lem4825716 _110927 u x). Qed.
Lemma lem4825718 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term77 _110927 t x u) = (term80 _110927 t u x).
Proof. exact (MK_COMB (@lem4825713 _110927 t x) (@lem4825717 _110927 u x)). Qed.
Lemma lem4825721 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term76 _110927 x t u) = (term80 _110927 t u x).
Proof. exact (TRANS (@lem4825705 _110927 t x u) (@lem4825718 _110927 t u x)). Qed.
Lemma lem4825722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4825723 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term81 _110927 x t u) = (term82 _110927 t u x).
Proof. exact (MK_COMB (@lem4825722) (@lem4825721 _110927 t u x)). Qed.
Lemma lem4825725 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4825726 {_110927 : Type'} (x : _110927) : (@IN _110927 x (@EMPTY _110927)) = False.
Proof. exact (@lem4825725 _110927 x). Qed.
Lemma lem4825727 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : ((term76 _110927 x t u) = (@IN _110927 x (@EMPTY _110927))) = ((term80 _110927 t u x) = False).
Proof. exact (MK_COMB (@lem4825723 _110927 t u x) (@lem4825726 _110927 x)). Qed.
Lemma lem4825729 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4825730 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : ((term80 _110927 t u x) = False) = (term83 _110927 t u x).
Proof. exact (@lem4825729 (term80 _110927 t u x)). Qed.
Lemma lem4825733 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : ((term76 _110927 x t u) = (@IN _110927 x (@EMPTY _110927))) = (term83 _110927 t u x).
Proof. exact (TRANS (@lem4825727 _110927 t u x) (@lem4825730 _110927 t u x)). Qed.
Lemma lem4825734 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term84 _110927 t u) = (term85 _110927 t u).
Proof. exact (fun_ext (fun x : _110927 => @lem4825733 _110927 t u x)). Qed.
Lemma lem4825735 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4825736 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term57 _110927 t u) = (term86 _110927 t u).
Proof. exact (MK_COMB (@lem4825735 _110927) (@lem4825734 _110927 t u)). Qed.
Lemma lem4825741 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term59 _110927 s t u) = (term87 _110927 s t u).
Proof. exact (MK_COMB (@lem4825695 _110927 t u s) (@lem4825736 _110927 t u)). Qed.
Lemma lem4825744 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4825745 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term61 _110927 s t u) = (term88 _110927 s t u).
Proof. exact (MK_COMB (@lem4825744) (@lem4825741 _110927 s t u)). Qed.
Lemma lem4825753 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4825754 {_110927 : Type'} (s : _110927 -> Prop) (x : _110927) (t : _110927 -> Prop) : (term5 _110927 x s t) = (term6 _110927 s x t).
Proof. exact (@lem4825753 _110927 s x t). Qed.
Lemma lem4825758 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4825759 {_110927 : Type'} (P : _110927 -> Prop) (x : _110927) : (@IN _110927 x P) = (P x).
Proof. exact (@lem4825758 _110927 P x). Qed.
Lemma lem4825760 {_110927 : Type'} (s : _110927 -> Prop) (x : _110927) : (@IN _110927 x s) = (s x).
Proof. exact (@lem4825759 _110927 s x). Qed.
Lemma lem4825761 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4825762 {_110927 : Type'} (s : _110927 -> Prop) (x : _110927) : (term78 _110927 x s) = (term79 _110927 s x).
Proof. exact (MK_COMB (@lem4825761) (@lem4825760 _110927 s x)). Qed.
Lemma lem4825764 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4825765 {_110927 : Type'} (P : _110927 -> Prop) (x : _110927) : (@IN _110927 x P) = (P x).
Proof. exact (@lem4825764 _110927 P x). Qed.
Lemma lem4825766 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) : (@IN _110927 x t) = (t x).
Proof. exact (@lem4825765 _110927 t x). Qed.
Lemma lem4825767 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4825768 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) : (term89 _110927 x t) = (term90 _110927 t x).
Proof. exact (MK_COMB (@lem4825767) (@lem4825766 _110927 t x)). Qed.
Lemma lem4825769 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (x : _110927) : (term6 _110927 s x t) = (term91 _110927 s t x).
Proof. exact (MK_COMB (@lem4825762 _110927 s x) (@lem4825768 _110927 t x)). Qed.
Lemma lem4825772 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (x : _110927) : (term5 _110927 x s t) = (term91 _110927 s t x).
Proof. exact (TRANS (@lem4825754 _110927 s x t) (@lem4825769 _110927 s t x)). Qed.
Lemma lem4825773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4825774 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (x : _110927) : (term92 _110927 x s t) = (term93 _110927 s t x).
Proof. exact (MK_COMB (@lem4825773) (@lem4825772 _110927 s t x)). Qed.
Lemma lem4825776 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4825777 {_110927 : Type'} (P : _110927 -> Prop) (x : _110927) : (@IN _110927 x P) = (P x).
Proof. exact (@lem4825776 _110927 P x). Qed.
Lemma lem4825778 {_110927 : Type'} (u : _110927 -> Prop) (x : _110927) : (@IN _110927 x u) = (u x).
Proof. exact (@lem4825777 _110927 u x). Qed.
Lemma lem4825779 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : ((term5 _110927 x s t) = (@IN _110927 x u)) = ((term91 _110927 s t x) = (u x)).
Proof. exact (MK_COMB (@lem4825774 _110927 s t x) (@lem4825778 _110927 u x)). Qed.
Lemma lem4825782 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term94 _110927 s t u) = (term95 _110927 s t u).
Proof. exact (fun_ext (fun x : _110927 => @lem4825779 _110927 s t u x)). Qed.
Lemma lem4825783 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4825784 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term62 _110927 s t u) = (term96 _110927 s t u).
Proof. exact (MK_COMB (@lem4825783 _110927) (@lem4825782 _110927 s t u)). Qed.
Lemma lem4825789 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term64 _110927 s t u) = (term97 _110927 s t u).
Proof. exact (MK_COMB (@lem4825745 _110927 s t u) (@lem4825784 _110927 s t u)). Qed.
Lemma lem4825792 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term97 _110927 s t u) = (term64 _110927 s t u).
Proof. exact (SYM (@lem4825789 _110927 s t u)). Qed.
Lemma lem4825794 (p : Prop) : p = (term98 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4825795 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term97 _110927 s t u) = (term99 _110927 s t u).
Proof. exact (@lem4825794 (term97 _110927 s t u)). Qed.
Lemma lem4825796 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term99 _110927 s t u) = (term97 _110927 s t u).
Proof. exact (SYM (@lem4825795 _110927 s t u)). Qed.
Lemma lem4825797 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term100 _110927 s t u) : term100 _110927 s t u.
Proof. exact (h1). Qed.
Lemma lem4825800 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term99 _110927 s t u) : term99 _110927 s t u.
Proof. exact (h1). Qed.
Lemma lem4825801 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : term101 _110927 s t u.
Proof. exact (fun h0 : term99 _110927 s t u => @lem4825800 _110927 s t u h0). Qed.
Lemma lem4825802 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term101 _110927 s t u) : term101 _110927 s t u.
Proof. exact (h1). Qed.
Lemma lem4825803 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term99 _110927 s t u) : term99 _110927 s t u.
Proof. exact (h1). Qed.
Lemma lem4825804 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term99 _110927 s t u) (h2 : term101 _110927 s t u) : term99 _110927 s t u.
Proof. exact (@lem4825802 _110927 s t u h2 (@lem4825803 _110927 s t u h1)). Qed.
Lemma lem4825805 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term99 _110927 s t u) : term102 _110927 s t u.
Proof. exact (fun h0 : term101 _110927 s t u => @lem4825804 _110927 s t u h1 h0). Qed.
Lemma lem4825806 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term101 _110927 s t u) : term101 _110927 s t u.
Proof. exact (h1). Qed.
Lemma lem4825807 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term99 _110927 s t u) (h2 : term101 _110927 s t u) : term99 _110927 s t u.
Proof. exact (@lem4825805 _110927 s t u h1 (@lem4825806 _110927 s t u h2)). Qed.
Lemma lem4825808 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term101 _110927 s t u) : term101 _110927 s t u.
Proof. exact (fun h0 : term99 _110927 s t u => @lem4825807 _110927 s t u h0 h1). Qed.
Lemma lem4825809 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : term103 _110927 s t u.
Proof. exact (fun h0 : term101 _110927 s t u => @lem4825808 _110927 s t u h0). Qed.
Lemma lem4825812 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : term101 _110927 s t u.
Proof. exact (@lem4825809 _110927 s t u (@lem4825801 _110927 s t u)). Qed.
Lemma lem4825813 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : term101 _110927 s t u.
Proof. exact (@lem4825812 _110927 s t u). Qed.
Lemma lem4825827 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4825828 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term99 _110927 s t u) = (term104 _110927 s t u).
Proof. exact (@lem4825827 (term100 _110927 s t u)). Qed.
Lemma lem4825830 (t : Prop) : (term105 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4825831 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term104 _110927 s t u) = (term97 _110927 s t u).
Proof. exact (@lem4825830 (term97 _110927 s t u)). Qed.
Lemma lem4825834 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term99 _110927 s t u) = (term97 _110927 s t u).
Proof. exact (TRANS (@lem4825828 _110927 s t u) (@lem4825831 _110927 s t u)). Qed.
Lemma lem4825855 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term106 _110927 t u) = (term107 _110927 t u).
Proof. exact (fun_ext (fun s : _110927 -> Prop => @lem4825834 _110927 s t u)). Qed.
Lemma lem4825856 {_110927 : Type'} : (@all (_110927 -> Prop)) = (@all (_110927 -> Prop)).
Proof. exact (eq_refl (@all (_110927 -> Prop))). Qed.
Lemma lem4825857 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term108 _110927 t u) = (term109 _110927 t u).
Proof. exact (MK_COMB (@lem4825856 _110927) (@lem4825855 _110927 t u)). Qed.
Lemma lem4825862 {_110927 : Type'} (u : _110927 -> Prop) : (term110 _110927 u) = (term111 _110927 u).
Proof. exact (fun_ext (fun t : _110927 -> Prop => @lem4825857 _110927 t u)). Qed.
Lemma lem4825863 {_110927 : Type'} : (@all (_110927 -> Prop)) = (@all (_110927 -> Prop)).
Proof. exact (eq_refl (@all (_110927 -> Prop))). Qed.
Lemma lem4825864 {_110927 : Type'} (u : _110927 -> Prop) : (term112 _110927 u) = (term113 _110927 u).
Proof. exact (MK_COMB (@lem4825863 _110927) (@lem4825862 _110927 u)). Qed.
Lemma lem4825869 {_110927 : Type'} : (term114 _110927) = (term115 _110927).
Proof. exact (fun_ext (fun u : _110927 -> Prop => @lem4825864 _110927 u)). Qed.
Lemma lem4825870 {_110927 : Type'} : (@all (_110927 -> Prop)) = (@all (_110927 -> Prop)).
Proof. exact (eq_refl (@all (_110927 -> Prop))). Qed.
Lemma lem4825879 {_110927 : Type'} : (term116 _110927) = (term117 _110927).
Proof. exact (MK_COMB (@lem4825870 _110927) (@lem4825869 _110927)). Qed.
Lemma lem4825890 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : ((term91 _110927 s t x) = (u x)) = ((term91 _110927 s t x) = (u x)).
Proof. exact (eq_refl ((term91 _110927 s t x) = (u x))). Qed.
Lemma lem4825891 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term95 _110927 s t u) = (term95 _110927 s t u).
Proof. exact (fun_ext (fun x : _110927 => @lem4825890 _110927 s t u x)). Qed.
Lemma lem4825892 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4825893 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term96 _110927 s t u) = (term96 _110927 s t u).
Proof. exact (MK_COMB (@lem4825892 _110927) (@lem4825891 _110927 s t u)). Qed.
Lemma lem4825900 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term83 _110927 t u x) = (term83 _110927 t u x).
Proof. exact (eq_refl (term83 _110927 t u x)). Qed.
Lemma lem4825901 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term85 _110927 t u) = (term85 _110927 t u).
Proof. exact (fun_ext (fun x : _110927 => @lem4825900 _110927 t u x)). Qed.
Lemma lem4825902 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4825903 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term86 _110927 t u) = (term86 _110927 t u).
Proof. exact (MK_COMB (@lem4825902 _110927) (@lem4825901 _110927 t u)). Qed.
Lemma lem4825912 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : ((term69 _110927 t u x) = (s x)) = ((term69 _110927 t u x) = (s x)).
Proof. exact (eq_refl ((term69 _110927 t u x) = (s x))). Qed.
Lemma lem4825913 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term73 _110927 t u s) = (term73 _110927 t u s).
Proof. exact (fun_ext (fun x : _110927 => @lem4825912 _110927 t u s x)). Qed.
Lemma lem4825914 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4825915 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term74 _110927 t u s) = (term74 _110927 t u s).
Proof. exact (MK_COMB (@lem4825914 _110927) (@lem4825913 _110927 t u s)). Qed.
Lemma lem4825916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4825917 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term75 _110927 t u s) = (term75 _110927 t u s).
Proof. exact (MK_COMB (@lem4825916) (@lem4825915 _110927 t u s)). Qed.
Lemma lem4825918 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term87 _110927 s t u) = (term87 _110927 s t u).
Proof. exact (MK_COMB (@lem4825917 _110927 t u s) (@lem4825903 _110927 t u)). Qed.
Lemma lem4825919 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4825920 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term88 _110927 s t u) = (term88 _110927 s t u).
Proof. exact (MK_COMB (@lem4825919) (@lem4825918 _110927 s t u)). Qed.
Lemma lem4825921 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term97 _110927 s t u) = (term97 _110927 s t u).
Proof. exact (MK_COMB (@lem4825920 _110927 s t u) (@lem4825893 _110927 s t u)). Qed.
Lemma lem4825922 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term107 _110927 t u) = (term107 _110927 t u).
Proof. exact (fun_ext (fun s : _110927 -> Prop => @lem4825921 _110927 s t u)). Qed.
Lemma lem4825923 {_110927 : Type'} : (@all (_110927 -> Prop)) = (@all (_110927 -> Prop)).
Proof. exact (eq_refl (@all (_110927 -> Prop))). Qed.
Lemma lem4825924 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term109 _110927 t u) = (term109 _110927 t u).
Proof. exact (MK_COMB (@lem4825923 _110927) (@lem4825922 _110927 t u)). Qed.
Lemma lem4825925 {_110927 : Type'} (u : _110927 -> Prop) : (term111 _110927 u) = (term111 _110927 u).
Proof. exact (fun_ext (fun t : _110927 -> Prop => @lem4825924 _110927 t u)). Qed.
Lemma lem4825926 {_110927 : Type'} : (@all (_110927 -> Prop)) = (@all (_110927 -> Prop)).
Proof. exact (eq_refl (@all (_110927 -> Prop))). Qed.
Lemma lem4825927 {_110927 : Type'} (u : _110927 -> Prop) : (term113 _110927 u) = (term113 _110927 u).
Proof. exact (MK_COMB (@lem4825926 _110927) (@lem4825925 _110927 u)). Qed.
Lemma lem4825928 {_110927 : Type'} : (term115 _110927) = (term115 _110927).
Proof. exact (fun_ext (fun u : _110927 -> Prop => @lem4825927 _110927 u)). Qed.
Lemma lem4825929 {_110927 : Type'} : (@all (_110927 -> Prop)) = (@all (_110927 -> Prop)).
Proof. exact (eq_refl (@all (_110927 -> Prop))). Qed.
Lemma lem4825930 {_110927 : Type'} : (term117 _110927) = (term117 _110927).
Proof. exact (MK_COMB (@lem4825929 _110927) (@lem4825928 _110927)). Qed.
Lemma lem4825979 {_110927 : Type'} : (term116 _110927) = (term117 _110927).
Proof. exact (TRANS (@lem4825879 _110927) (@lem4825930 _110927)). Qed.
Lemma lem4825980 {_110927 : Type'} : (term117 _110927) = (term116 _110927).
Proof. exact (SYM (@lem4825979 _110927)). Qed.
Lemma lem4825981 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term87 _110927 s t u.
Proof. exact (h1). Qed.
Lemma lem4825983 (p : Prop) : p = (term98 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4825984 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : ((term91 _110927 s t x) = (u x)) = (term118 _110927 s t u x).
Proof. exact (@lem4825983 ((term91 _110927 s t x) = (u x))). Qed.
Lemma lem4825985 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term118 _110927 s t u x) = ((term91 _110927 s t x) = (u x)).
Proof. exact (SYM (@lem4825984 _110927 s t u x)). Qed.
Lemma lem4825986 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term119 _110927 s t u x) : term119 _110927 s t u x.
Proof. exact (h1). Qed.
Lemma lem4825995 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term120 _110927 t u x) = (term121 _110927 t u x).
Proof. exact (@lem17160 (t x) (u x)). Qed.
Lemma lem4826000 {_110927 : Type'} (s : _110927 -> Prop) (x : _110927) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4826001 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4826002 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term122 _110927 t u x) = (term123 _110927 t u x).
Proof. exact (MK_COMB (@lem4826001) (@lem4825995 _110927 t u x)). Qed.
Lemma lem4826003 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : (term124 _110927 t u s x) = (term125 _110927 t u s x).
Proof. exact (MK_COMB (@lem4826002 _110927 t u x) (@lem4826000 _110927 s x)). Qed.
Lemma lem4826008 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : (term126 _110927 t u s x) = (term126 _110927 t u s x).
Proof. exact (eq_refl (term126 _110927 t u s x)). Qed.
Lemma lem4826009 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : (term127 _110927 t u s x) = (term128 _110927 t u s x).
Proof. exact (MK_COMB (@lem4826008 _110927 t u s x) (@lem4826003 _110927 t u s x)). Qed.
Lemma lem4826010 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : ((term69 _110927 t u x) = (s x)) = (term127 _110927 t u s x).
Proof. exact (@lem17784 (term69 _110927 t u x) (s x)). Qed.
Lemma lem4826011 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : ((term69 _110927 t u x) = (s x)) = (term128 _110927 t u s x).
Proof. exact (TRANS (@lem4826010 _110927 t u s x) (@lem4826009 _110927 t u s x)). Qed.
Lemma lem4826012 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term73 _110927 t u s) = (term129 _110927 t u s).
Proof. exact (fun_ext (fun x : _110927 => @lem4826011 _110927 t u s x)). Qed.
Lemma lem4826013 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4826014 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term74 _110927 t u s) = (term130 _110927 t u s).
Proof. exact (MK_COMB (@lem4826013 _110927) (@lem4826012 _110927 t u s)). Qed.
Lemma lem4826021 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term83 _110927 t u x) = (term131 _110927 t u x).
Proof. exact (@lem17045 (t x) (u x)). Qed.
Lemma lem4826022 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term85 _110927 t u) = (term132 _110927 t u).
Proof. exact (fun_ext (fun x : _110927 => @lem4826021 _110927 t u x)). Qed.
Lemma lem4826023 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4826024 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term86 _110927 t u) = (term133 _110927 t u).
Proof. exact (MK_COMB (@lem4826023 _110927) (@lem4826022 _110927 t u)). Qed.
Lemma lem4826025 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4826026 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term75 _110927 t u s) = (term134 _110927 t u s).
Proof. exact (MK_COMB (@lem4826025) (@lem4826014 _110927 t u s)). Qed.
Lemma lem4826027 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term87 _110927 s t u) = (term135 _110927 s t u).
Proof. exact (MK_COMB (@lem4826026 _110927 t u s) (@lem4826024 _110927 t u)). Qed.
Lemma lem4826029 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4826030 {_110927 : Type'} (P : _110927 -> Prop) (Q : _110927 -> Prop) : (term136 _110927 P Q) = (term137 _110927 P Q).
Proof. exact (@lem4826029 _110927 P Q). Qed.
Lemma lem4826031 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term138 _110927 t u s) = (term139 _110927 t u s).
Proof. exact (@lem4826030 _110927 (term140 _110927 t u s) (term141 _110927 t u s)). Qed.
Lemma lem4826032 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : (term142 _110927 t u s x) = (term143 _110927 t u s x).
Proof. exact (eq_refl (term142 _110927 t u s x)). Qed.
Lemma lem4826033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4826034 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : (term144 _110927 t u s x) = (term126 _110927 t u s x).
Proof. exact (MK_COMB (@lem4826033) (@lem4826032 _110927 t u s x)). Qed.
Lemma lem4826035 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : (term145 _110927 t u s x) = (term125 _110927 t u s x).
Proof. exact (eq_refl (term145 _110927 t u s x)). Qed.
Lemma lem4826036 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : (term146 _110927 t u s x) = (term128 _110927 t u s x).
Proof. exact (MK_COMB (@lem4826034 _110927 t u s x) (@lem4826035 _110927 t u s x)). Qed.
Lemma lem4826037 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term147 _110927 t u s) = (term129 _110927 t u s).
Proof. exact (fun_ext (fun x : _110927 => @lem4826036 _110927 t u s x)). Qed.
Lemma lem4826038 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4826039 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term138 _110927 t u s) = (term130 _110927 t u s).
Proof. exact (MK_COMB (@lem4826038 _110927) (@lem4826037 _110927 t u s)). Qed.
Lemma lem4826040 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4826041 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term148 _110927 t u s) = (term149 _110927 t u s).
Proof. exact (MK_COMB (@lem4826040) (@lem4826039 _110927 t u s)). Qed.
Lemma lem4826042 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : (term142 _110927 t u s x) = (term143 _110927 t u s x).
Proof. exact (eq_refl (term142 _110927 t u s x)). Qed.
Lemma lem4826043 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term150 _110927 t u s) = (term140 _110927 t u s).
Proof. exact (fun_ext (fun x : _110927 => @lem4826042 _110927 t u s x)). Qed.
Lemma lem4826044 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4826045 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term151 _110927 t u s) = (term152 _110927 t u s).
Proof. exact (MK_COMB (@lem4826044 _110927) (@lem4826043 _110927 t u s)). Qed.
Lemma lem4826046 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4826047 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term153 _110927 t u s) = (term154 _110927 t u s).
Proof. exact (MK_COMB (@lem4826046) (@lem4826045 _110927 t u s)). Qed.
Lemma lem4826048 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : (term145 _110927 t u s x) = (term125 _110927 t u s x).
Proof. exact (eq_refl (term145 _110927 t u s x)). Qed.
Lemma lem4826049 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term155 _110927 t u s) = (term141 _110927 t u s).
Proof. exact (fun_ext (fun x : _110927 => @lem4826048 _110927 t u s x)). Qed.
Lemma lem4826050 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4826051 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term156 _110927 t u s) = (term157 _110927 t u s).
Proof. exact (MK_COMB (@lem4826050 _110927) (@lem4826049 _110927 t u s)). Qed.
Lemma lem4826052 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term139 _110927 t u s) = (term158 _110927 t u s).
Proof. exact (MK_COMB (@lem4826047 _110927 t u s) (@lem4826051 _110927 t u s)). Qed.
Lemma lem4826053 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : ((term138 _110927 t u s) = (term139 _110927 t u s)) = ((term130 _110927 t u s) = (term158 _110927 t u s)).
Proof. exact (MK_COMB (@lem4826041 _110927 t u s) (@lem4826052 _110927 t u s)). Qed.
Lemma lem4826054 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term130 _110927 t u s) = (term158 _110927 t u s).
Proof. exact (EQ_MP (@lem4826053 _110927 t u s) (@lem4826031 _110927 t u s)). Qed.
Lemma lem4826135 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4826136 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term134 _110927 t u s) = (term159 _110927 t u s).
Proof. exact (MK_COMB (@lem4826135) (@lem4826054 _110927 t u s)). Qed.
Lemma lem4826185 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term133 _110927 t u) = (term133 _110927 t u).
Proof. exact (eq_refl (term133 _110927 t u)). Qed.
Lemma lem4826188 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term135 _110927 s t u) = (term160 _110927 s t u).
Proof. exact (MK_COMB (@lem4826136 _110927 t u s) (@lem4826185 _110927 t u)). Qed.
Lemma lem4826189 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term87 _110927 s t u) = (term160 _110927 s t u).
Proof. exact (TRANS (@lem4826027 _110927 s t u) (@lem4826188 _110927 s t u)). Qed.
Lemma lem4826190 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term160 _110927 s t u.
Proof. exact (EQ_MP (@lem4826189 _110927 s t u) (@lem4825981 _110927 s t u h1)). Qed.
Lemma lem4826196 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) : (term161 _110927 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem4826198 {_110927 : Type'} (s : _110927 -> Prop) (x : _110927) : (term162 _110927 s x) = (term162 _110927 s x).
Proof. exact (eq_refl (term162 _110927 s x)). Qed.
Lemma lem4826199 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (x : _110927) : (term163 _110927 s t x) = (term164 _110927 s t x).
Proof. exact (MK_COMB (@lem4826198 _110927 s x) (@lem4826196 _110927 t x)). Qed.
Lemma lem4826200 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (x : _110927) : (term165 _110927 s t x) = (term163 _110927 s t x).
Proof. exact (@lem17045 (s x) (term90 _110927 t x)). Qed.
Lemma lem4826201 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (x : _110927) : (term165 _110927 s t x) = (term164 _110927 s t x).
Proof. exact (TRANS (@lem4826200 _110927 s t x) (@lem4826199 _110927 s t x)). Qed.
Lemma lem4826206 {_110927 : Type'} (u : _110927 -> Prop) (x : _110927) : (u x) = (u x).
Proof. exact (eq_refl (u x)). Qed.
Lemma lem4826207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4826208 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (x : _110927) : (term166 _110927 s t x) = (term167 _110927 s t x).
Proof. exact (MK_COMB (@lem4826207) (@lem4826201 _110927 s t x)). Qed.
Lemma lem4826209 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term168 _110927 s t u x) = (term169 _110927 s t u x).
Proof. exact (MK_COMB (@lem4826208 _110927 s t x) (@lem4826206 _110927 u x)). Qed.
Lemma lem4826214 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term170 _110927 s t u x) = (term170 _110927 s t u x).
Proof. exact (eq_refl (term170 _110927 s t u x)). Qed.
Lemma lem4826215 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term171 _110927 s t u x) = (term172 _110927 s t u x).
Proof. exact (MK_COMB (@lem4826214 _110927 s t u x) (@lem4826209 _110927 s t u x)). Qed.
Lemma lem4826216 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term119 _110927 s t u x) = (term171 _110927 s t u x).
Proof. exact (@lem17646 (term91 _110927 s t x) (u x)). Qed.
Lemma lem4826221 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term119 _110927 s t u x) = (term172 _110927 s t u x).
Proof. exact (TRANS (@lem4826216 _110927 s t u x) (@lem4826215 _110927 s t u x)). Qed.
Lemma lem4826235 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term131 _110927 t u x) = (term131 _110927 t u x).
Proof. exact (eq_refl (term131 _110927 t u x)). Qed.
Lemma lem4826236 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term132 _110927 t u) = (term132 _110927 t u).
Proof. exact (fun_ext (fun x : _110927 => @lem4826235 _110927 t u x)). Qed.
Lemma lem4826237 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4826238 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term133 _110927 t u) = (term133 _110927 t u).
Proof. exact (MK_COMB (@lem4826237 _110927) (@lem4826236 _110927 t u)). Qed.
Lemma lem4826257 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : (term125 _110927 t u s x) = (term125 _110927 t u s x).
Proof. exact (eq_refl (term125 _110927 t u s x)). Qed.
Lemma lem4826258 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term141 _110927 t u s) = (term141 _110927 t u s).
Proof. exact (fun_ext (fun x : _110927 => @lem4826257 _110927 t u s x)). Qed.
Lemma lem4826259 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4826260 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term157 _110927 t u s) = (term157 _110927 t u s).
Proof. exact (MK_COMB (@lem4826259 _110927) (@lem4826258 _110927 t u s)). Qed.
Lemma lem4826277 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : (term143 _110927 t u s x) = (term143 _110927 t u s x).
Proof. exact (eq_refl (term143 _110927 t u s x)). Qed.
Lemma lem4826278 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term140 _110927 t u s) = (term140 _110927 t u s).
Proof. exact (fun_ext (fun x : _110927 => @lem4826277 _110927 t u s x)). Qed.
Lemma lem4826279 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4826280 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term152 _110927 t u s) = (term152 _110927 t u s).
Proof. exact (MK_COMB (@lem4826279 _110927) (@lem4826278 _110927 t u s)). Qed.
Lemma lem4826281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4826282 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term154 _110927 t u s) = (term154 _110927 t u s).
Proof. exact (MK_COMB (@lem4826281) (@lem4826280 _110927 t u s)). Qed.
Lemma lem4826283 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term158 _110927 t u s) = (term158 _110927 t u s).
Proof. exact (MK_COMB (@lem4826282 _110927 t u s) (@lem4826260 _110927 t u s)). Qed.
Lemma lem4826284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4826285 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term159 _110927 t u s) = (term159 _110927 t u s).
Proof. exact (MK_COMB (@lem4826284) (@lem4826283 _110927 t u s)). Qed.
Lemma lem4826286 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term160 _110927 s t u) = (term160 _110927 s t u).
Proof. exact (MK_COMB (@lem4826285 _110927 t u s) (@lem4826238 _110927 t u)). Qed.
Lemma lem4826287 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term160 _110927 s t u.
Proof. exact (EQ_MP (@lem4826286 _110927 s t u) (@lem4826190 _110927 s t u h1)). Qed.
Lemma lem4826327 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term119 _110927 s t u x) : term172 _110927 s t u x.
Proof. exact (EQ_MP (@lem4826221 _110927 s t u x) (@lem4825986 _110927 s t u x h1)). Qed.
Lemma lem4826328 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term133 _110927 t u.
Proof. exact (proj2 (@lem4826287 _110927 s t u h1)). Qed.
Lemma lem4826329 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term158 _110927 t u s.
Proof. exact (proj1 (@lem4826287 _110927 s t u h1)). Qed.
Lemma lem4826330 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term157 _110927 t u s.
Proof. exact (proj2 (@lem4826329 _110927 s t u h1)). Qed.
Lemma lem4826331 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term152 _110927 t u s.
Proof. exact (proj1 (@lem4826329 _110927 s t u h1)). Qed.
Lemma lem4826332 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term173 _110927 s t u x) : term173 _110927 s t u x.
Proof. exact (h1). Qed.
Lemma lem4826333 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term169 _110927 s t u x) : term169 _110927 s t u x.
Proof. exact (h1). Qed.
Lemma lem4826335 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term173 _110927 s t u x) : term91 _110927 s t x.
Proof. exact (proj1 (@lem4826332 _110927 s t u x h1)). Qed.
Lemma lem4826339 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term169 _110927 s t u x) : term164 _110927 s t x.
Proof. exact (proj1 (@lem4826333 _110927 s t u x h1)). Qed.
Lemma lem4826368 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : (term143 _110927 t u s x) = (term143 _110927 t u s x).
Proof. exact (eq_refl (term143 _110927 t u s x)). Qed.
Lemma lem4826369 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term140 _110927 t u s) = (term140 _110927 t u s).
Proof. exact (fun_ext (fun x : _110927 => @lem4826368 _110927 t u s x)). Qed.
Lemma lem4826370 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4826372 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term152 _110927 t u s) = (term152 _110927 t u s).
Proof. exact (MK_COMB (@lem4826370 _110927) (@lem4826369 _110927 t u s)). Qed.
Lemma lem4826373 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term152 _110927 t u s.
Proof. exact (EQ_MP (@lem4826372 _110927 t u s) (@lem4826331 _110927 s t u h1)). Qed.
Lemma lem4826458 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (x : _110927) : (term125 _110927 t u s x) = (term174 _110927 t u s x).
Proof. exact (@lem19699 (term90 _110927 t x) (term90 _110927 u x) (s x)). Qed.
Lemma lem4826459 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term141 _110927 t u s) = (term175 _110927 t u s).
Proof. exact (fun_ext (fun x : _110927 => @lem4826458 _110927 t u s x)). Qed.
Lemma lem4826460 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4826462 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : (term157 _110927 t u s) = (term176 _110927 t u s).
Proof. exact (MK_COMB (@lem4826460 _110927) (@lem4826459 _110927 t u s)). Qed.
Lemma lem4826463 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term176 _110927 t u s.
Proof. exact (EQ_MP (@lem4826462 _110927 t u s) (@lem4826330 _110927 s t u h1)). Qed.
Lemma lem4826471 {_110927 : Type'} (s : _110927 -> Prop) (x : _110927) (h1 : term90 _110927 s x) : term90 _110927 s x.
Proof. exact (h1). Qed.
Lemma lem4826479 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) : (term131 _110927 t u x) = (term131 _110927 t u x).
Proof. exact (eq_refl (term131 _110927 t u x)). Qed.
Lemma lem4826480 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term132 _110927 t u) = (term132 _110927 t u).
Proof. exact (fun_ext (fun x : _110927 => @lem4826479 _110927 t u x)). Qed.
Lemma lem4826481 {_110927 : Type'} : (@all _110927) = (@all _110927).
Proof. exact (eq_refl (@all _110927)). Qed.
Lemma lem4826483 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term133 _110927 t u) = (term133 _110927 t u).
Proof. exact (MK_COMB (@lem4826481 _110927) (@lem4826480 _110927 t u)). Qed.
Lemma lem4826484 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term133 _110927 t u.
Proof. exact (EQ_MP (@lem4826483 _110927 t u) (@lem4826328 _110927 s t u h1)). Qed.
Lemma lem4826534 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4826538 {_110927 : Type'} (_59816 : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term142 _110927 t u s _59816.
Proof. exact (@lem4826373 _110927 s t u h1 _59816). Qed.
Lemma lem4826539 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (_59816 : _110927) : (term142 _110927 t u s _59816) = (term143 _110927 t u s _59816).
Proof. exact (eq_refl (term142 _110927 t u s _59816)). Qed.
Lemma lem4826540 {_110927 : Type'} (_59816 : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term143 _110927 t u s _59816.
Proof. exact (EQ_MP (@lem4826539 _110927 t u s _59816) (@lem4826538 _110927 _59816 s t u h1)). Qed.
Lemma lem4826550 {_110927 : Type'} (_59820 : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term177 _110927 t u s _59820.
Proof. exact (@lem4826463 _110927 s t u h1 _59820). Qed.
Lemma lem4826551 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (_59820 : _110927) : (term177 _110927 t u s _59820) = (term174 _110927 t u s _59820).
Proof. exact (eq_refl (term177 _110927 t u s _59820)). Qed.
Lemma lem4826552 {_110927 : Type'} (_59820 : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term174 _110927 t u s _59820.
Proof. exact (EQ_MP (@lem4826551 _110927 t u s _59820) (@lem4826550 _110927 _59820 s t u h1)). Qed.
Lemma lem4826553 {_110927 : Type'} (_59821 : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term178 _110927 t u _59821.
Proof. exact (@lem4826484 _110927 s t u h1 _59821). Qed.
Lemma lem4826554 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (_59821 : _110927) : (term178 _110927 t u _59821) = (term131 _110927 t u _59821).
Proof. exact (eq_refl (term178 _110927 t u _59821)). Qed.
Lemma lem4826584 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) (_59816 : _110927) : (term143 _110927 t u s _59816) = (term179 _110927 t u s _59816).
Proof. exact (@lem4825585 (t _59816) (u _59816) (term90 _110927 s _59816)). Qed.
Lemma lem4826585 {_110927 : Type'} (_59816 : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term179 _110927 t u s _59816.
Proof. exact (EQ_MP (@lem4826584 _110927 t u s _59816) (@lem4826540 _110927 _59816 s t u h1)). Qed.
Lemma lem4826591 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term173 _110927 s t u x) : term90 _110927 t x.
Proof. exact (proj2 (@lem4826335 _110927 s t u x h1)). Qed.
Lemma lem4826625 {_110927 : Type'} (s : _110927 -> Prop) (x : _110927) (h1 : term90 _110927 s x) : term90 _110927 s x.
Proof. exact (h1). Qed.
Lemma lem4826637 {_110927 : Type'} (_59820 : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term164 _110927 u s _59820.
Proof. exact (proj2 (@lem4826552 _110927 _59820 s t u h1)). Qed.
Lemma lem4826643 {_110927 : Type'} (_59821 : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term131 _110927 t u _59821.
Proof. exact (EQ_MP (@lem4826554 _110927 t u _59821) (@lem4826553 _110927 _59821 s t u h1)). Qed.
Lemma lem4826659 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4826673 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term173 _110927 s t u x) : term90 _110927 u x.
Proof. exact (proj2 (@lem4826332 _110927 s t u x h1)). Qed.
Lemma lem4826674 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term173 _110927 s t u x) : term180 _110927 u x.
Proof. exact (fun h0 : u x => @lem4826673 _110927 s t u x h1). Qed.
Lemma lem4826676 (p : Prop) : (term181 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4826677 {_110927 : Type'} (u : _110927 -> Prop) (x : _110927) : (term180 _110927 u x) = (term90 _110927 u x).
Proof. exact (@lem4826676 (u x)). Qed.
Lemma lem4826678 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term173 _110927 s t u x) : term90 _110927 u x.
Proof. exact (EQ_MP (@lem4826677 _110927 u x) (@lem4826674 _110927 s t u x h1)). Qed.
Lemma lem4826680 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term173 _110927 s t u x) : s x.
Proof. exact (proj1 (@lem4826335 _110927 s t u x h1)). Qed.
Lemma lem4826681 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term173 _110927 s t u x) : term182 _110927 s x.
Proof. exact (fun h0 : term90 _110927 s x => @lem4826680 _110927 s t u x h1). Qed.
Lemma lem4826683 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4826684 {_110927 : Type'} (s : _110927 -> Prop) (x : _110927) : (term182 _110927 s x) = (s x).
Proof. exact (@lem4826683 (s x)). Qed.
Lemma lem4826685 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term173 _110927 s t u x) : s x.
Proof. exact (EQ_MP (@lem4826684 _110927 s x) (@lem4826681 _110927 s t u x h1)). Qed.
Lemma lem4826687 (b : Prop) (a : Prop) : (a \/ b) = (term184 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4826688 {_110927 : Type'} (u : _110927 -> Prop) (s : _110927 -> Prop) (t : _110927 -> Prop) (_59816 : _110927) : (term179 _110927 t u s _59816) = (term185 _110927 u s t _59816).
Proof. exact (@lem4826687 (term186 _110927 u s _59816) (t _59816)). Qed.
Lemma lem4826690 (a : Prop) (b : Prop) : (term187 a b) = (term188 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4826691 {_110927 : Type'} (u : _110927 -> Prop) (s : _110927 -> Prop) (_59816 : _110927) : (term189 _110927 u s _59816) = (term190 _110927 u s _59816).
Proof. exact (@lem4826690 (u _59816) (term90 _110927 s _59816)). Qed.
Lemma lem4826693 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4826694 {_110927 : Type'} (s : _110927 -> Prop) (_59816 : _110927) : (term161 _110927 s _59816) = (s _59816).
Proof. exact (@lem4826693 (s _59816)). Qed.
Lemma lem4826695 {_110927 : Type'} (u : _110927 -> Prop) (_59816 : _110927) : (term191 _110927 u _59816) = (term191 _110927 u _59816).
Proof. exact (eq_refl (term191 _110927 u _59816)). Qed.
Lemma lem4826696 {_110927 : Type'} (u : _110927 -> Prop) (s : _110927 -> Prop) (_59816 : _110927) : (term190 _110927 u s _59816) = (term192 _110927 u s _59816).
Proof. exact (MK_COMB (@lem4826695 _110927 u _59816) (@lem4826694 _110927 s _59816)). Qed.
Lemma lem4826697 {_110927 : Type'} (u : _110927 -> Prop) (s : _110927 -> Prop) (_59816 : _110927) : (term189 _110927 u s _59816) = (term192 _110927 u s _59816).
Proof. exact (TRANS (@lem4826691 _110927 u s _59816) (@lem4826696 _110927 u s _59816)). Qed.
Lemma lem4826698 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4826699 {_110927 : Type'} (u : _110927 -> Prop) (s : _110927 -> Prop) (_59816 : _110927) : (term193 _110927 u s _59816) = (term194 _110927 u s _59816).
Proof. exact (MK_COMB (@lem4826698) (@lem4826697 _110927 u s _59816)). Qed.
Lemma lem4826700 {_110927 : Type'} (t : _110927 -> Prop) (_59816 : _110927) : (t _59816) = (t _59816).
Proof. exact (eq_refl (t _59816)). Qed.
Lemma lem4826701 {_110927 : Type'} (u : _110927 -> Prop) (s : _110927 -> Prop) (t : _110927 -> Prop) (_59816 : _110927) : (term185 _110927 u s t _59816) = (term195 _110927 u s t _59816).
Proof. exact (MK_COMB (@lem4826699 _110927 u s _59816) (@lem4826700 _110927 t _59816)). Qed.
Lemma lem4826702 {_110927 : Type'} (u : _110927 -> Prop) (s : _110927 -> Prop) (t : _110927 -> Prop) (_59816 : _110927) : (term179 _110927 t u s _59816) = (term195 _110927 u s t _59816).
Proof. exact (TRANS (@lem4826688 _110927 u s t _59816) (@lem4826701 _110927 u s t _59816)). Qed.
Lemma lem4826704 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term173 _110927 s t u x) : term192 _110927 u s x.
Proof. exact (conj (@lem4826678 _110927 s t u x h1) (@lem4826685 _110927 s t u x h1)). Qed.
Lemma lem4826706 {_110927 : Type'} (_59816 : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term195 _110927 u s t _59816.
Proof. exact (EQ_MP (@lem4826702 _110927 u s t _59816) (@lem4826585 _110927 _59816 s t u h1)). Qed.
Lemma lem4826707 {_110927 : Type'} (_59816 : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term195 _110927 u s t _59816.
Proof. exact (@lem4826706 _110927 _59816 s t u h1). Qed.
Lemma lem4826708 {_110927 : Type'} (x : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term195 _110927 u s t x.
Proof. exact (@lem4826707 _110927 x s t u h1). Qed.
Lemma lem4826711 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term87 _110927 s t u) (h2 : term173 _110927 s t u x) : t x.
Proof. exact (@lem4826708 _110927 x s t u h1 (@lem4826704 _110927 s t u x h2)). Qed.
Lemma lem4826712 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term87 _110927 s t u) (h2 : term173 _110927 s t u x) : term182 _110927 t x.
Proof. exact (fun h0 : term90 _110927 t x => @lem4826711 _110927 s t u x h1 h2). Qed.
Lemma lem4826714 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4826715 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) : (term182 _110927 t x) = (t x).
Proof. exact (@lem4826714 (t x)). Qed.
Lemma lem4826716 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term87 _110927 s t u) (h2 : term173 _110927 s t u x) : t x.
Proof. exact (EQ_MP (@lem4826715 _110927 t x) (@lem4826712 _110927 s t u x h1 h2)). Qed.
Lemma lem4826719 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4826721 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) : (term90 _110927 t x) = (term196 _110927 t x).
Proof. exact (@lem4826719 (t x)). Qed.
Lemma lem4826724 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term173 _110927 s t u x) : term196 _110927 t x.
Proof. exact (EQ_MP (@lem4826721 _110927 t x) (@lem4826591 _110927 s t u x h1)). Qed.
Lemma lem4826727 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term87 _110927 s t u) (h2 : term173 _110927 s t u x) : False.
Proof. exact (@lem4826724 _110927 s t u x h2 (@lem4826716 _110927 s t u x h1 h2)). Qed.
Lemma lem4826728 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term87 _110927 s t u) (h2 : term173 _110927 s t u x) : term197.
Proof. exact (fun h0 : ~ False => @lem4826727 _110927 s t u x h1 h2). Qed.
Lemma lem4826730 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4826731 : term197 = False.
Proof. exact (@lem4826730 False). Qed.
Lemma lem4826732 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term87 _110927 s t u) (h2 : term173 _110927 s t u x) : False.
Proof. exact (EQ_MP (@lem4826731) (@lem4826728 _110927 s t u x h1 h2)). Qed.
Lemma lem4826734 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term169 _110927 s t u x) : u x.
Proof. exact (proj2 (@lem4826333 _110927 s t u x h1)). Qed.
Lemma lem4826735 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term169 _110927 s t u x) : term182 _110927 u x.
Proof. exact (fun h0 : term90 _110927 u x => @lem4826734 _110927 s t u x h1). Qed.
Lemma lem4826737 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4826738 {_110927 : Type'} (u : _110927 -> Prop) (x : _110927) : (term182 _110927 u x) = (u x).
Proof. exact (@lem4826737 (u x)). Qed.
Lemma lem4826739 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term169 _110927 s t u x) : u x.
Proof. exact (EQ_MP (@lem4826738 _110927 u x) (@lem4826735 _110927 s t u x h1)). Qed.
Lemma lem4826745 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4826746 {_110927 : Type'} (s : _110927 -> Prop) (u : _110927 -> Prop) (_59820 : _110927) : (term164 _110927 u s _59820) = (term186 _110927 s u _59820).
Proof. exact (@lem4826745 (s _59820) (term90 _110927 u _59820)). Qed.
Lemma lem4826752 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4826753 {_110927 : Type'} (s : _110927 -> Prop) (u : _110927 -> Prop) (_59820 : _110927) : (term198 _110927 u s _59820) = (term199 _110927 s u _59820).
Proof. exact (MK_COMB (@lem4826752) (@lem4826746 _110927 s u _59820)). Qed.
Lemma lem4826759 {_110927 : Type'} (s : _110927 -> Prop) (u : _110927 -> Prop) (_59820 : _110927) : (term186 _110927 s u _59820) = (term186 _110927 s u _59820).
Proof. exact (eq_refl (term186 _110927 s u _59820)). Qed.
Lemma lem4826760 {_110927 : Type'} (s : _110927 -> Prop) (u : _110927 -> Prop) (_59820 : _110927) : ((term164 _110927 u s _59820) = (term186 _110927 s u _59820)) = ((term186 _110927 s u _59820) = (term186 _110927 s u _59820)).
Proof. exact (MK_COMB (@lem4826753 _110927 s u _59820) (@lem4826759 _110927 s u _59820)). Qed.
Lemma lem4826762 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4826763 (x : Prop) : (x = x) = True.
Proof. exact (@lem4826762 Prop x). Qed.
Lemma lem4826764 {_110927 : Type'} (s : _110927 -> Prop) (u : _110927 -> Prop) (_59820 : _110927) : ((term186 _110927 s u _59820) = (term186 _110927 s u _59820)) = True.
Proof. exact (@lem4826763 (term186 _110927 s u _59820)). Qed.
Lemma lem4826765 {_110927 : Type'} (s : _110927 -> Prop) (u : _110927 -> Prop) (_59820 : _110927) : ((term164 _110927 u s _59820) = (term186 _110927 s u _59820)) = True.
Proof. exact (TRANS (@lem4826760 _110927 s u _59820) (@lem4826764 _110927 s u _59820)). Qed.
Lemma lem4826766 {_110927 : Type'} (s : _110927 -> Prop) (u : _110927 -> Prop) (_59820 : _110927) : True = ((term164 _110927 u s _59820) = (term186 _110927 s u _59820)).
Proof. exact (SYM (@lem4826765 _110927 s u _59820)). Qed.
Lemma lem4826767 {_110927 : Type'} (s : _110927 -> Prop) (u : _110927 -> Prop) (_59820 : _110927) : (term164 _110927 u s _59820) = (term186 _110927 s u _59820).
Proof. exact (EQ_MP (@lem4826766 _110927 s u _59820) (@lem0)). Qed.
Lemma lem4826768 {_110927 : Type'} (_59820 : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term186 _110927 s u _59820.
Proof. exact (EQ_MP (@lem4826767 _110927 s u _59820) (@lem4826637 _110927 _59820 s t u h1)). Qed.
Lemma lem4826770 (b : Prop) (a : Prop) : (a \/ b) = (term184 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4826771 {_110927 : Type'} (u : _110927 -> Prop) (s : _110927 -> Prop) (_59820 : _110927) : (term186 _110927 s u _59820) = (term200 _110927 u s _59820).
Proof. exact (@lem4826770 (term90 _110927 u _59820) (s _59820)). Qed.
Lemma lem4826773 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4826774 {_110927 : Type'} (u : _110927 -> Prop) (_59820 : _110927) : (term161 _110927 u _59820) = (u _59820).
Proof. exact (@lem4826773 (u _59820)). Qed.
Lemma lem4826775 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4826776 {_110927 : Type'} (u : _110927 -> Prop) (_59820 : _110927) : (term201 _110927 u _59820) = (term202 _110927 u _59820).
Proof. exact (MK_COMB (@lem4826775) (@lem4826774 _110927 u _59820)). Qed.
Lemma lem4826777 {_110927 : Type'} (s : _110927 -> Prop) (_59820 : _110927) : (s _59820) = (s _59820).
Proof. exact (eq_refl (s _59820)). Qed.
Lemma lem4826778 {_110927 : Type'} (u : _110927 -> Prop) (s : _110927 -> Prop) (_59820 : _110927) : (term200 _110927 u s _59820) = (term203 _110927 u s _59820).
Proof. exact (MK_COMB (@lem4826776 _110927 u _59820) (@lem4826777 _110927 s _59820)). Qed.
Lemma lem4826779 {_110927 : Type'} (u : _110927 -> Prop) (s : _110927 -> Prop) (_59820 : _110927) : (term186 _110927 s u _59820) = (term203 _110927 u s _59820).
Proof. exact (TRANS (@lem4826771 _110927 u s _59820) (@lem4826778 _110927 u s _59820)). Qed.
Lemma lem4826782 {_110927 : Type'} (_59820 : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term203 _110927 u s _59820.
Proof. exact (EQ_MP (@lem4826779 _110927 u s _59820) (@lem4826768 _110927 _59820 s t u h1)). Qed.
Lemma lem4826783 {_110927 : Type'} (_59820 : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term203 _110927 u s _59820.
Proof. exact (@lem4826782 _110927 _59820 s t u h1). Qed.
Lemma lem4826784 {_110927 : Type'} (x : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term203 _110927 u s x.
Proof. exact (@lem4826783 _110927 x s t u h1). Qed.
Lemma lem4826787 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term87 _110927 s t u) (h2 : term169 _110927 s t u x) : s x.
Proof. exact (@lem4826784 _110927 x s t u h1 (@lem4826739 _110927 s t u x h2)). Qed.
Lemma lem4826788 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term87 _110927 s t u) (h2 : term169 _110927 s t u x) : term182 _110927 s x.
Proof. exact (fun h0 : term90 _110927 s x => @lem4826787 _110927 s t u x h1 h2). Qed.
Lemma lem4826790 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4826791 {_110927 : Type'} (s : _110927 -> Prop) (x : _110927) : (term182 _110927 s x) = (s x).
Proof. exact (@lem4826790 (s x)). Qed.
Lemma lem4826792 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term87 _110927 s t u) (h2 : term169 _110927 s t u x) : s x.
Proof. exact (EQ_MP (@lem4826791 _110927 s x) (@lem4826788 _110927 s t u x h1 h2)). Qed.
Lemma lem4826795 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4826797 {_110927 : Type'} (s : _110927 -> Prop) (x : _110927) : (term90 _110927 s x) = (term196 _110927 s x).
Proof. exact (@lem4826795 (s x)). Qed.
Lemma lem4826800 {_110927 : Type'} (s : _110927 -> Prop) (x : _110927) (h1 : term90 _110927 s x) : term196 _110927 s x.
Proof. exact (EQ_MP (@lem4826797 _110927 s x) (@lem4826625 _110927 s x h1)). Qed.
Lemma lem4826803 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term90 _110927 s x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : False.
Proof. exact (@lem4826800 _110927 s x h1 (@lem4826792 _110927 s t u x h2 h3)). Qed.
Lemma lem4826804 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term90 _110927 s x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : term197.
Proof. exact (fun h0 : ~ False => @lem4826803 _110927 s t u x h1 h2 h3). Qed.
Lemma lem4826806 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4826807 : term197 = False.
Proof. exact (@lem4826806 False). Qed.
Lemma lem4826808 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term90 _110927 s x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : False.
Proof. exact (EQ_MP (@lem4826807) (@lem4826804 _110927 s t u x h1 h2 h3)). Qed.
Lemma lem4826810 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4826811 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) (h1 : t x) : term182 _110927 t x.
Proof. exact (fun h0 : term90 _110927 t x => @lem4826810 _110927 t x h1). Qed.
Lemma lem4826813 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4826814 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) : (term182 _110927 t x) = (t x).
Proof. exact (@lem4826813 (t x)). Qed.
Lemma lem4826815 {_110927 : Type'} (t : _110927 -> Prop) (x : _110927) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem4826814 _110927 t x) (@lem4826811 _110927 t x h1)). Qed.
Lemma lem4826817 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term169 _110927 s t u x) : u x.
Proof. exact (proj2 (@lem4826333 _110927 s t u x h1)). Qed.
Lemma lem4826818 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term169 _110927 s t u x) : term182 _110927 u x.
Proof. exact (fun h0 : term90 _110927 u x => @lem4826817 _110927 s t u x h1). Qed.
Lemma lem4826820 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4826821 {_110927 : Type'} (u : _110927 -> Prop) (x : _110927) : (term182 _110927 u x) = (u x).
Proof. exact (@lem4826820 (u x)). Qed.
Lemma lem4826822 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term169 _110927 s t u x) : u x.
Proof. exact (EQ_MP (@lem4826821 _110927 u x) (@lem4826818 _110927 s t u x h1)). Qed.
Lemma lem4826824 (a : Prop) (b : Prop) : (term204 a b) = (term205 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4826825 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (_59821 : _110927) : (term131 _110927 t u _59821) = (term83 _110927 t u _59821).
Proof. exact (@lem4826824 (t _59821) (u _59821)). Qed.
Lemma lem4826827 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4826828 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (_59821 : _110927) : (term83 _110927 t u _59821) = (term206 _110927 t u _59821).
Proof. exact (@lem4826827 (term80 _110927 t u _59821)). Qed.
Lemma lem4826829 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (_59821 : _110927) : (term131 _110927 t u _59821) = (term206 _110927 t u _59821).
Proof. exact (TRANS (@lem4826825 _110927 t u _59821) (@lem4826828 _110927 t u _59821)). Qed.
Lemma lem4826831 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : t x) (h2 : term169 _110927 s t u x) : term80 _110927 t u x.
Proof. exact (conj (@lem4826815 _110927 t x h1) (@lem4826822 _110927 s t u x h2)). Qed.
Lemma lem4826833 {_110927 : Type'} (_59821 : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term206 _110927 t u _59821.
Proof. exact (EQ_MP (@lem4826829 _110927 t u _59821) (@lem4826643 _110927 _59821 s t u h1)). Qed.
Lemma lem4826834 {_110927 : Type'} (_59821 : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term206 _110927 t u _59821.
Proof. exact (@lem4826833 _110927 _59821 s t u h1). Qed.
Lemma lem4826835 {_110927 : Type'} (x : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term206 _110927 t u x.
Proof. exact (@lem4826834 _110927 x s t u h1). Qed.
Lemma lem4826838 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : t x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : False.
Proof. exact (@lem4826835 _110927 x s t u h2 (@lem4826831 _110927 s t u x h1 h3)). Qed.
Lemma lem4826839 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : t x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : term197.
Proof. exact (fun h0 : ~ False => @lem4826838 _110927 s t u x h1 h2 h3). Qed.
Lemma lem4826841 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4826842 : term197 = False.
Proof. exact (@lem4826841 False). Qed.
Lemma lem4826843 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : t x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : False.
Proof. exact (EQ_MP (@lem4826842) (@lem4826839 _110927 s t u x h1 h2 h3)). Qed.
Lemma lem4826844 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : t x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem4826843 _110927 s t u x h1 h2 h3) (fun h4 : False => @lem4826659 _110927 t x h1)). Qed.
Lemma lem4826845 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : t x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : False.
Proof. exact (EQ_MP (@lem4826844 _110927 s t u x h1 h2 h3) (@lem4826659 _110927 t x h1)). Qed.
Lemma lem4826846 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term90 _110927 s x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : (term90 _110927 s x) = False.
Proof. exact (prop_ext (fun h4 : term90 _110927 s x => @lem4826808 _110927 s t u x h1 h2 h3) (fun h4 : False => @lem4826625 _110927 s x h1)). Qed.
Lemma lem4826847 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term90 _110927 s x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : False.
Proof. exact (EQ_MP (@lem4826846 _110927 s t u x h1 h2 h3) (@lem4826625 _110927 s x h1)). Qed.
Lemma lem4826848 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : t x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem4826845 _110927 s t u x h1 h2 h3) (fun h4 : False => @lem4826534 _110927 t x h1)). Qed.
Lemma lem4826849 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : t x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : False.
Proof. exact (EQ_MP (@lem4826848 _110927 s t u x h1 h2 h3) (@lem4826534 _110927 t x h1)). Qed.
Lemma lem4826850 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term90 _110927 s x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : (term90 _110927 s x) = False.
Proof. exact (prop_ext (fun h4 : term90 _110927 s x => @lem4826847 _110927 s t u x h1 h2 h3) (fun h4 : False => @lem4826471 _110927 s x h1)). Qed.
Lemma lem4826851 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term90 _110927 s x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : False.
Proof. exact (EQ_MP (@lem4826850 _110927 s t u x h1 h2 h3) (@lem4826471 _110927 s x h1)). Qed.
Lemma lem4826852 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : t x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem4826849 _110927 s t u x h1 h2 h3) (fun h4 : False => @lem4826534 _110927 t x h1)). Qed.
Lemma lem4826853 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : t x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : False.
Proof. exact (EQ_MP (@lem4826852 _110927 s t u x h1 h2 h3) (@lem4826534 _110927 t x h1)). Qed.
Lemma lem4826854 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term90 _110927 s x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : (term90 _110927 s x) = False.
Proof. exact (prop_ext (fun h4 : term90 _110927 s x => @lem4826851 _110927 s t u x h1 h2 h3) (fun h4 : False => @lem4826471 _110927 s x h1)). Qed.
Lemma lem4826855 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term90 _110927 s x) (h2 : term87 _110927 s t u) (h3 : term169 _110927 s t u x) : False.
Proof. exact (EQ_MP (@lem4826854 _110927 s t u x h1 h2 h3) (@lem4826471 _110927 s x h1)). Qed.
Lemma lem4826856 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (x : _110927) (h1 : term87 _110927 s t u) (h2 : term169 _110927 s t u x) : False.
Proof. exact (or_elim (@lem4826339 _110927 s t u x h2) (fun h0 : term90 _110927 s x => @lem4826855 _110927 s t u x h0 h1 h2) (fun h0 : t x => @lem4826853 _110927 s t u x h0 h1 h2)). Qed.
Lemma lem4826857 {_110927 : Type'} (x : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term119 _110927 s t u x) (h2 : term87 _110927 s t u) : False.
Proof. exact (or_elim (@lem4826327 _110927 s t u x h1) (fun h0 : term173 _110927 s t u x => @lem4826732 _110927 s t u x h2 h0) (fun h0 : term169 _110927 s t u x => @lem4826856 _110927 s t u x h2 h0)). Qed.
Lemma lem4826858 {_110927 : Type'} (x : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term119 _110927 s t u x) (h2 : term87 _110927 s t u) : (term119 _110927 s t u x) = False.
Proof. exact (prop_ext (fun h3 : term119 _110927 s t u x => @lem4826857 _110927 x s t u h1 h2) (fun h3 : False => @lem4825986 _110927 s t u x h1)). Qed.
Lemma lem4826859 {_110927 : Type'} (x : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term119 _110927 s t u x) (h2 : term87 _110927 s t u) : False.
Proof. exact (EQ_MP (@lem4826858 _110927 x s t u h1 h2) (@lem4825986 _110927 s t u x h1)). Qed.
Lemma lem4826860 {_110927 : Type'} (x : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term118 _110927 s t u x.
Proof. exact (fun h0 : term119 _110927 s t u x => @lem4826859 _110927 x s t u h0 h1). Qed.
Lemma lem4826861 {_110927 : Type'} (x : _110927) (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : (term91 _110927 s t x) = (u x).
Proof. exact (EQ_MP (@lem4825985 _110927 s t u x) (@lem4826860 _110927 x s t u h1)). Qed.
Lemma lem4826866 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term87 _110927 s t u) : term96 _110927 s t u.
Proof. exact (fun x : _110927 => @lem4826861 _110927 x s t u h1). Qed.
Lemma lem4826867 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : term97 _110927 s t u.
Proof. exact (fun h0 : term87 _110927 s t u => @lem4826866 _110927 s t u h0). Qed.
Lemma lem4826872 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : term109 _110927 t u.
Proof. exact (fun s : _110927 -> Prop => @lem4826867 _110927 s t u). Qed.
Lemma lem4826877 {_110927 : Type'} (u : _110927 -> Prop) : term113 _110927 u.
Proof. exact (fun t : _110927 -> Prop => @lem4826872 _110927 t u). Qed.
Lemma lem4826882 {_110927 : Type'} : term117 _110927.
Proof. exact (fun u : _110927 -> Prop => @lem4826877 _110927 u). Qed.
Lemma lem4826883 {_110927 : Type'} : term116 _110927.
Proof. exact (EQ_MP (@lem4825980 _110927) (@lem4826882 _110927)). Qed.
Lemma lem4826884 {_110927 : Type'} (u : _110927 -> Prop) : term207 _110927 u.
Proof. exact (@lem4826883 _110927 u). Qed.
Lemma lem4826885 {_110927 : Type'} (u : _110927 -> Prop) : (term207 _110927 u) = (term112 _110927 u).
Proof. exact (eq_refl (term207 _110927 u)). Qed.
Lemma lem4826886 {_110927 : Type'} (u : _110927 -> Prop) : term112 _110927 u.
Proof. exact (EQ_MP (@lem4826885 _110927 u) (@lem4826884 _110927 u)). Qed.
Lemma lem4826887 {_110927 : Type'} (u : _110927 -> Prop) (t : _110927 -> Prop) : term208 _110927 u t.
Proof. exact (@lem4826886 _110927 u t). Qed.
Lemma lem4826888 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : (term208 _110927 u t) = (term108 _110927 t u).
Proof. exact (eq_refl (term208 _110927 u t)). Qed.
Lemma lem4826889 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) : term108 _110927 t u.
Proof. exact (EQ_MP (@lem4826888 _110927 t u) (@lem4826887 _110927 u t)). Qed.
Lemma lem4826890 {_110927 : Type'} (t : _110927 -> Prop) (u : _110927 -> Prop) (s : _110927 -> Prop) : term209 _110927 t u s.
Proof. exact (@lem4826889 _110927 t u s). Qed.
Lemma lem4826891 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : (term209 _110927 t u s) = (term99 _110927 s t u).
Proof. exact (eq_refl (term209 _110927 t u s)). Qed.
Lemma lem4826892 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : term99 _110927 s t u.
Proof. exact (EQ_MP (@lem4826891 _110927 s t u) (@lem4826890 _110927 t u s)). Qed.
Lemma lem4826894 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : term99 _110927 s t u.
Proof. exact (@lem4825813 _110927 s t u (@lem4826892 _110927 s t u)). Qed.
Lemma lem4826895 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term100 _110927 s t u) : False.
Proof. exact (@lem4826894 _110927 s t u (@lem4825797 _110927 s t u h1)). Qed.
Lemma lem4826896 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term100 _110927 s t u) : (term100 _110927 s t u) = False.
Proof. exact (prop_ext (fun h2 : term100 _110927 s t u => @lem4826895 _110927 s t u h1) (fun h2 : False => @lem4825797 _110927 s t u h1)). Qed.
Lemma lem4826897 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term100 _110927 s t u) : False.
Proof. exact (EQ_MP (@lem4826896 _110927 s t u h1) (@lem4825797 _110927 s t u h1)). Qed.
Lemma lem4826898 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : term99 _110927 s t u.
Proof. exact (fun h0 : term100 _110927 s t u => @lem4826897 _110927 s t u h0). Qed.
Lemma lem4826899 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : term97 _110927 s t u.
Proof. exact (EQ_MP (@lem4825796 _110927 s t u) (@lem4826898 _110927 s t u)). Qed.
Lemma lem4826900 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : term64 _110927 s t u.
Proof. exact (EQ_MP (@lem4825792 _110927 s t u) (@lem4826899 _110927 s t u)). Qed.
Lemma lem4826901 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : term63 _110927 s t u.
Proof. exact (EQ_MP (@lem4825647 _110927 s t u) (@lem4826900 _110927 s t u)). Qed.
Lemma lem4826902 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term63 _110927 s t u) : term63 _110927 s t u.
Proof. exact (h1). Qed.
Lemma lem4826903 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term58 _110927 s t u) : term58 _110927 s t u.
Proof. exact (h1). Qed.
Lemma lem4826904 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term58 _110927 s t u) (h2 : term63 _110927 s t u) : (@DIFF _110927 s t) = u.
Proof. exact (@lem4826902 _110927 s t u h2 (@lem4826903 _110927 s t u h1)). Qed.
Lemma lem4826905 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term58 _110927 s t u) : term210 _110927 s t u.
Proof. exact (fun h0 : term63 _110927 s t u => @lem4826904 _110927 s t u h1 h0). Qed.
Lemma lem4826906 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term63 _110927 s t u) : term63 _110927 s t u.
Proof. exact (h1). Qed.
Lemma lem4826907 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term58 _110927 s t u) (h2 : term63 _110927 s t u) : (@DIFF _110927 s t) = u.
Proof. exact (@lem4826905 _110927 s t u h1 (@lem4826906 _110927 s t u h2)). Qed.
Lemma lem4826908 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) (h1 : term63 _110927 s t u) : term63 _110927 s t u.
Proof. exact (fun h0 : term58 _110927 s t u => @lem4826907 _110927 s t u h0 h1). Qed.
Lemma lem4826909 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : term211 _110927 s t u.
Proof. exact (fun h0 : term63 _110927 s t u => @lem4826908 _110927 s t u h0). Qed.
Lemma lem4826911 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term212 A t s) : term212 A t s.
Proof. exact (h1). Qed.
Lemma lem4826912 {A : Type'} (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) : @SUBSET (A -> Prop) t s.
Proof. exact (h1). Qed.
Lemma lem4826913 {A : Type'} (s : type686 A) (h1 : @pairwise (A -> Prop) (@DISJOINT A) s) : @pairwise (A -> Prop) (@DISJOINT A) s.
Proof. exact (h1). Qed.
Lemma lem4826915 {_110927 : Type'} (s : _110927 -> Prop) (t : _110927 -> Prop) (u : _110927 -> Prop) : term63 _110927 s t u.
Proof. exact (@lem4826909 _110927 s t u (@lem4826901 _110927 s t u)). Qed.
Lemma lem4826916 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term63 A s t u.
Proof. exact (@lem4826915 A s t u). Qed.
Lemma lem4826917 {A : Type'} (s : type686 A) (t : type686 A) : term213 A s t.
Proof. exact (@lem4826916 A (@UNIONS A s) (@UNIONS A t) (term214 A s t)). Qed.
Lemma lem4826921 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) : (term35 _87099 s t) = (term34 _87099 s t).
Proof. exact (EQ_MP (@lem4825574 _87099 s t) (@lem4825573 _87099 s t)). Qed.
Lemma lem4826922 {A : Type'} (s : type686 A) (t : type686 A) : (term35 A s t) = (term34 A s t).
Proof. exact (@lem4826921 A s t). Qed.
Lemma lem4826923 {A : Type'} (s : type686 A) (t : type686 A) : (term215 A s t) = (term216 A s t).
Proof. exact (@lem4826922 A t (@DIFF (A -> Prop) s t)). Qed.
Lemma lem4826924 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4826925 {A : Type'} (s : type686 A) (t : type686 A) : (term217 A s t) = (term218 A s t).
Proof. exact (MK_COMB (@lem4826924 A) (@lem4826923 A s t)). Qed.
Lemma lem4826926 {A : Type'} (s : type686 A) : (@UNIONS A s) = (@UNIONS A s).
Proof. exact (eq_refl (@UNIONS A s)). Qed.
Lemma lem4826927 {A : Type'} (t : type686 A) (s : type686 A) : ((term215 A s t) = (@UNIONS A s)) = ((term216 A s t) = (@UNIONS A s)).
Proof. exact (MK_COMB (@lem4826925 A s t) (@lem4826926 A s)). Qed.
Lemma lem4826930 {A : Type'} (t : type686 A) (s : type686 A) : ((term216 A s t) = (@UNIONS A s)) = ((term215 A s t) = (@UNIONS A s)).
Proof. exact (SYM (@lem4826927 A t s)). Qed.
Lemma lem4826931 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4826942 {A : Type'} (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) (h2 : @pairwise (A -> Prop) (@DISJOINT A) s) : term219 A t s.
Proof. exact (conj (@lem4826912 A t s h1) (@lem4826913 A s h2)). Qed.
Lemma lem4826948 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term220 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4826949 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term221 A s t).
Proof. exact (@lem4826948 (A -> Prop) s t). Qed.
Lemma lem4826950 {A : Type'} (t : type686 A) (s : type686 A) : (@SUBSET (A -> Prop) t s) = (term221 A t s).
Proof. exact (@lem4826949 A t s). Qed.
Lemma lem4826957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4826958 {A : Type'} (t : type686 A) (s : type686 A) : (term222 A t s) = (term223 A t s).
Proof. exact (MK_COMB (@lem4826957) (@lem4826950 A t s)). Qed.
Lemma lem4826959 {A : Type'} (s : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) s) = (@pairwise (A -> Prop) (@DISJOINT A) s).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) s)). Qed.
Lemma lem4826960 {A : Type'} (t : type686 A) (s : type686 A) : (term219 A t s) = (term224 A t s).
Proof. exact (MK_COMB (@lem4826958 A t s) (@lem4826959 A s)). Qed.
Lemma lem4826963 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4826964 {A : Type'} (t : type686 A) (s : type686 A) : (term225 A t s) = (term226 A t s).
Proof. exact (MK_COMB (@lem4826963) (@lem4826960 A t s)). Qed.
Lemma lem4826968 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term53 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4826969 {A : Type'} (s : type686 A) (t : type686 A) : (s = t) = (term227 A s t).
Proof. exact (@lem4826968 (A -> Prop) s t). Qed.
Lemma lem4826970 {A : Type'} (t : type686 A) (s : type686 A) : ((term228 A s t) = s) = (term229 A t s).
Proof. exact (@lem4826969 A (term228 A s t) s). Qed.
Lemma lem4826979 {A : Type'} (t : type686 A) (s : type686 A) : (term230 A t s) = (term231 A t s).
Proof. exact (MK_COMB (@lem4826964 A t s) (@lem4826970 A t s)). Qed.
Lemma lem4826982 {A : Type'} (t : type686 A) (s : type686 A) : (term231 A t s) = (term230 A t s).
Proof. exact (SYM (@lem4826979 A t s)). Qed.
Lemma lem4826994 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4826995 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4826994 (A -> Prop) P x). Qed.
Lemma lem4826996 {A : Type'} (t : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x t) = (t x).
Proof. exact (@lem4826995 A t x). Qed.
Lemma lem4826997 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4826998 {A : Type'} (t : type686 A) (x : A -> Prop) : (term232 A x t) = (term233 A t x).
Proof. exact (MK_COMB (@lem4826997) (@lem4826996 A t x)). Qed.
Lemma lem4827000 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4827001 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4827000 (A -> Prop) P x). Qed.
Lemma lem4827002 {A : Type'} (s : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x s) = (s x).
Proof. exact (@lem4827001 A s x). Qed.
Lemma lem4827003 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term234 A t x s) = (term235 A t s x).
Proof. exact (MK_COMB (@lem4826998 A t x) (@lem4827002 A s x)). Qed.
Lemma lem4827006 {A : Type'} (t : type686 A) (s : type686 A) : (term236 A t s) = (term237 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4827003 A t s x)). Qed.
Lemma lem4827007 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4827008 {A : Type'} (t : type686 A) (s : type686 A) : (term221 A t s) = (term238 A t s).
Proof. exact (MK_COMB (@lem4827007 A) (@lem4827006 A t s)). Qed.
Lemma lem4827013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4827014 {A : Type'} (t : type686 A) (s : type686 A) : (term223 A t s) = (term239 A t s).
Proof. exact (MK_COMB (@lem4827013) (@lem4827008 A t s)). Qed.
Lemma lem4827015 {A : Type'} (s : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) s) = (@pairwise (A -> Prop) (@DISJOINT A) s).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) s)). Qed.
Lemma lem4827016 {A : Type'} (t : type686 A) (s : type686 A) : (term224 A t s) = (term240 A t s).
Proof. exact (MK_COMB (@lem4827014 A t s) (@lem4827015 A s)). Qed.
Lemma lem4827019 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4827020 {A : Type'} (t : type686 A) (s : type686 A) : (term226 A t s) = (term241 A t s).
Proof. exact (MK_COMB (@lem4827019) (@lem4827016 A t s)). Qed.
Lemma lem4827028 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term65 A x s t) = (term66 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem4827029 {A : Type'} (s : type686 A) (x : A -> Prop) (t : type686 A) : (term242 A x s t) = (term243 A s x t).
Proof. exact (@lem4827028 (A -> Prop) s x t). Qed.
Lemma lem4827030 {A : Type'} (x : A -> Prop) (s : type686 A) (t : type686 A) : (term244 A x s t) = (term245 A x s t).
Proof. exact (@lem4827029 A t x (@DIFF (A -> Prop) s t)). Qed.
Lemma lem4827034 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4827035 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4827034 (A -> Prop) P x). Qed.
Lemma lem4827036 {A : Type'} (t : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x t) = (t x).
Proof. exact (@lem4827035 A t x). Qed.
Lemma lem4827037 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4827038 {A : Type'} (t : type686 A) (x : A -> Prop) : (term246 A x t) = (term247 A t x).
Proof. exact (MK_COMB (@lem4827037) (@lem4827036 A t x)). Qed.
Lemma lem4827040 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4827041 {A : Type'} (s : type686 A) (x : A -> Prop) (t : type686 A) : (term248 A x s t) = (term249 A s x t).
Proof. exact (@lem4827040 (A -> Prop) s x t). Qed.
Lemma lem4827045 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4827046 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4827045 (A -> Prop) P x). Qed.
Lemma lem4827047 {A : Type'} (s : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x s) = (s x).
Proof. exact (@lem4827046 A s x). Qed.
Lemma lem4827048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4827049 {A : Type'} (s : type686 A) (x : A -> Prop) : (term250 A x s) = (term251 A s x).
Proof. exact (MK_COMB (@lem4827048) (@lem4827047 A s x)). Qed.
Lemma lem4827051 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4827052 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4827051 (A -> Prop) P x). Qed.
Lemma lem4827053 {A : Type'} (t : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x t) = (t x).
Proof. exact (@lem4827052 A t x). Qed.
Lemma lem4827054 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4827055 {A : Type'} (t : type686 A) (x : A -> Prop) : (term252 A x t) = (term253 A t x).
Proof. exact (MK_COMB (@lem4827054) (@lem4827053 A t x)). Qed.
Lemma lem4827056 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term249 A s x t) = (term254 A s t x).
Proof. exact (MK_COMB (@lem4827049 A s x) (@lem4827055 A t x)). Qed.
Lemma lem4827059 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term248 A x s t) = (term254 A s t x).
Proof. exact (TRANS (@lem4827041 A s x t) (@lem4827056 A s t x)). Qed.
Lemma lem4827060 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term245 A x s t) = (term255 A s t x).
Proof. exact (MK_COMB (@lem4827038 A t x) (@lem4827059 A s t x)). Qed.
Lemma lem4827063 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term244 A x s t) = (term255 A s t x).
Proof. exact (TRANS (@lem4827030 A x s t) (@lem4827060 A s t x)). Qed.
Lemma lem4827064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4827065 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term256 A x s t) = (term257 A s t x).
Proof. exact (MK_COMB (@lem4827064) (@lem4827063 A s t x)). Qed.
Lemma lem4827067 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4827068 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4827067 (A -> Prop) P x). Qed.
Lemma lem4827069 {A : Type'} (s : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x s) = (s x).
Proof. exact (@lem4827068 A s x). Qed.
Lemma lem4827070 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : ((term244 A x s t) = (@IN (A -> Prop) x s)) = ((term255 A s t x) = (s x)).
Proof. exact (MK_COMB (@lem4827065 A s t x) (@lem4827069 A s x)). Qed.
Lemma lem4827073 {A : Type'} (t : type686 A) (s : type686 A) : (term258 A t s) = (term259 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4827070 A t s x)). Qed.
Lemma lem4827074 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4827075 {A : Type'} (t : type686 A) (s : type686 A) : (term229 A t s) = (term260 A t s).
Proof. exact (MK_COMB (@lem4827074 A) (@lem4827073 A t s)). Qed.
Lemma lem4827080 {A : Type'} (t : type686 A) (s : type686 A) : (term231 A t s) = (term261 A t s).
Proof. exact (MK_COMB (@lem4827020 A t s) (@lem4827075 A t s)). Qed.
Lemma lem4827083 {A : Type'} (t : type686 A) (s : type686 A) : (term261 A t s) = (term231 A t s).
Proof. exact (SYM (@lem4827080 A t s)). Qed.
Lemma lem4827085 (p : Prop) : p = (term98 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4827086 {A : Type'} (t : type686 A) (s : type686 A) : (term261 A t s) = (term262 A t s).
Proof. exact (@lem4827085 (term261 A t s)). Qed.
Lemma lem4827087 {A : Type'} (t : type686 A) (s : type686 A) : (term262 A t s) = (term261 A t s).
Proof. exact (SYM (@lem4827086 A t s)). Qed.
Lemma lem4827088 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term263 A t s) : term263 A t s.
Proof. exact (h1). Qed.
Lemma lem4827091 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term262 A t s) : term262 A t s.
Proof. exact (h1). Qed.
Lemma lem4827092 {A : Type'} (t : type686 A) (s : type686 A) : term264 A t s.
Proof. exact (fun h0 : term262 A t s => @lem4827091 A t s h0). Qed.
Lemma lem4827093 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term264 A t s) : term264 A t s.
Proof. exact (h1). Qed.
Lemma lem4827094 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term262 A t s) : term262 A t s.
Proof. exact (h1). Qed.
Lemma lem4827095 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term262 A t s) (h2 : term264 A t s) : term262 A t s.
Proof. exact (@lem4827093 A t s h2 (@lem4827094 A t s h1)). Qed.
Lemma lem4827096 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term262 A t s) : term265 A t s.
Proof. exact (fun h0 : term264 A t s => @lem4827095 A t s h1 h0). Qed.
Lemma lem4827097 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term264 A t s) : term264 A t s.
Proof. exact (h1). Qed.
Lemma lem4827098 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term262 A t s) (h2 : term264 A t s) : term262 A t s.
Proof. exact (@lem4827096 A t s h1 (@lem4827097 A t s h2)). Qed.
Lemma lem4827099 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term264 A t s) : term264 A t s.
Proof. exact (fun h0 : term262 A t s => @lem4827098 A t s h0 h1). Qed.
Lemma lem4827100 {A : Type'} (t : type686 A) (s : type686 A) : term266 A t s.
Proof. exact (fun h0 : term264 A t s => @lem4827099 A t s h0). Qed.
Lemma lem4827103 {A : Type'} (t : type686 A) (s : type686 A) : term264 A t s.
Proof. exact (@lem4827100 A t s (@lem4827092 A t s)). Qed.
Lemma lem4827104 {A : Type'} (t : type686 A) (s : type686 A) : term264 A t s.
Proof. exact (@lem4827103 A t s). Qed.
Lemma lem4827114 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4827115 {A : Type'} (t : type686 A) (s : type686 A) : (term262 A t s) = (term267 A t s).
Proof. exact (@lem4827114 (term263 A t s)). Qed.
Lemma lem4827117 (t : Prop) : (term105 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4827118 {A : Type'} (t : type686 A) (s : type686 A) : (term267 A t s) = (term261 A t s).
Proof. exact (@lem4827117 (term261 A t s)). Qed.
Lemma lem4827121 {A : Type'} (t : type686 A) (s : type686 A) : (term262 A t s) = (term261 A t s).
Proof. exact (TRANS (@lem4827115 A t s) (@lem4827118 A t s)). Qed.
Lemma lem4827138 {A : Type'} (s : type686 A) : (term268 A s) = (term269 A s).
Proof. exact (fun_ext (fun t : type686 A => @lem4827121 A t s)). Qed.
Lemma lem4827139 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4827140 {A : Type'} (s : type686 A) : (term270 A s) = (term271 A s).
Proof. exact (MK_COMB (@lem4827139 A) (@lem4827138 A s)). Qed.
Lemma lem4827145 {A : Type'} : (term272 A) = (term273 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4827140 A s)). Qed.
Lemma lem4827146 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4827155 {A : Type'} : (term274 A) = (term275 A).
Proof. exact (MK_COMB (@lem4827146 A) (@lem4827145 A)). Qed.
Lemma lem4827170 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : ((term255 A s t x) = (s x)) = ((term255 A s t x) = (s x)).
Proof. exact (eq_refl ((term255 A s t x) = (s x))). Qed.
Lemma lem4827171 {A : Type'} (t : type686 A) (s : type686 A) : (term259 A t s) = (term259 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4827170 A t s x)). Qed.
Lemma lem4827172 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4827173 {A : Type'} (t : type686 A) (s : type686 A) : (term260 A t s) = (term260 A t s).
Proof. exact (MK_COMB (@lem4827172 A) (@lem4827171 A t s)). Qed.
Lemma lem4827174 {A : Type'} (s : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) s) = (@pairwise (A -> Prop) (@DISJOINT A) s).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) s)). Qed.
Lemma lem4827179 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term235 A t s x) = (term235 A t s x).
Proof. exact (eq_refl (term235 A t s x)). Qed.
Lemma lem4827180 {A : Type'} (t : type686 A) (s : type686 A) : (term237 A t s) = (term237 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4827179 A t s x)). Qed.
Lemma lem4827181 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4827182 {A : Type'} (t : type686 A) (s : type686 A) : (term238 A t s) = (term238 A t s).
Proof. exact (MK_COMB (@lem4827181 A) (@lem4827180 A t s)). Qed.
Lemma lem4827183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4827184 {A : Type'} (t : type686 A) (s : type686 A) : (term239 A t s) = (term239 A t s).
Proof. exact (MK_COMB (@lem4827183) (@lem4827182 A t s)). Qed.
Lemma lem4827185 {A : Type'} (t : type686 A) (s : type686 A) : (term240 A t s) = (term240 A t s).
Proof. exact (MK_COMB (@lem4827184 A t s) (@lem4827174 A s)). Qed.
Lemma lem4827186 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4827187 {A : Type'} (t : type686 A) (s : type686 A) : (term241 A t s) = (term241 A t s).
Proof. exact (MK_COMB (@lem4827186) (@lem4827185 A t s)). Qed.
Lemma lem4827188 {A : Type'} (t : type686 A) (s : type686 A) : (term261 A t s) = (term261 A t s).
Proof. exact (MK_COMB (@lem4827187 A t s) (@lem4827173 A t s)). Qed.
Lemma lem4827189 {A : Type'} (s : type686 A) : (term269 A s) = (term269 A s).
Proof. exact (fun_ext (fun t : type686 A => @lem4827188 A t s)). Qed.
Lemma lem4827190 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4827191 {A : Type'} (s : type686 A) : (term271 A s) = (term271 A s).
Proof. exact (MK_COMB (@lem4827190 A) (@lem4827189 A s)). Qed.
Lemma lem4827192 {A : Type'} : (term273 A) = (term273 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4827191 A s)). Qed.
Lemma lem4827193 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4827194 {A : Type'} : (term275 A) = (term275 A).
Proof. exact (MK_COMB (@lem4827193 A) (@lem4827192 A)). Qed.
Lemma lem4827231 {A : Type'} : (term274 A) = (term275 A).
Proof. exact (TRANS (@lem4827155 A) (@lem4827194 A)). Qed.
Lemma lem4827232 {A : Type'} : (term275 A) = (term274 A).
Proof. exact (SYM (@lem4827231 A)). Qed.
Lemma lem4827233 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term240 A t s) : term240 A t s.
Proof. exact (h1). Qed.
Lemma lem4827235 (p : Prop) : p = (term98 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4827236 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : ((term255 A s t x) = (s x)) = (term276 A t s x).
Proof. exact (@lem4827235 ((term255 A s t x) = (s x))). Qed.
Lemma lem4827237 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term276 A t s x) = ((term255 A s t x) = (s x)).
Proof. exact (SYM (@lem4827236 A t s x)). Qed.
Lemma lem4827238 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term277 A t s x) : term277 A t s x.
Proof. exact (h1). Qed.
Lemma lem4827245 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term235 A t s x) = (term278 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem4827246 {A : Type'} (t : type686 A) (s : type686 A) : (term237 A t s) = (term279 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4827245 A t s x)). Qed.
Lemma lem4827247 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4827248 {A : Type'} (t : type686 A) (s : type686 A) : (term238 A t s) = (term280 A t s).
Proof. exact (MK_COMB (@lem4827247 A) (@lem4827246 A t s)). Qed.
Lemma lem4827249 {A : Type'} (s : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) s) = (@pairwise (A -> Prop) (@DISJOINT A) s).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) s)). Qed.
Lemma lem4827250 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4827251 {A : Type'} (t : type686 A) (s : type686 A) : (term239 A t s) = (term281 A t s).
Proof. exact (MK_COMB (@lem4827250) (@lem4827248 A t s)). Qed.
Lemma lem4827288 {A : Type'} (t : type686 A) (s : type686 A) : (term240 A t s) = (term282 A t s).
Proof. exact (MK_COMB (@lem4827251 A t s) (@lem4827249 A s)). Qed.
Lemma lem4827289 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term240 A t s) : term282 A t s.
Proof. exact (EQ_MP (@lem4827288 A t s) (@lem4827233 A t s h1)). Qed.
Lemma lem4827297 {A : Type'} (t : type686 A) (x : A -> Prop) : (term283 A t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem4827299 {A : Type'} (s : type686 A) (x : A -> Prop) : (term284 A s x) = (term284 A s x).
Proof. exact (eq_refl (term284 A s x)). Qed.
Lemma lem4827300 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term285 A s t x) = (term278 A s t x).
Proof. exact (MK_COMB (@lem4827299 A s x) (@lem4827297 A t x)). Qed.
Lemma lem4827301 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term286 A s t x) = (term285 A s t x).
Proof. exact (@lem17045 (s x) (term253 A t x)). Qed.
Lemma lem4827302 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term286 A s t x) = (term278 A s t x).
Proof. exact (TRANS (@lem4827301 A s t x) (@lem4827300 A s t x)). Qed.
Lemma lem4827307 {A : Type'} (t : type686 A) (x : A -> Prop) : (term287 A t x) = (term287 A t x).
Proof. exact (eq_refl (term287 A t x)). Qed.
Lemma lem4827308 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term288 A s t x) = (term289 A s t x).
Proof. exact (MK_COMB (@lem4827307 A t x) (@lem4827302 A s t x)). Qed.
Lemma lem4827309 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term290 A s t x) = (term288 A s t x).
Proof. exact (@lem17160 (t x) (term254 A s t x)). Qed.
Lemma lem4827310 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term290 A s t x) = (term289 A s t x).
Proof. exact (TRANS (@lem4827309 A s t x) (@lem4827308 A s t x)). Qed.
Lemma lem4827315 {A : Type'} (s : type686 A) (x : A -> Prop) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4827316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4827317 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term291 A s t x) = (term292 A s t x).
Proof. exact (MK_COMB (@lem4827316) (@lem4827310 A s t x)). Qed.
Lemma lem4827318 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term293 A t s x) = (term294 A t s x).
Proof. exact (MK_COMB (@lem4827317 A s t x) (@lem4827315 A s x)). Qed.
Lemma lem4827323 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term295 A t s x) = (term295 A t s x).
Proof. exact (eq_refl (term295 A t s x)). Qed.
Lemma lem4827324 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term296 A t s x) = (term297 A t s x).
Proof. exact (MK_COMB (@lem4827323 A t s x) (@lem4827318 A t s x)). Qed.
Lemma lem4827325 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term277 A t s x) = (term296 A t s x).
Proof. exact (@lem17646 (term255 A s t x) (s x)). Qed.
Lemma lem4827330 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term277 A t s x) = (term297 A t s x).
Proof. exact (TRANS (@lem4827325 A t s x) (@lem4827324 A t s x)). Qed.
Lemma lem4827331 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term277 A t s x) : term297 A t s x.
Proof. exact (EQ_MP (@lem4827330 A t s x) (@lem4827238 A t s x h1)). Qed.
Lemma lem4827336 {A : Type'} (s : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) s) = (@pairwise (A -> Prop) (@DISJOINT A) s).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) s)). Qed.
Lemma lem4827341 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4827342 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4827341 (A -> Prop) Prop f x). Qed.
Lemma lem4827344 {A : Type'} (s : type686 A) (x : A -> Prop) : (s x) = (@I ((A -> Prop) -> Prop) s x).
Proof. exact (@lem4827342 A s x). Qed.
Lemma lem4827351 {A : Type'} (t : type686 A) (x : A -> Prop) : (term284 A t x) = (term284 A t x).
Proof. exact (eq_refl (term284 A t x)). Qed.
Lemma lem4827352 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term278 A t s x) = (term298 A t s x).
Proof. exact (MK_COMB (@lem4827351 A t x) (@lem4827344 A s x)). Qed.
Lemma lem4827353 {A : Type'} (t : type686 A) (s : type686 A) : (term279 A t s) = (term299 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4827352 A t s x)). Qed.
Lemma lem4827354 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4827355 {A : Type'} (t : type686 A) (s : type686 A) : (term280 A t s) = (term300 A t s).
Proof. exact (MK_COMB (@lem4827354 A) (@lem4827353 A t s)). Qed.
Lemma lem4827356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4827357 {A : Type'} (t : type686 A) (s : type686 A) : (term281 A t s) = (term301 A t s).
Proof. exact (MK_COMB (@lem4827356) (@lem4827355 A t s)). Qed.
Lemma lem4827358 {A : Type'} (t : type686 A) (s : type686 A) : (term282 A t s) = (term302 A t s).
Proof. exact (MK_COMB (@lem4827357 A t s) (@lem4827336 A s)). Qed.
Lemma lem4827359 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term240 A t s) : term302 A t s.
Proof. exact (EQ_MP (@lem4827358 A t s) (@lem4827289 A t s h1)). Qed.
Lemma lem4827364 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4827365 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4827364 (A -> Prop) Prop f x). Qed.
Lemma lem4827367 {A : Type'} (s : type686 A) (x : A -> Prop) : (s x) = (@I ((A -> Prop) -> Prop) s x).
Proof. exact (@lem4827365 A s x). Qed.
Lemma lem4827370 {A : Type'} (t : type686 A) (x : A -> Prop) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4827371 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4827376 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4827377 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4827376 (A -> Prop) Prop f x). Qed.
Lemma lem4827379 {A : Type'} (s : type686 A) (x : A -> Prop) : (s x) = (@I ((A -> Prop) -> Prop) s x).
Proof. exact (@lem4827377 A s x). Qed.
Lemma lem4827380 {A : Type'} (s : type686 A) (x : A -> Prop) : (term253 A s x) = (term303 A s x).
Proof. exact (MK_COMB (@lem4827371) (@lem4827379 A s x)). Qed.
Lemma lem4827381 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4827382 {A : Type'} (s : type686 A) (x : A -> Prop) : (term284 A s x) = (term304 A s x).
Proof. exact (MK_COMB (@lem4827381) (@lem4827380 A s x)). Qed.
Lemma lem4827383 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term278 A s t x) = (term305 A s t x).
Proof. exact (MK_COMB (@lem4827382 A s x) (@lem4827370 A t x)). Qed.
Lemma lem4827390 {A : Type'} (t : type686 A) (x : A -> Prop) : (term287 A t x) = (term287 A t x).
Proof. exact (eq_refl (term287 A t x)). Qed.
Lemma lem4827391 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term289 A s t x) = (term306 A s t x).
Proof. exact (MK_COMB (@lem4827390 A t x) (@lem4827383 A s t x)). Qed.
Lemma lem4827392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4827393 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term292 A s t x) = (term307 A s t x).
Proof. exact (MK_COMB (@lem4827392) (@lem4827391 A s t x)). Qed.
Lemma lem4827394 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term294 A t s x) = (term308 A t s x).
Proof. exact (MK_COMB (@lem4827393 A s t x) (@lem4827367 A s x)). Qed.
Lemma lem4827395 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4827400 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4827401 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4827400 (A -> Prop) Prop f x). Qed.
Lemma lem4827403 {A : Type'} (s : type686 A) (x : A -> Prop) : (s x) = (@I ((A -> Prop) -> Prop) s x).
Proof. exact (@lem4827401 A s x). Qed.
Lemma lem4827404 {A : Type'} (s : type686 A) (x : A -> Prop) : (term253 A s x) = (term303 A s x).
Proof. exact (MK_COMB (@lem4827395) (@lem4827403 A s x)). Qed.
Lemma lem4827409 {A : Type'} (t : type686 A) (x : A -> Prop) : (term253 A t x) = (term253 A t x).
Proof. exact (eq_refl (term253 A t x)). Qed.
Lemma lem4827414 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4827415 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4827414 (A -> Prop) Prop f x). Qed.
Lemma lem4827417 {A : Type'} (s : type686 A) (x : A -> Prop) : (s x) = (@I ((A -> Prop) -> Prop) s x).
Proof. exact (@lem4827415 A s x). Qed.
Lemma lem4827418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4827419 {A : Type'} (s : type686 A) (x : A -> Prop) : (term251 A s x) = (term309 A s x).
Proof. exact (MK_COMB (@lem4827418) (@lem4827417 A s x)). Qed.
Lemma lem4827420 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term254 A s t x) = (term310 A s t x).
Proof. exact (MK_COMB (@lem4827419 A s x) (@lem4827409 A t x)). Qed.
Lemma lem4827425 {A : Type'} (t : type686 A) (x : A -> Prop) : (term247 A t x) = (term247 A t x).
Proof. exact (eq_refl (term247 A t x)). Qed.
Lemma lem4827426 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term255 A s t x) = (term311 A s t x).
Proof. exact (MK_COMB (@lem4827425 A t x) (@lem4827420 A s t x)). Qed.
Lemma lem4827427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4827428 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term312 A s t x) = (term313 A s t x).
Proof. exact (MK_COMB (@lem4827427) (@lem4827426 A s t x)). Qed.
Lemma lem4827429 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term314 A t s x) = (term315 A t s x).
Proof. exact (MK_COMB (@lem4827428 A s t x) (@lem4827404 A s x)). Qed.
Lemma lem4827430 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4827431 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term295 A t s x) = (term316 A t s x).
Proof. exact (MK_COMB (@lem4827430) (@lem4827429 A t s x)). Qed.
Lemma lem4827432 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term297 A t s x) = (term317 A t s x).
Proof. exact (MK_COMB (@lem4827431 A t s x) (@lem4827394 A t s x)). Qed.
Lemma lem4827433 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term277 A t s x) : term317 A t s x.
Proof. exact (EQ_MP (@lem4827432 A t s x) (@lem4827331 A t s x h1)). Qed.
Lemma lem4827435 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term240 A t s) : term300 A t s.
Proof. exact (proj1 (@lem4827359 A t s h1)). Qed.
Lemma lem4827436 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term315 A t s x) : term315 A t s x.
Proof. exact (h1). Qed.
Lemma lem4827437 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term308 A t s x) : term308 A t s x.
Proof. exact (h1). Qed.
Lemma lem4827439 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term315 A t s x) : term311 A s t x.
Proof. exact (proj1 (@lem4827436 A t s x h1)). Qed.
Lemma lem4827441 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (h1 : term310 A s t x) : term310 A s t x.
Proof. exact (h1). Qed.
Lemma lem4827445 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term308 A t s x) : term306 A s t x.
Proof. exact (proj1 (@lem4827437 A t s x h1)). Qed.
Lemma lem4827446 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term308 A t s x) : term305 A s t x.
Proof. exact (proj2 (@lem4827445 A t s x h1)). Qed.
Lemma lem4827457 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term298 A t s x) = (term298 A t s x).
Proof. exact (eq_refl (term298 A t s x)). Qed.
Lemma lem4827458 {A : Type'} (t : type686 A) (s : type686 A) : (term299 A t s) = (term299 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4827457 A t s x)). Qed.
Lemma lem4827459 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4827461 {A : Type'} (t : type686 A) (s : type686 A) : (term300 A t s) = (term300 A t s).
Proof. exact (MK_COMB (@lem4827459 A) (@lem4827458 A t s)). Qed.
Lemma lem4827462 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term240 A t s) : term300 A t s.
Proof. exact (EQ_MP (@lem4827461 A t s) (@lem4827435 A t s h1)). Qed.
Lemma lem4827474 {A : Type'} (t : type686 A) (x : A -> Prop) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4827532 {A : Type'} (s : type686 A) (x : A -> Prop) (h1 : term303 A s x) : term303 A s x.
Proof. exact (h1). Qed.
Lemma lem4827561 {A : Type'} (t : type686 A) (x : A -> Prop) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4827562 {A : Type'} (_59824 : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term240 A t s) : term318 A t s _59824.
Proof. exact (@lem4827462 A t s h1 _59824). Qed.
Lemma lem4827563 {A : Type'} (t : type686 A) (s : type686 A) (_59824 : A -> Prop) : (term318 A t s _59824) = (term298 A t s _59824).
Proof. exact (eq_refl (term318 A t s _59824)). Qed.
Lemma lem4827579 {A : Type'} (_59824 : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term240 A t s) : term298 A t s _59824.
Proof. exact (EQ_MP (@lem4827563 A t s _59824) (@lem4827562 A _59824 t s h1)). Qed.
Lemma lem4827583 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term315 A t s x) : term303 A s x.
Proof. exact (proj2 (@lem4827436 A t s x h1)). Qed.
Lemma lem4827585 {A : Type'} (t : type686 A) (x : A -> Prop) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4827595 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term315 A t s x) : term303 A s x.
Proof. exact (proj2 (@lem4827436 A t s x h1)). Qed.
Lemma lem4827613 {A : Type'} (s : type686 A) (x : A -> Prop) (h1 : term303 A s x) : term303 A s x.
Proof. exact (h1). Qed.
Lemma lem4827625 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term308 A t s x) : term253 A t x.
Proof. exact (proj1 (@lem4827445 A t s x h1)). Qed.
Lemma lem4827627 {A : Type'} (t : type686 A) (x : A -> Prop) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4827629 {A : Type'} (t : type686 A) (x : A -> Prop) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4827630 {A : Type'} (t : type686 A) (x : A -> Prop) (h1 : t x) : term319 A t x.
Proof. exact (fun h0 : term253 A t x => @lem4827629 A t x h1). Qed.
Lemma lem4827632 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4827633 {A : Type'} (t : type686 A) (x : A -> Prop) : (term319 A t x) = (t x).
Proof. exact (@lem4827632 (t x)). Qed.
Lemma lem4827634 {A : Type'} (t : type686 A) (x : A -> Prop) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem4827633 A t x) (@lem4827630 A t x h1)). Qed.
Lemma lem4827640 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4827641 {A : Type'} (s : type686 A) (t : type686 A) (_59824 : A -> Prop) : (term298 A t s _59824) = (term320 A s t _59824).
Proof. exact (@lem4827640 (@I ((A -> Prop) -> Prop) s _59824) (term253 A t _59824)). Qed.
Lemma lem4827647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4827648 {A : Type'} (s : type686 A) (t : type686 A) (_59824 : A -> Prop) : (term321 A t s _59824) = (term322 A s t _59824).
Proof. exact (MK_COMB (@lem4827647) (@lem4827641 A s t _59824)). Qed.
Lemma lem4827654 {A : Type'} (s : type686 A) (t : type686 A) (_59824 : A -> Prop) : (term320 A s t _59824) = (term320 A s t _59824).
Proof. exact (eq_refl (term320 A s t _59824)). Qed.
Lemma lem4827655 {A : Type'} (s : type686 A) (t : type686 A) (_59824 : A -> Prop) : ((term298 A t s _59824) = (term320 A s t _59824)) = ((term320 A s t _59824) = (term320 A s t _59824)).
Proof. exact (MK_COMB (@lem4827648 A s t _59824) (@lem4827654 A s t _59824)). Qed.
Lemma lem4827657 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4827658 (x : Prop) : (x = x) = True.
Proof. exact (@lem4827657 Prop x). Qed.
Lemma lem4827659 {A : Type'} (s : type686 A) (t : type686 A) (_59824 : A -> Prop) : ((term320 A s t _59824) = (term320 A s t _59824)) = True.
Proof. exact (@lem4827658 (term320 A s t _59824)). Qed.
Lemma lem4827660 {A : Type'} (s : type686 A) (t : type686 A) (_59824 : A -> Prop) : ((term298 A t s _59824) = (term320 A s t _59824)) = True.
Proof. exact (TRANS (@lem4827655 A s t _59824) (@lem4827659 A s t _59824)). Qed.
Lemma lem4827661 {A : Type'} (s : type686 A) (t : type686 A) (_59824 : A -> Prop) : True = ((term298 A t s _59824) = (term320 A s t _59824)).
Proof. exact (SYM (@lem4827660 A s t _59824)). Qed.
Lemma lem4827662 {A : Type'} (s : type686 A) (t : type686 A) (_59824 : A -> Prop) : (term298 A t s _59824) = (term320 A s t _59824).
Proof. exact (EQ_MP (@lem4827661 A s t _59824) (@lem0)). Qed.
Lemma lem4827663 {A : Type'} (_59824 : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term240 A t s) : term320 A s t _59824.
Proof. exact (EQ_MP (@lem4827662 A s t _59824) (@lem4827579 A _59824 t s h1)). Qed.
Lemma lem4827665 (b : Prop) (a : Prop) : (a \/ b) = (term184 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4827666 {A : Type'} (t : type686 A) (s : type686 A) (_59824 : A -> Prop) : (term320 A s t _59824) = (term323 A t s _59824).
Proof. exact (@lem4827665 (term253 A t _59824) (@I ((A -> Prop) -> Prop) s _59824)). Qed.
Lemma lem4827668 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4827669 {A : Type'} (t : type686 A) (_59824 : A -> Prop) : (term283 A t _59824) = (t _59824).
Proof. exact (@lem4827668 (t _59824)). Qed.
Lemma lem4827670 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4827671 {A : Type'} (t : type686 A) (_59824 : A -> Prop) : (term324 A t _59824) = (term233 A t _59824).
Proof. exact (MK_COMB (@lem4827670) (@lem4827669 A t _59824)). Qed.
Lemma lem4827672 {A : Type'} (s : type686 A) (_59824 : A -> Prop) : (@I ((A -> Prop) -> Prop) s _59824) = (@I ((A -> Prop) -> Prop) s _59824).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop) s _59824)). Qed.
Lemma lem4827673 {A : Type'} (t : type686 A) (s : type686 A) (_59824 : A -> Prop) : (term323 A t s _59824) = (term325 A t s _59824).
Proof. exact (MK_COMB (@lem4827671 A t _59824) (@lem4827672 A s _59824)). Qed.
Lemma lem4827674 {A : Type'} (t : type686 A) (s : type686 A) (_59824 : A -> Prop) : (term320 A s t _59824) = (term325 A t s _59824).
Proof. exact (TRANS (@lem4827666 A t s _59824) (@lem4827673 A t s _59824)). Qed.
Lemma lem4827677 {A : Type'} (_59824 : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term240 A t s) : term325 A t s _59824.
Proof. exact (EQ_MP (@lem4827674 A t s _59824) (@lem4827663 A _59824 t s h1)). Qed.
Lemma lem4827678 {A : Type'} (_59824 : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term240 A t s) : term325 A t s _59824.
Proof. exact (@lem4827677 A _59824 t s h1). Qed.
Lemma lem4827679 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term240 A t s) : term325 A t s x.
Proof. exact (@lem4827678 A x t s h1). Qed.
Lemma lem4827682 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : t x) (h2 : term240 A t s) : @I ((A -> Prop) -> Prop) s x.
Proof. exact (@lem4827679 A x t s h2 (@lem4827634 A t x h1)). Qed.
Lemma lem4827683 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : t x) (h2 : term240 A t s) : term326 A s x.
Proof. exact (fun h0 : term303 A s x => @lem4827682 A x t s h1 h2). Qed.
Lemma lem4827685 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4827686 {A : Type'} (s : type686 A) (x : A -> Prop) : (term326 A s x) = (@I ((A -> Prop) -> Prop) s x).
Proof. exact (@lem4827685 (@I ((A -> Prop) -> Prop) s x)). Qed.
Lemma lem4827687 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : t x) (h2 : term240 A t s) : @I ((A -> Prop) -> Prop) s x.
Proof. exact (EQ_MP (@lem4827686 A s x) (@lem4827683 A x t s h1 h2)). Qed.
Lemma lem4827690 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4827692 {A : Type'} (s : type686 A) (x : A -> Prop) : (term303 A s x) = (term327 A s x).
Proof. exact (@lem4827690 (@I ((A -> Prop) -> Prop) s x)). Qed.
Lemma lem4827695 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term315 A t s x) : term327 A s x.
Proof. exact (EQ_MP (@lem4827692 A s x) (@lem4827583 A t s x h1)). Qed.
Lemma lem4827698 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term240 A t s) (h3 : term315 A t s x) : False.
Proof. exact (@lem4827695 A t s x h3 (@lem4827687 A x t s h1 h2)). Qed.
Lemma lem4827699 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term240 A t s) (h3 : term315 A t s x) : term197.
Proof. exact (fun h0 : ~ False => @lem4827698 A t s x h1 h2 h3). Qed.
Lemma lem4827701 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4827702 : term197 = False.
Proof. exact (@lem4827701 False). Qed.
Lemma lem4827703 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term240 A t s) (h3 : term315 A t s x) : False.
Proof. exact (EQ_MP (@lem4827702) (@lem4827699 A t s x h1 h2 h3)). Qed.
Lemma lem4827705 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (h1 : term310 A s t x) : @I ((A -> Prop) -> Prop) s x.
Proof. exact (proj1 (@lem4827441 A s t x h1)). Qed.
Lemma lem4827706 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (h1 : term310 A s t x) : term326 A s x.
Proof. exact (fun h0 : term303 A s x => @lem4827705 A s t x h1). Qed.
Lemma lem4827708 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4827709 {A : Type'} (s : type686 A) (x : A -> Prop) : (term326 A s x) = (@I ((A -> Prop) -> Prop) s x).
Proof. exact (@lem4827708 (@I ((A -> Prop) -> Prop) s x)). Qed.
Lemma lem4827710 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (h1 : term310 A s t x) : @I ((A -> Prop) -> Prop) s x.
Proof. exact (EQ_MP (@lem4827709 A s x) (@lem4827706 A s t x h1)). Qed.
Lemma lem4827713 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4827715 {A : Type'} (s : type686 A) (x : A -> Prop) : (term303 A s x) = (term327 A s x).
Proof. exact (@lem4827713 (@I ((A -> Prop) -> Prop) s x)). Qed.
Lemma lem4827718 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term315 A t s x) : term327 A s x.
Proof. exact (EQ_MP (@lem4827715 A s x) (@lem4827595 A t s x h1)). Qed.
Lemma lem4827721 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term310 A s t x) (h2 : term315 A t s x) : False.
Proof. exact (@lem4827718 A t s x h2 (@lem4827710 A s t x h1)). Qed.
Lemma lem4827722 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term310 A s t x) (h2 : term315 A t s x) : term197.
Proof. exact (fun h0 : ~ False => @lem4827721 A t s x h1 h2). Qed.
Lemma lem4827724 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4827725 : term197 = False.
Proof. exact (@lem4827724 False). Qed.
Lemma lem4827726 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term310 A s t x) (h2 : term315 A t s x) : False.
Proof. exact (EQ_MP (@lem4827725) (@lem4827722 A t s x h1 h2)). Qed.
Lemma lem4827728 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term308 A t s x) : @I ((A -> Prop) -> Prop) s x.
Proof. exact (proj2 (@lem4827437 A t s x h1)). Qed.
Lemma lem4827729 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term308 A t s x) : term326 A s x.
Proof. exact (fun h0 : term303 A s x => @lem4827728 A t s x h1). Qed.
Lemma lem4827731 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4827732 {A : Type'} (s : type686 A) (x : A -> Prop) : (term326 A s x) = (@I ((A -> Prop) -> Prop) s x).
Proof. exact (@lem4827731 (@I ((A -> Prop) -> Prop) s x)). Qed.
Lemma lem4827733 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term308 A t s x) : @I ((A -> Prop) -> Prop) s x.
Proof. exact (EQ_MP (@lem4827732 A s x) (@lem4827729 A t s x h1)). Qed.
Lemma lem4827736 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4827738 {A : Type'} (s : type686 A) (x : A -> Prop) : (term303 A s x) = (term327 A s x).
Proof. exact (@lem4827736 (@I ((A -> Prop) -> Prop) s x)). Qed.
Lemma lem4827741 {A : Type'} (s : type686 A) (x : A -> Prop) (h1 : term303 A s x) : term327 A s x.
Proof. exact (EQ_MP (@lem4827738 A s x) (@lem4827613 A s x h1)). Qed.
Lemma lem4827744 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term303 A s x) (h2 : term308 A t s x) : False.
Proof. exact (@lem4827741 A s x h1 (@lem4827733 A t s x h2)). Qed.
Lemma lem4827745 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term303 A s x) (h2 : term308 A t s x) : term197.
Proof. exact (fun h0 : ~ False => @lem4827744 A t s x h1 h2). Qed.
Lemma lem4827747 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4827748 : term197 = False.
Proof. exact (@lem4827747 False). Qed.
Lemma lem4827749 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term303 A s x) (h2 : term308 A t s x) : False.
Proof. exact (EQ_MP (@lem4827748) (@lem4827745 A t s x h1 h2)). Qed.
Lemma lem4827751 {A : Type'} (t : type686 A) (x : A -> Prop) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4827752 {A : Type'} (t : type686 A) (x : A -> Prop) (h1 : t x) : term319 A t x.
Proof. exact (fun h0 : term253 A t x => @lem4827751 A t x h1). Qed.
Lemma lem4827754 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4827755 {A : Type'} (t : type686 A) (x : A -> Prop) : (term319 A t x) = (t x).
Proof. exact (@lem4827754 (t x)). Qed.
Lemma lem4827756 {A : Type'} (t : type686 A) (x : A -> Prop) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem4827755 A t x) (@lem4827752 A t x h1)). Qed.
Lemma lem4827759 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4827761 {A : Type'} (t : type686 A) (x : A -> Prop) : (term253 A t x) = (term328 A t x).
Proof. exact (@lem4827759 (t x)). Qed.
Lemma lem4827764 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term308 A t s x) : term328 A t x.
Proof. exact (EQ_MP (@lem4827761 A t x) (@lem4827625 A t s x h1)). Qed.
Lemma lem4827767 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term308 A t s x) : False.
Proof. exact (@lem4827764 A t s x h2 (@lem4827756 A t x h1)). Qed.
Lemma lem4827768 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term308 A t s x) : term197.
Proof. exact (fun h0 : ~ False => @lem4827767 A t s x h1 h2). Qed.
Lemma lem4827770 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4827771 : term197 = False.
Proof. exact (@lem4827770 False). Qed.
Lemma lem4827772 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term308 A t s x) : False.
Proof. exact (EQ_MP (@lem4827771) (@lem4827768 A t s x h1 h2)). Qed.
Lemma lem4827773 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term308 A t s x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4827772 A t s x h1 h2) (fun h3 : False => @lem4827627 A t x h1)). Qed.
Lemma lem4827774 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term308 A t s x) : False.
Proof. exact (EQ_MP (@lem4827773 A t s x h1 h2) (@lem4827627 A t x h1)). Qed.
Lemma lem4827775 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term303 A s x) (h2 : term308 A t s x) : (term303 A s x) = False.
Proof. exact (prop_ext (fun h3 : term303 A s x => @lem4827749 A t s x h1 h2) (fun h3 : False => @lem4827613 A s x h1)). Qed.
Lemma lem4827776 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term303 A s x) (h2 : term308 A t s x) : False.
Proof. exact (EQ_MP (@lem4827775 A t s x h1 h2) (@lem4827613 A s x h1)). Qed.
Lemma lem4827777 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term240 A t s) (h3 : term315 A t s x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem4827703 A t s x h1 h2 h3) (fun h4 : False => @lem4827585 A t x h1)). Qed.
Lemma lem4827778 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term240 A t s) (h3 : term315 A t s x) : False.
Proof. exact (EQ_MP (@lem4827777 A t s x h1 h2 h3) (@lem4827585 A t x h1)). Qed.
Lemma lem4827779 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term308 A t s x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4827774 A t s x h1 h2) (fun h3 : False => @lem4827561 A t x h1)). Qed.
Lemma lem4827780 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term308 A t s x) : False.
Proof. exact (EQ_MP (@lem4827779 A t s x h1 h2) (@lem4827561 A t x h1)). Qed.
Lemma lem4827781 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term303 A s x) (h2 : term308 A t s x) : (term303 A s x) = False.
Proof. exact (prop_ext (fun h3 : term303 A s x => @lem4827776 A t s x h1 h2) (fun h3 : False => @lem4827532 A s x h1)). Qed.
Lemma lem4827782 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term303 A s x) (h2 : term308 A t s x) : False.
Proof. exact (EQ_MP (@lem4827781 A t s x h1 h2) (@lem4827532 A s x h1)). Qed.
Lemma lem4827783 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term240 A t s) (h3 : term315 A t s x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem4827778 A t s x h1 h2 h3) (fun h4 : False => @lem4827474 A t x h1)). Qed.
Lemma lem4827784 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term240 A t s) (h3 : term315 A t s x) : False.
Proof. exact (EQ_MP (@lem4827783 A t s x h1 h2 h3) (@lem4827474 A t x h1)). Qed.
Lemma lem4827785 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term308 A t s x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4827780 A t s x h1 h2) (fun h3 : False => @lem4827561 A t x h1)). Qed.
Lemma lem4827786 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term308 A t s x) : False.
Proof. exact (EQ_MP (@lem4827785 A t s x h1 h2) (@lem4827561 A t x h1)). Qed.
Lemma lem4827787 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term303 A s x) (h2 : term308 A t s x) : (term303 A s x) = False.
Proof. exact (prop_ext (fun h3 : term303 A s x => @lem4827782 A t s x h1 h2) (fun h3 : False => @lem4827532 A s x h1)). Qed.
Lemma lem4827788 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term303 A s x) (h2 : term308 A t s x) : False.
Proof. exact (EQ_MP (@lem4827787 A t s x h1 h2) (@lem4827532 A s x h1)). Qed.
Lemma lem4827789 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term240 A t s) (h3 : term315 A t s x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem4827784 A t s x h1 h2 h3) (fun h4 : False => @lem4827474 A t x h1)). Qed.
Lemma lem4827790 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : t x) (h2 : term240 A t s) (h3 : term315 A t s x) : False.
Proof. exact (EQ_MP (@lem4827789 A t s x h1 h2 h3) (@lem4827474 A t x h1)). Qed.
Lemma lem4827791 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term308 A t s x) : False.
Proof. exact (or_elim (@lem4827446 A t s x h1) (fun h0 : term303 A s x => @lem4827788 A t s x h0 h1) (fun h0 : t x => @lem4827786 A t s x h0 h1)). Qed.
Lemma lem4827792 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term240 A t s) (h2 : term315 A t s x) : False.
Proof. exact (or_elim (@lem4827439 A t s x h2) (fun h0 : t x => @lem4827790 A t s x h0 h1 h2) (fun h0 : term310 A s t x => @lem4827726 A t s x h0 h2)). Qed.
Lemma lem4827793 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term277 A t s x) (h2 : term240 A t s) : False.
Proof. exact (or_elim (@lem4827433 A t s x h1) (fun h0 : term315 A t s x => @lem4827792 A t s x h2 h0) (fun h0 : term308 A t s x => @lem4827791 A t s x h0)). Qed.
Lemma lem4827794 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term277 A t s x) (h2 : term240 A t s) : (term277 A t s x) = False.
Proof. exact (prop_ext (fun h3 : term277 A t s x => @lem4827793 A x t s h1 h2) (fun h3 : False => @lem4827238 A t s x h1)). Qed.
Lemma lem4827795 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term277 A t s x) (h2 : term240 A t s) : False.
Proof. exact (EQ_MP (@lem4827794 A x t s h1 h2) (@lem4827238 A t s x h1)). Qed.
Lemma lem4827796 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term240 A t s) : term276 A t s x.
Proof. exact (fun h0 : term277 A t s x => @lem4827795 A x t s h0 h1). Qed.
Lemma lem4827797 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term240 A t s) : (term255 A s t x) = (s x).
Proof. exact (EQ_MP (@lem4827237 A t s x) (@lem4827796 A x t s h1)). Qed.
Lemma lem4827802 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term240 A t s) : term260 A t s.
Proof. exact (fun x : A -> Prop => @lem4827797 A x t s h1). Qed.
Lemma lem4827803 {A : Type'} (t : type686 A) (s : type686 A) : term261 A t s.
Proof. exact (fun h0 : term240 A t s => @lem4827802 A t s h0). Qed.
Lemma lem4827808 {A : Type'} (s : type686 A) : term271 A s.
Proof. exact (fun t : type686 A => @lem4827803 A t s). Qed.
Lemma lem4827813 {A : Type'} : term275 A.
Proof. exact (fun s : type686 A => @lem4827808 A s). Qed.
Lemma lem4827814 {A : Type'} : term274 A.
Proof. exact (EQ_MP (@lem4827232 A) (@lem4827813 A)). Qed.
Lemma lem4827815 {A : Type'} (s : type686 A) : term329 A s.
Proof. exact (@lem4827814 A s). Qed.
Lemma lem4827816 {A : Type'} (s : type686 A) : (term329 A s) = (term270 A s).
Proof. exact (eq_refl (term329 A s)). Qed.
Lemma lem4827817 {A : Type'} (s : type686 A) : term270 A s.
Proof. exact (EQ_MP (@lem4827816 A s) (@lem4827815 A s)). Qed.
Lemma lem4827818 {A : Type'} (s : type686 A) (t : type686 A) : term330 A s t.
Proof. exact (@lem4827817 A s t). Qed.
Lemma lem4827819 {A : Type'} (t : type686 A) (s : type686 A) : (term330 A s t) = (term262 A t s).
Proof. exact (eq_refl (term330 A s t)). Qed.
Lemma lem4827820 {A : Type'} (t : type686 A) (s : type686 A) : term262 A t s.
Proof. exact (EQ_MP (@lem4827819 A t s) (@lem4827818 A s t)). Qed.
Lemma lem4827822 {A : Type'} (t : type686 A) (s : type686 A) : term262 A t s.
Proof. exact (@lem4827104 A t s (@lem4827820 A t s)). Qed.
Lemma lem4827823 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term263 A t s) : False.
Proof. exact (@lem4827822 A t s (@lem4827088 A t s h1)). Qed.
Lemma lem4827824 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term263 A t s) : (term263 A t s) = False.
Proof. exact (prop_ext (fun h2 : term263 A t s => @lem4827823 A t s h1) (fun h2 : False => @lem4827088 A t s h1)). Qed.
Lemma lem4827825 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term263 A t s) : False.
Proof. exact (EQ_MP (@lem4827824 A t s h1) (@lem4827088 A t s h1)). Qed.
Lemma lem4827826 {A : Type'} (t : type686 A) (s : type686 A) : term262 A t s.
Proof. exact (fun h0 : term263 A t s => @lem4827825 A t s h0). Qed.
Lemma lem4827827 {A : Type'} (t : type686 A) (s : type686 A) : term261 A t s.
Proof. exact (EQ_MP (@lem4827087 A t s) (@lem4827826 A t s)). Qed.
Lemma lem4827828 {A : Type'} (t : type686 A) (s : type686 A) : term231 A t s.
Proof. exact (EQ_MP (@lem4827083 A t s) (@lem4827827 A t s)). Qed.
Lemma lem4827829 {A : Type'} (t : type686 A) (s : type686 A) : term230 A t s.
Proof. exact (EQ_MP (@lem4826982 A t s) (@lem4827828 A t s)). Qed.
Lemma lem4827830 {A : Type'} (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) (h2 : @pairwise (A -> Prop) (@DISJOINT A) s) : (term228 A s t) = s.
Proof. exact (@lem4827829 A t s (@lem4826942 A t s h1 h2)). Qed.
Lemma lem4827831 {A : Type'} (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) (h2 : @pairwise (A -> Prop) (@DISJOINT A) s) : (term216 A s t) = (@UNIONS A s).
Proof. exact (MK_COMB (@lem4826931 A) (@lem4827830 A t s h1 h2)). Qed.
Lemma lem4827832 {A : Type'} (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) (h2 : @pairwise (A -> Prop) (@DISJOINT A) s) : (term215 A s t) = (@UNIONS A s).
Proof. exact (EQ_MP (@lem4826930 A t s) (@lem4827831 A t s h1 h2)). Qed.
Lemma lem4827834 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem4825554 A s t) (@lem4825553 A s t)). Qed.
Lemma lem4827835 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem4827834 A s t). Qed.
Lemma lem4827836 {A : Type'} (s : type686 A) (t : type686 A) : (term331 A s t) = ((term332 A s t) = (@EMPTY A)).
Proof. exact (@lem4827835 A (@UNIONS A t) (term214 A s t)). Qed.
Lemma lem4827840 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term32 _86990 s t) = (term33 _86990 s t).
Proof. exact (EQ_MP (@lem4825548 _86990 s t) (@lem4825547 _86990 s t)). Qed.
Lemma lem4827841 {A : Type'} (s : type686 A) (t : A -> Prop) : (term32 A s t) = (term33 A s t).
Proof. exact (@lem4827840 A s t). Qed.
Lemma lem4827842 {A : Type'} (s : type686 A) (t : type686 A) : (term332 A s t) = (term333 A s t).
Proof. exact (@lem4827841 A t (term214 A s t)). Qed.
Lemma lem4827848 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term26 _87026 t s) = (term27 _87026 s t).
Proof. exact (EQ_MP (@lem4825541 _87026 s t) (@lem4825540 _87026 s t)). Qed.
Lemma lem4827849 {A : Type'} (s : type686 A) (t : A -> Prop) : (term26 A t s) = (term27 A s t).
Proof. exact (@lem4827848 A s t). Qed.
Lemma lem4827850 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term334 A x s t) = (term335 A s t x).
Proof. exact (@lem4827849 A (@DIFF (A -> Prop) s t) x). Qed.
Lemma lem4827855 {A : Type'} (GEN_PVAR_21 : A -> Prop) (x : A -> Prop) (t : type686 A) : (term336 A GEN_PVAR_21 x t) = (term336 A GEN_PVAR_21 x t).
Proof. exact (eq_refl (term336 A GEN_PVAR_21 x t)). Qed.
Lemma lem4827856 {A : Type'} (GEN_PVAR_21 : A -> Prop) (s : type686 A) (t : type686 A) (x : A -> Prop) : (term337 A GEN_PVAR_21 x s t) = (term338 A GEN_PVAR_21 s t x).
Proof. exact (MK_COMB (@lem4827855 A GEN_PVAR_21 x t) (@lem4827850 A s t x)). Qed.
Lemma lem4827857 {A : Type'} (GEN_PVAR_21 : A -> Prop) (s : type686 A) (t : type686 A) : (term339 A GEN_PVAR_21 s t) = (term340 A GEN_PVAR_21 s t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4827856 A GEN_PVAR_21 s t x)). Qed.
Lemma lem4827858 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4827859 {A : Type'} (GEN_PVAR_21 : A -> Prop) (s : type686 A) (t : type686 A) : (term341 A GEN_PVAR_21 s t) = (term342 A GEN_PVAR_21 s t).
Proof. exact (MK_COMB (@lem4827858 A) (@lem4827857 A GEN_PVAR_21 s t)). Qed.
Lemma lem4827864 {A : Type'} (s : type686 A) (t : type686 A) : (term343 A s t) = (term344 A s t).
Proof. exact (fun_ext (fun GEN_PVAR_21 : A -> Prop => @lem4827859 A GEN_PVAR_21 s t)). Qed.
Lemma lem4827865 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4827866 {A : Type'} (s : type686 A) (t : type686 A) : (term345 A s t) = (term346 A s t).
Proof. exact (MK_COMB (@lem4827865 A) (@lem4827864 A s t)). Qed.
Lemma lem4827867 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4827868 {A : Type'} (s : type686 A) (t : type686 A) : (term333 A s t) = (term347 A s t).
Proof. exact (MK_COMB (@lem4827867 A) (@lem4827866 A s t)). Qed.
Lemma lem4827869 {A : Type'} (s : type686 A) (t : type686 A) : (term332 A s t) = (term347 A s t).
Proof. exact (TRANS (@lem4827842 A s t) (@lem4827868 A s t)). Qed.
Lemma lem4827870 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4827871 {A : Type'} (s : type686 A) (t : type686 A) : (term348 A s t) = (term349 A s t).
Proof. exact (MK_COMB (@lem4827870 A) (@lem4827869 A s t)). Qed.
Lemma lem4827872 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem4827873 {A : Type'} (s : type686 A) (t : type686 A) : ((term332 A s t) = (@EMPTY A)) = ((term347 A s t) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem4827871 A s t) (@lem4827872 A)). Qed.
Lemma lem4827875 {_86951 : Type'} (s : type686 _86951) : ((@UNIONS _86951 s) = (@EMPTY _86951)) = (term21 _86951 s).
Proof. exact (EQ_MP (@lem4825534 _86951 s) (@lem4825533 _86951 s)). Qed.
Lemma lem4827876 {A : Type'} (s : type686 A) : ((@UNIONS A s) = (@EMPTY A)) = (term21 A s).
Proof. exact (@lem4827875 A s). Qed.
Lemma lem4827877 {A : Type'} (s : type686 A) (t : type686 A) : ((term347 A s t) = (@EMPTY A)) = (term350 A s t).
Proof. exact (@lem4827876 A (term346 A s t)). Qed.
Lemma lem4827879 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term18 _88905 _89106 P f Q) = (term19 _88905 _89106 P Q f).
Proof. exact (EQ_MP (@lem4825531 _88905 _89106 P Q f) (@lem4825530 _88905 _89106 P Q f)). Qed.
Lemma lem4827880 {A : Type'} (P : type686 A) (Q : type686 A) (f : type672 A) : (term351 A P f Q) = (term352 A P Q f).
Proof. exact (@lem4827879 (A -> Prop) (A -> Prop) P Q f). Qed.
Lemma lem4827881 {A : Type'} (s : type686 A) (t : type686 A) : (term353 A s t) = (term354 A s t).
Proof. exact (@lem4827880 A (term355 A t) (term356 A) (term357 A s t)). Qed.
Lemma lem4827882 {A : Type'} (x : A -> Prop) (t : type686 A) : (term358 A t x) = (@IN (A -> Prop) x t).
Proof. exact (eq_refl (term358 A t x)). Qed.
Lemma lem4827883 {A : Type'} (GEN_PVAR_21 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_21) = (@SETSPEC (A -> Prop) GEN_PVAR_21).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_21)). Qed.
Lemma lem4827884 {A : Type'} (GEN_PVAR_21 : A -> Prop) (x : A -> Prop) (t : type686 A) : (term359 A GEN_PVAR_21 t x) = (term336 A GEN_PVAR_21 x t).
Proof. exact (MK_COMB (@lem4827883 A GEN_PVAR_21) (@lem4827882 A x t)). Qed.
Lemma lem4827885 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term360 A s t x) = (term335 A s t x).
Proof. exact (eq_refl (term360 A s t x)). Qed.
Lemma lem4827886 {A : Type'} (GEN_PVAR_21 : A -> Prop) (s : type686 A) (t : type686 A) (x : A -> Prop) : (term361 A GEN_PVAR_21 s t x) = (term338 A GEN_PVAR_21 s t x).
Proof. exact (MK_COMB (@lem4827884 A GEN_PVAR_21 x t) (@lem4827885 A s t x)). Qed.
Lemma lem4827887 {A : Type'} (GEN_PVAR_21 : A -> Prop) (s : type686 A) (t : type686 A) : (term362 A GEN_PVAR_21 s t) = (term340 A GEN_PVAR_21 s t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4827886 A GEN_PVAR_21 s t x)). Qed.
Lemma lem4827888 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4827889 {A : Type'} (GEN_PVAR_21 : A -> Prop) (s : type686 A) (t : type686 A) : (term363 A GEN_PVAR_21 s t) = (term342 A GEN_PVAR_21 s t).
Proof. exact (MK_COMB (@lem4827888 A) (@lem4827887 A GEN_PVAR_21 s t)). Qed.
Lemma lem4827890 {A : Type'} (s : type686 A) (t : type686 A) : (term364 A s t) = (term344 A s t).
Proof. exact (fun_ext (fun GEN_PVAR_21 : A -> Prop => @lem4827889 A GEN_PVAR_21 s t)). Qed.
Lemma lem4827891 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4827892 {A : Type'} (s : type686 A) (t : type686 A) : (term365 A s t) = (term346 A s t).
Proof. exact (MK_COMB (@lem4827891 A) (@lem4827890 A s t)). Qed.
Lemma lem4827893 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t) = (@IN (A -> Prop) t).
Proof. exact (eq_refl (@IN (A -> Prop) t)). Qed.
Lemma lem4827894 {A : Type'} (t : A -> Prop) (s : type686 A) (t' : type686 A) : (term366 A t s t') = (term367 A t s t').
Proof. exact (MK_COMB (@lem4827893 A t) (@lem4827892 A s t')). Qed.
Lemma lem4827895 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4827896 {A : Type'} (t : A -> Prop) (s : type686 A) (t' : type686 A) : (term368 A t s t') = (term369 A t s t').
Proof. exact (MK_COMB (@lem4827895) (@lem4827894 A t s t')). Qed.
Lemma lem4827897 {A : Type'} (t : A -> Prop) : (term370 A t) = (t = (@EMPTY A)).
Proof. exact (eq_refl (term370 A t)). Qed.
Lemma lem4827898 {A : Type'} (s : type686 A) (t : type686 A) (t' : A -> Prop) : (term371 A s t t') = (term372 A s t t').
Proof. exact (MK_COMB (@lem4827896 A t' s t) (@lem4827897 A t')). Qed.
Lemma lem4827899 {A : Type'} (s : type686 A) (t : type686 A) : (term373 A s t) = (term374 A s t).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4827898 A s t t')). Qed.
Lemma lem4827900 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4827901 {A : Type'} (s : type686 A) (t : type686 A) : (term353 A s t) = (term350 A s t).
Proof. exact (MK_COMB (@lem4827900 A) (@lem4827899 A s t)). Qed.
Lemma lem4827902 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4827903 {A : Type'} (s : type686 A) (t : type686 A) : (term375 A s t) = (term376 A s t).
Proof. exact (MK_COMB (@lem4827902) (@lem4827901 A s t)). Qed.
Lemma lem4827904 {A : Type'} (x : A -> Prop) (t : type686 A) : (term358 A t x) = (@IN (A -> Prop) x t).
Proof. exact (eq_refl (term358 A t x)). Qed.
Lemma lem4827905 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4827906 {A : Type'} (x : A -> Prop) (t : type686 A) : (term377 A t x) = (term232 A x t).
Proof. exact (MK_COMB (@lem4827905) (@lem4827904 A x t)). Qed.
Lemma lem4827907 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term378 A s t x) = ((term360 A s t x) = (@EMPTY A)).
Proof. exact (eq_refl (term378 A s t x)). Qed.
Lemma lem4827908 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term379 A s t x) = (term380 A s t x).
Proof. exact (MK_COMB (@lem4827906 A x t) (@lem4827907 A s t x)). Qed.
Lemma lem4827909 {A : Type'} (s : type686 A) (t : type686 A) : (term381 A s t) = (term382 A s t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4827908 A s t x)). Qed.
Lemma lem4827910 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4827911 {A : Type'} (s : type686 A) (t : type686 A) : (term354 A s t) = (term383 A s t).
Proof. exact (MK_COMB (@lem4827910 A) (@lem4827909 A s t)). Qed.
Lemma lem4827912 {A : Type'} (s : type686 A) (t : type686 A) : ((term353 A s t) = (term354 A s t)) = ((term350 A s t) = (term383 A s t)).
Proof. exact (MK_COMB (@lem4827903 A s t) (@lem4827911 A s t)). Qed.
Lemma lem4827913 {A : Type'} (s : type686 A) (t : type686 A) : (term350 A s t) = (term383 A s t).
Proof. exact (EQ_MP (@lem4827912 A s t) (@lem4827881 A s t)). Qed.
Lemma lem4827923 {A B : Type'} (f : A -> B) (y : A) : (term384 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4827924 {A : Type'} (f : type672 A) (y : A -> Prop) : (term385 A f y) = (f y).
Proof. exact (@lem4827923 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4827925 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term386 A s t x) = (term360 A s t x).
Proof. exact (@lem4827924 A (term357 A s t) x). Qed.
Lemma lem4827926 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term360 A s t x) = (term335 A s t x).
Proof. exact (eq_refl (term360 A s t x)). Qed.
Lemma lem4827927 {A : Type'} (s : type686 A) (t : type686 A) : (term387 A s t) = (term357 A s t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4827926 A s t x)). Qed.
Lemma lem4827928 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4827929 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term386 A s t x) = (term360 A s t x).
Proof. exact (MK_COMB (@lem4827927 A s t) (@lem4827928 A x)). Qed.
Lemma lem4827930 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4827931 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term388 A s t x) = (term389 A s t x).
Proof. exact (MK_COMB (@lem4827930 A) (@lem4827929 A s t x)). Qed.
Lemma lem4827932 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term360 A s t x) = (term335 A s t x).
Proof. exact (eq_refl (term360 A s t x)). Qed.
Lemma lem4827933 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : ((term386 A s t x) = (term360 A s t x)) = ((term360 A s t x) = (term335 A s t x)).
Proof. exact (MK_COMB (@lem4827931 A s t x) (@lem4827932 A s t x)). Qed.
Lemma lem4827934 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term360 A s t x) = (term335 A s t x).
Proof. exact (EQ_MP (@lem4827933 A s t x) (@lem4827925 A s t x)). Qed.
Lemma lem4827939 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4827940 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term389 A s t x) = (term390 A s t x).
Proof. exact (MK_COMB (@lem4827939 A) (@lem4827934 A s t x)). Qed.
Lemma lem4827941 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem4827942 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : ((term360 A s t x) = (@EMPTY A)) = ((term335 A s t x) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem4827940 A s t x) (@lem4827941 A)). Qed.
Lemma lem4827944 {_86951 : Type'} (s : type686 _86951) : ((@UNIONS _86951 s) = (@EMPTY _86951)) = (term21 _86951 s).
Proof. exact (EQ_MP (@lem4825534 _86951 s) (@lem4825533 _86951 s)). Qed.
Lemma lem4827945 {A : Type'} (s : type686 A) : ((@UNIONS A s) = (@EMPTY A)) = (term21 A s).
Proof. exact (@lem4827944 A s). Qed.
Lemma lem4827946 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : ((term335 A s t x) = (@EMPTY A)) = (term391 A s t x).
Proof. exact (@lem4827945 A (term392 A s t x)). Qed.
Lemma lem4827948 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term18 _88905 _89106 P f Q) = (term19 _88905 _89106 P Q f).
Proof. exact (EQ_MP (@lem4825531 _88905 _89106 P Q f) (@lem4825530 _88905 _89106 P Q f)). Qed.
Lemma lem4827949 {A : Type'} (P : type686 A) (Q : type686 A) (f : type672 A) : (term351 A P f Q) = (term352 A P Q f).
Proof. exact (@lem4827948 (A -> Prop) (A -> Prop) P Q f). Qed.
Lemma lem4827950 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term393 A s t x) = (term394 A s t x).
Proof. exact (@lem4827949 A (term395 A s t) (term356 A) (term396 A x)). Qed.
Lemma lem4827951 {A : Type'} (x' : A -> Prop) (s : type686 A) (t : type686 A) : (term397 A s t x') = (term248 A x' s t).
Proof. exact (eq_refl (term397 A s t x')). Qed.
Lemma lem4827952 {A : Type'} (GEN_PVAR_22 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_22) = (@SETSPEC (A -> Prop) GEN_PVAR_22).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_22)). Qed.
Lemma lem4827953 {A : Type'} (GEN_PVAR_22 : A -> Prop) (x' : A -> Prop) (s : type686 A) (t : type686 A) : (term398 A GEN_PVAR_22 s t x') = (term399 A GEN_PVAR_22 x' s t).
Proof. exact (MK_COMB (@lem4827952 A GEN_PVAR_22) (@lem4827951 A x' s t)). Qed.
Lemma lem4827954 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term400 A x x') = (@INTER A x x').
Proof. exact (eq_refl (term400 A x x')). Qed.
Lemma lem4827955 {A : Type'} (GEN_PVAR_22 : A -> Prop) (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term401 A GEN_PVAR_22 s t x x') = (term402 A GEN_PVAR_22 s t x x').
Proof. exact (MK_COMB (@lem4827953 A GEN_PVAR_22 x' s t) (@lem4827954 A x x')). Qed.
Lemma lem4827956 {A : Type'} (GEN_PVAR_22 : A -> Prop) (s : type686 A) (t : type686 A) (x : A -> Prop) : (term403 A GEN_PVAR_22 s t x) = (term404 A GEN_PVAR_22 s t x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4827955 A GEN_PVAR_22 s t x x')). Qed.
Lemma lem4827957 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4827958 {A : Type'} (GEN_PVAR_22 : A -> Prop) (s : type686 A) (t : type686 A) (x : A -> Prop) : (term405 A GEN_PVAR_22 s t x) = (term406 A GEN_PVAR_22 s t x).
Proof. exact (MK_COMB (@lem4827957 A) (@lem4827956 A GEN_PVAR_22 s t x)). Qed.
Lemma lem4827959 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term407 A s t x) = (term408 A s t x).
Proof. exact (fun_ext (fun GEN_PVAR_22 : A -> Prop => @lem4827958 A GEN_PVAR_22 s t x)). Qed.
Lemma lem4827960 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4827961 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term409 A s t x) = (term392 A s t x).
Proof. exact (MK_COMB (@lem4827960 A) (@lem4827959 A s t x)). Qed.
Lemma lem4827962 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t) = (@IN (A -> Prop) t).
Proof. exact (eq_refl (@IN (A -> Prop) t)). Qed.
Lemma lem4827963 {A : Type'} (t : A -> Prop) (s : type686 A) (t' : type686 A) (x : A -> Prop) : (term410 A t s t' x) = (term411 A t s t' x).
Proof. exact (MK_COMB (@lem4827962 A t) (@lem4827961 A s t' x)). Qed.
Lemma lem4827964 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4827965 {A : Type'} (t : A -> Prop) (s : type686 A) (t' : type686 A) (x : A -> Prop) : (term412 A t s t' x) = (term413 A t s t' x).
Proof. exact (MK_COMB (@lem4827964) (@lem4827963 A t s t' x)). Qed.
Lemma lem4827966 {A : Type'} (t : A -> Prop) : (term370 A t) = (t = (@EMPTY A)).
Proof. exact (eq_refl (term370 A t)). Qed.
Lemma lem4827967 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (t' : A -> Prop) : (term414 A s t x t') = (term415 A s t x t').
Proof. exact (MK_COMB (@lem4827965 A t' s t x) (@lem4827966 A t')). Qed.
Lemma lem4827968 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term416 A s t x) = (term417 A s t x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4827967 A s t x t')). Qed.
Lemma lem4827969 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4827970 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term393 A s t x) = (term391 A s t x).
Proof. exact (MK_COMB (@lem4827969 A) (@lem4827968 A s t x)). Qed.
Lemma lem4827971 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4827972 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term418 A s t x) = (term419 A s t x).
Proof. exact (MK_COMB (@lem4827971) (@lem4827970 A s t x)). Qed.
Lemma lem4827973 {A : Type'} (x' : A -> Prop) (s : type686 A) (t : type686 A) : (term397 A s t x') = (term248 A x' s t).
Proof. exact (eq_refl (term397 A s t x')). Qed.
Lemma lem4827974 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4827975 {A : Type'} (x' : A -> Prop) (s : type686 A) (t : type686 A) : (term420 A s t x') = (term421 A x' s t).
Proof. exact (MK_COMB (@lem4827974) (@lem4827973 A x' s t)). Qed.
Lemma lem4827976 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term422 A x x') = ((term400 A x x') = (@EMPTY A)).
Proof. exact (eq_refl (term422 A x x')). Qed.
Lemma lem4827977 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term423 A s t x x') = (term424 A s t x x').
Proof. exact (MK_COMB (@lem4827975 A x' s t) (@lem4827976 A x x')). Qed.
Lemma lem4827978 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term425 A s t x) = (term426 A s t x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4827977 A s t x x')). Qed.
Lemma lem4827979 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4827980 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term394 A s t x) = (term427 A s t x).
Proof. exact (MK_COMB (@lem4827979 A) (@lem4827978 A s t x)). Qed.
Lemma lem4827981 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : ((term393 A s t x) = (term394 A s t x)) = ((term391 A s t x) = (term427 A s t x)).
Proof. exact (MK_COMB (@lem4827972 A s t x) (@lem4827980 A s t x)). Qed.
Lemma lem4827982 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term391 A s t x) = (term427 A s t x).
Proof. exact (EQ_MP (@lem4827981 A s t x) (@lem4827950 A s t x)). Qed.
Lemma lem4827992 {A B : Type'} (f : A -> B) (y : A) : (term384 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4827993 {A : Type'} (f : type672 A) (y : A -> Prop) : (term385 A f y) = (f y).
Proof. exact (@lem4827992 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4827994 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term428 A x x') = (term400 A x x').
Proof. exact (@lem4827993 A (term396 A x) x'). Qed.
Lemma lem4827995 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term400 A x x') = (@INTER A x x').
Proof. exact (eq_refl (term400 A x x')). Qed.
Lemma lem4827996 {A : Type'} (x : A -> Prop) : (term429 A x) = (term396 A x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4827995 A x x')). Qed.
Lemma lem4827997 {A : Type'} (x' : A -> Prop) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem4827998 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term428 A x x') = (term400 A x x').
Proof. exact (MK_COMB (@lem4827996 A x) (@lem4827997 A x')). Qed.
Lemma lem4827999 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4828000 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term430 A x x') = (term431 A x x').
Proof. exact (MK_COMB (@lem4827999 A) (@lem4827998 A x x')). Qed.
Lemma lem4828001 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term400 A x x') = (@INTER A x x').
Proof. exact (eq_refl (term400 A x x')). Qed.
Lemma lem4828002 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : ((term428 A x x') = (term400 A x x')) = ((term400 A x x') = (@INTER A x x')).
Proof. exact (MK_COMB (@lem4828000 A x x') (@lem4828001 A x x')). Qed.
Lemma lem4828003 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term400 A x x') = (@INTER A x x').
Proof. exact (EQ_MP (@lem4828002 A x x') (@lem4827994 A x x')). Qed.
Lemma lem4828004 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4828005 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term431 A x x') = (term432 A x x').
Proof. exact (MK_COMB (@lem4828004 A) (@lem4828003 A x x')). Qed.
Lemma lem4828006 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem4828007 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : ((term400 A x x') = (@EMPTY A)) = ((@INTER A x x') = (@EMPTY A)).
Proof. exact (MK_COMB (@lem4828005 A x x') (@lem4828006 A)). Qed.
Lemma lem4828010 {A : Type'} (x' : A -> Prop) (s : type686 A) (t : type686 A) : (term421 A x' s t) = (term421 A x' s t).
Proof. exact (eq_refl (term421 A x' s t)). Qed.
Lemma lem4828011 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term424 A s t x x') = (term433 A s t x x').
Proof. exact (MK_COMB (@lem4828010 A x' s t) (@lem4828007 A x x')). Qed.
Lemma lem4828014 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term426 A s t x) = (term434 A s t x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4828011 A s t x x')). Qed.
Lemma lem4828015 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828016 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term427 A s t x) = (term435 A s t x).
Proof. exact (MK_COMB (@lem4828015 A) (@lem4828014 A s t x)). Qed.
Lemma lem4828021 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term391 A s t x) = (term435 A s t x).
Proof. exact (TRANS (@lem4827982 A s t x) (@lem4828016 A s t x)). Qed.
Lemma lem4828022 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : ((term335 A s t x) = (@EMPTY A)) = (term435 A s t x).
Proof. exact (TRANS (@lem4827946 A s t x) (@lem4828021 A s t x)). Qed.
Lemma lem4828023 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : ((term360 A s t x) = (@EMPTY A)) = (term435 A s t x).
Proof. exact (TRANS (@lem4827942 A s t x) (@lem4828022 A s t x)). Qed.
Lemma lem4828024 {A : Type'} (x : A -> Prop) (t : type686 A) : (term232 A x t) = (term232 A x t).
Proof. exact (eq_refl (term232 A x t)). Qed.
Lemma lem4828025 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term380 A s t x) = (term436 A s t x).
Proof. exact (MK_COMB (@lem4828024 A x t) (@lem4828023 A s t x)). Qed.
Lemma lem4828028 {A : Type'} (s : type686 A) (t : type686 A) : (term382 A s t) = (term437 A s t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4828025 A s t x)). Qed.
Lemma lem4828029 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828030 {A : Type'} (s : type686 A) (t : type686 A) : (term383 A s t) = (term438 A s t).
Proof. exact (MK_COMB (@lem4828029 A) (@lem4828028 A s t)). Qed.
Lemma lem4828035 {A : Type'} (s : type686 A) (t : type686 A) : (term350 A s t) = (term438 A s t).
Proof. exact (TRANS (@lem4827913 A s t) (@lem4828030 A s t)). Qed.
Lemma lem4828036 {A : Type'} (s : type686 A) (t : type686 A) : ((term347 A s t) = (@EMPTY A)) = (term438 A s t).
Proof. exact (TRANS (@lem4827877 A s t) (@lem4828035 A s t)). Qed.
Lemma lem4828037 {A : Type'} (s : type686 A) (t : type686 A) : ((term332 A s t) = (@EMPTY A)) = (term438 A s t).
Proof. exact (TRANS (@lem4827873 A s t) (@lem4828036 A s t)). Qed.
Lemma lem4828038 {A : Type'} (s : type686 A) (t : type686 A) : (term331 A s t) = (term438 A s t).
Proof. exact (TRANS (@lem4827836 A s t) (@lem4828037 A s t)). Qed.
Lemma lem4828039 {A : Type'} (s : type686 A) (t : type686 A) : (term438 A s t) = (term331 A s t).
Proof. exact (SYM (@lem4828038 A s t)). Qed.
Lemma lem4828041 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term13 _110510 s r).
Proof. exact (EQ_MP (@lem4825501 _110510 s r) (@lem4825500 _110510 s r)). Qed.
Lemma lem4828042 {A : Type'} (s : type686 A) (r : type639 A) : (@pairwise (A -> Prop) r s) = (term439 A s r).
Proof. exact (@lem4828041 (A -> Prop) s r). Qed.
Lemma lem4828043 {A : Type'} (s : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) s) = (term440 A s).
Proof. exact (@lem4828042 A s (@DISJOINT A)). Qed.
Lemma lem4828044 {A : Type'} (s : type686 A) (h1 : @pairwise (A -> Prop) (@DISJOINT A) s) : term440 A s.
Proof. exact (EQ_MP (@lem4828043 A s) (@lem4826913 A s h1)). Qed.
Lemma lem4828064 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem4825495 A s t) (@lem4825494 A s t)). Qed.
Lemma lem4828065 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem4828064 A s t). Qed.
Lemma lem4828066 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (@DISJOINT A x y) = ((@INTER A x y) = (@EMPTY A)).
Proof. exact (@lem4828065 A x y). Qed.
Lemma lem4828069 {A : Type'} (s : type686 A) (x : A -> Prop) (y : A -> Prop) : (term441 A s x y) = (term441 A s x y).
Proof. exact (eq_refl (term441 A s x y)). Qed.
Lemma lem4828070 {A : Type'} (s : type686 A) (x : A -> Prop) (y : A -> Prop) : (term442 A s x y) = (term443 A s x y).
Proof. exact (MK_COMB (@lem4828069 A s x y) (@lem4828066 A x y)). Qed.
Lemma lem4828073 {A : Type'} (s : type686 A) (x : A -> Prop) : (term444 A s x) = (term445 A s x).
Proof. exact (fun_ext (fun y : A -> Prop => @lem4828070 A s x y)). Qed.
Lemma lem4828074 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828075 {A : Type'} (s : type686 A) (x : A -> Prop) : (term446 A s x) = (term447 A s x).
Proof. exact (MK_COMB (@lem4828074 A) (@lem4828073 A s x)). Qed.
Lemma lem4828080 {A : Type'} (s : type686 A) : (term448 A s) = (term449 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4828075 A s x)). Qed.
Lemma lem4828081 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828082 {A : Type'} (s : type686 A) : (term440 A s) = (term450 A s).
Proof. exact (MK_COMB (@lem4828081 A) (@lem4828080 A s)). Qed.
Lemma lem4828087 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4828088 {A : Type'} (s : type686 A) : (term451 A s) = (term452 A s).
Proof. exact (MK_COMB (@lem4828087) (@lem4828082 A s)). Qed.
Lemma lem4828102 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (EQ_MP (@lem4825489 A s x t) (@lem4825488 A s t x)). Qed.
Lemma lem4828103 {A : Type'} (s : type686 A) (x : A -> Prop) (t : type686 A) : (term248 A x s t) = (term249 A s x t).
Proof. exact (@lem4828102 (A -> Prop) s x t). Qed.
Lemma lem4828104 {A : Type'} (s : type686 A) (x' : A -> Prop) (t : type686 A) : (term248 A x' s t) = (term249 A s x' t).
Proof. exact (@lem4828103 A s x' t). Qed.
Lemma lem4828107 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4828108 {A : Type'} (s : type686 A) (x' : A -> Prop) (t : type686 A) : (term421 A x' s t) = (term453 A s x' t).
Proof. exact (MK_COMB (@lem4828107) (@lem4828104 A s x' t)). Qed.
Lemma lem4828111 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : ((@INTER A x x') = (@EMPTY A)) = ((@INTER A x x') = (@EMPTY A)).
Proof. exact (eq_refl ((@INTER A x x') = (@EMPTY A))). Qed.
Lemma lem4828112 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term433 A s t x x') = (term454 A s t x x').
Proof. exact (MK_COMB (@lem4828108 A s x' t) (@lem4828111 A x x')). Qed.
Lemma lem4828115 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term434 A s t x) = (term455 A s t x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4828112 A s t x x')). Qed.
Lemma lem4828116 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828117 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term435 A s t x) = (term456 A s t x).
Proof. exact (MK_COMB (@lem4828116 A) (@lem4828115 A s t x)). Qed.
Lemma lem4828122 {A : Type'} (x : A -> Prop) (t : type686 A) : (term232 A x t) = (term232 A x t).
Proof. exact (eq_refl (term232 A x t)). Qed.
Lemma lem4828123 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term436 A s t x) = (term457 A s t x).
Proof. exact (MK_COMB (@lem4828122 A x t) (@lem4828117 A s t x)). Qed.
Lemma lem4828126 {A : Type'} (s : type686 A) (t : type686 A) : (term437 A s t) = (term458 A s t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4828123 A s t x)). Qed.
Lemma lem4828127 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828128 {A : Type'} (s : type686 A) (t : type686 A) : (term438 A s t) = (term459 A s t).
Proof. exact (MK_COMB (@lem4828127 A) (@lem4828126 A s t)). Qed.
Lemma lem4828133 {A : Type'} (s : type686 A) (t : type686 A) : (term460 A s t) = (term461 A s t).
Proof. exact (MK_COMB (@lem4828088 A s) (@lem4828128 A s t)). Qed.
Lemma lem4828136 {A : Type'} (s : type686 A) (t : type686 A) : (term461 A s t) = (term460 A s t).
Proof. exact (SYM (@lem4828133 A s t)). Qed.
Lemma lem4828137 {A : Type'} (s : type686 A) (h1 : term450 A s) : term450 A s.
Proof. exact (h1). Qed.
Lemma lem4828138 {A : Type'} (x : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) x t) : @IN (A -> Prop) x t.
Proof. exact (h1). Qed.
Lemma lem4828139 {A : Type'} (s : type686 A) (x' : A -> Prop) (t : type686 A) (h1 : term249 A s x' t) : term249 A s x' t.
Proof. exact (h1). Qed.
Lemma lem4828140 {A : Type'} (x' : A -> Prop) (t : type686 A) (h1 : term252 A x' t) : term252 A x' t.
Proof. exact (h1). Qed.
Lemma lem4828141 {A : Type'} (x' : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) x' s) : @IN (A -> Prop) x' s.
Proof. exact (h1). Qed.
Lemma lem4828142 {A : Type'} (s : type686 A) (h1 : term450 A s) : term450 A s.
Proof. exact (h1). Qed.
Lemma lem4828143 {A : Type'} (x : A -> Prop) (s : type686 A) (h1 : term450 A s) : term462 A s x.
Proof. exact (@lem4828142 A s h1 x). Qed.
Lemma lem4828144 {A : Type'} (s : type686 A) (x : A -> Prop) : (term462 A s x) = (term447 A s x).
Proof. exact (eq_refl (term462 A s x)). Qed.
Lemma lem4828145 {A : Type'} (x : A -> Prop) (s : type686 A) (h1 : term450 A s) : term447 A s x.
Proof. exact (EQ_MP (@lem4828144 A s x) (@lem4828143 A x s h1)). Qed.
Lemma lem4828146 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : type686 A) (h1 : term450 A s) : term463 A s x y.
Proof. exact (@lem4828145 A x s h1 y). Qed.
Lemma lem4828147 {A : Type'} (s : type686 A) (x : A -> Prop) (y : A -> Prop) : (term463 A s x y) = (term443 A s x y).
Proof. exact (eq_refl (term463 A s x y)). Qed.
Lemma lem4828148 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : type686 A) (h1 : term450 A s) : term443 A s x y.
Proof. exact (EQ_MP (@lem4828147 A s x y) (@lem4828146 A x y s h1)). Qed.
Lemma lem4828149 {A : Type'} (s : type686 A) (x : A -> Prop) (y : A -> Prop) (h1 : term464 A s x y) : term464 A s x y.
Proof. exact (h1). Qed.
Lemma lem4828150 {A : Type'} (s : type686 A) (x : A -> Prop) (y : A -> Prop) (h1 : term450 A s) (h2 : term464 A s x y) : (@INTER A x y) = (@EMPTY A).
Proof. exact (@lem4828148 A x y s h1 (@lem4828149 A s x y h2)). Qed.
Lemma lem4828151 {A : Type'} (s : type686 A) (x : A -> Prop) (y : A -> Prop) (h1 : term464 A s x y) : term465 A s x y.
Proof. exact (fun h0 : term450 A s => @lem4828150 A s x y h0 h1). Qed.
Lemma lem4828152 {A : Type'} (s : type686 A) (h1 : term450 A s) : term450 A s.
Proof. exact (h1). Qed.
Lemma lem4828153 {A : Type'} (s : type686 A) (x : A -> Prop) (y : A -> Prop) (h1 : term450 A s) (h2 : term464 A s x y) : (@INTER A x y) = (@EMPTY A).
Proof. exact (@lem4828151 A s x y h2 (@lem4828152 A s h1)). Qed.
Lemma lem4828154 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : type686 A) (h1 : term450 A s) : term443 A s x y.
Proof. exact (fun h0 : term464 A s x y => @lem4828153 A s x y h1 h0). Qed.
Lemma lem4828155 {A : Type'} (x : A -> Prop) (s : type686 A) (h1 : term450 A s) : term447 A s x.
Proof. exact (fun y : A -> Prop => @lem4828154 A x y s h1). Qed.
Lemma lem4828156 {A : Type'} (s : type686 A) (h1 : term450 A s) : term450 A s.
Proof. exact (fun x : A -> Prop => @lem4828155 A x s h1). Qed.
Lemma lem4828157 {A : Type'} (s : type686 A) : term466 A s.
Proof. exact (fun h0 : term450 A s => @lem4828156 A s h0). Qed.
Lemma lem4828158 {A : Type'} (s : type686 A) (h1 : term450 A s) : term450 A s.
Proof. exact (@lem4828157 A s (@lem4828137 A s h1)). Qed.
Lemma lem4828159 {A : Type'} (x : A -> Prop) (s : type686 A) (h1 : term450 A s) : term462 A s x.
Proof. exact (@lem4828158 A s h1 x). Qed.
Lemma lem4828160 {A : Type'} (s : type686 A) (x : A -> Prop) : (term462 A s x) = (term447 A s x).
Proof. exact (eq_refl (term462 A s x)). Qed.
Lemma lem4828161 {A : Type'} (x : A -> Prop) (s : type686 A) (h1 : term450 A s) : term447 A s x.
Proof. exact (EQ_MP (@lem4828160 A s x) (@lem4828159 A x s h1)). Qed.
Lemma lem4828162 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : type686 A) (h1 : term450 A s) : term463 A s x y.
Proof. exact (@lem4828161 A x s h1 y). Qed.
Lemma lem4828163 {A : Type'} (s : type686 A) (x : A -> Prop) (y : A -> Prop) : (term463 A s x y) = (term443 A s x y).
Proof. exact (eq_refl (term463 A s x y)). Qed.
Lemma lem4828166 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : type686 A) (h1 : term450 A s) : term443 A s x y.
Proof. exact (EQ_MP (@lem4828163 A s x y) (@lem4828162 A x y s h1)). Qed.
Lemma lem4828167 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : type686 A) (h1 : term450 A s) : term443 A s x y.
Proof. exact (@lem4828166 A x y s h1). Qed.
Lemma lem4828168 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (s : type686 A) (h1 : term450 A s) : term443 A s x x'.
Proof. exact (@lem4828167 A x x' s h1). Qed.
Lemma lem4828179 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : @IN (A -> Prop) x t) (h2 : @SUBSET (A -> Prop) t s) : term467 A x t s.
Proof. exact (conj (@lem4828138 A x t h1) (@lem4826912 A t s h2)). Qed.
Lemma lem4828180 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : @IN (A -> Prop) x t) (h2 : @IN (A -> Prop) x' s) (h3 : @SUBSET (A -> Prop) t s) : term468 A x' x t s.
Proof. exact (conj (@lem4828141 A x' s h2) (@lem4828179 A x t s h1 h3)). Qed.
Lemma lem4828181 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term252 A x' t) (h2 : @IN (A -> Prop) x t) (h3 : @IN (A -> Prop) x' s) (h4 : @SUBSET (A -> Prop) t s) : term469 A x' x t s.
Proof. exact (conj (@lem4828140 A x' t h1) (@lem4828180 A x x' t s h2 h3 h4)). Qed.
Lemma lem4828191 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term220 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4828192 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term221 A s t).
Proof. exact (@lem4828191 (A -> Prop) s t). Qed.
Lemma lem4828193 {A : Type'} (t : type686 A) (s : type686 A) : (@SUBSET (A -> Prop) t s) = (term221 A t s).
Proof. exact (@lem4828192 A t s). Qed.
Lemma lem4828200 {A : Type'} (x : A -> Prop) (t : type686 A) : (term250 A x t) = (term250 A x t).
Proof. exact (eq_refl (term250 A x t)). Qed.
Lemma lem4828201 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) : (term467 A x t s) = (term470 A x t s).
Proof. exact (MK_COMB (@lem4828200 A x t) (@lem4828193 A t s)). Qed.
Lemma lem4828204 {A : Type'} (x' : A -> Prop) (s : type686 A) : (term250 A x' s) = (term250 A x' s).
Proof. exact (eq_refl (term250 A x' s)). Qed.
Lemma lem4828205 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term468 A x' x t s) = (term471 A x' x t s).
Proof. exact (MK_COMB (@lem4828204 A x' s) (@lem4828201 A x t s)). Qed.
Lemma lem4828208 {A : Type'} (x' : A -> Prop) (t : type686 A) : (term472 A x' t) = (term472 A x' t).
Proof. exact (eq_refl (term472 A x' t)). Qed.
Lemma lem4828209 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term469 A x' x t s) = (term473 A x' x t s).
Proof. exact (MK_COMB (@lem4828208 A x' t) (@lem4828205 A x' x t s)). Qed.
Lemma lem4828212 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4828213 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term474 A x' x t s) = (term475 A x' x t s).
Proof. exact (MK_COMB (@lem4828212) (@lem4828209 A x' x t s)). Qed.
Lemma lem4828214 {A : Type'} (x : A -> Prop) (s : type686 A) : (@IN (A -> Prop) x s) = (@IN (A -> Prop) x s).
Proof. exact (eq_refl (@IN (A -> Prop) x s)). Qed.
Lemma lem4828215 {A : Type'} (x' : A -> Prop) (t : type686 A) (x : A -> Prop) (s : type686 A) : (term476 A x' t x s) = (term477 A x' t x s).
Proof. exact (MK_COMB (@lem4828213 A x' x t s) (@lem4828214 A x s)). Qed.
Lemma lem4828218 {A : Type'} (x' : A -> Prop) (t : type686 A) (x : A -> Prop) (s : type686 A) : (term477 A x' t x s) = (term476 A x' t x s).
Proof. exact (SYM (@lem4828215 A x' t x s)). Qed.
Lemma lem4828224 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4828225 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4828224 (A -> Prop) P x). Qed.
Lemma lem4828226 {A : Type'} (t : type686 A) (x' : A -> Prop) : (@IN (A -> Prop) x' t) = (t x').
Proof. exact (@lem4828225 A t x'). Qed.
Lemma lem4828227 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4828228 {A : Type'} (t : type686 A) (x' : A -> Prop) : (term252 A x' t) = (term253 A t x').
Proof. exact (MK_COMB (@lem4828227) (@lem4828226 A t x')). Qed.
Lemma lem4828229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4828230 {A : Type'} (t : type686 A) (x' : A -> Prop) : (term472 A x' t) = (term287 A t x').
Proof. exact (MK_COMB (@lem4828229) (@lem4828228 A t x')). Qed.
Lemma lem4828234 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4828235 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4828234 (A -> Prop) P x). Qed.
Lemma lem4828236 {A : Type'} (s : type686 A) (x' : A -> Prop) : (@IN (A -> Prop) x' s) = (s x').
Proof. exact (@lem4828235 A s x'). Qed.
Lemma lem4828237 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4828238 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term250 A x' s) = (term251 A s x').
Proof. exact (MK_COMB (@lem4828237) (@lem4828236 A s x')). Qed.
Lemma lem4828242 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4828243 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4828242 (A -> Prop) P x). Qed.
Lemma lem4828244 {A : Type'} (t : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x t) = (t x).
Proof. exact (@lem4828243 A t x). Qed.
Lemma lem4828245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4828246 {A : Type'} (t : type686 A) (x : A -> Prop) : (term250 A x t) = (term251 A t x).
Proof. exact (MK_COMB (@lem4828245) (@lem4828244 A t x)). Qed.
Lemma lem4828254 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4828255 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4828254 (A -> Prop) P x). Qed.
Lemma lem4828256 {A : Type'} (t : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x t) = (t x).
Proof. exact (@lem4828255 A t x). Qed.
Lemma lem4828257 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4828258 {A : Type'} (t : type686 A) (x : A -> Prop) : (term232 A x t) = (term233 A t x).
Proof. exact (MK_COMB (@lem4828257) (@lem4828256 A t x)). Qed.
Lemma lem4828260 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4828261 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4828260 (A -> Prop) P x). Qed.
Lemma lem4828262 {A : Type'} (s : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x s) = (s x).
Proof. exact (@lem4828261 A s x). Qed.
Lemma lem4828263 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term234 A t x s) = (term235 A t s x).
Proof. exact (MK_COMB (@lem4828258 A t x) (@lem4828262 A s x)). Qed.
Lemma lem4828266 {A : Type'} (t : type686 A) (s : type686 A) : (term236 A t s) = (term237 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4828263 A t s x)). Qed.
Lemma lem4828267 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828268 {A : Type'} (t : type686 A) (s : type686 A) : (term221 A t s) = (term238 A t s).
Proof. exact (MK_COMB (@lem4828267 A) (@lem4828266 A t s)). Qed.
Lemma lem4828273 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) : (term470 A x t s) = (term478 A x t s).
Proof. exact (MK_COMB (@lem4828246 A t x) (@lem4828268 A t s)). Qed.
Lemma lem4828276 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term471 A x' x t s) = (term479 A x' x t s).
Proof. exact (MK_COMB (@lem4828238 A s x') (@lem4828273 A x t s)). Qed.
Lemma lem4828279 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term473 A x' x t s) = (term480 A x' x t s).
Proof. exact (MK_COMB (@lem4828230 A t x') (@lem4828276 A x' x t s)). Qed.
Lemma lem4828282 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4828283 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term475 A x' x t s) = (term481 A x' x t s).
Proof. exact (MK_COMB (@lem4828282) (@lem4828279 A x' x t s)). Qed.
Lemma lem4828285 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4828286 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4828285 (A -> Prop) P x). Qed.
Lemma lem4828287 {A : Type'} (s : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x s) = (s x).
Proof. exact (@lem4828286 A s x). Qed.
Lemma lem4828288 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : (term477 A x' t x s) = (term482 A x' t s x).
Proof. exact (MK_COMB (@lem4828283 A x' x t s) (@lem4828287 A s x)). Qed.
Lemma lem4828291 {A : Type'} (x' : A -> Prop) (t : type686 A) (x : A -> Prop) (s : type686 A) : (term482 A x' t s x) = (term477 A x' t x s).
Proof. exact (SYM (@lem4828288 A x' t s x)). Qed.
Lemma lem4828293 (p : Prop) : p = (term98 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4828294 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : (term482 A x' t s x) = (term483 A x' t s x).
Proof. exact (@lem4828293 (term482 A x' t s x)). Qed.
Lemma lem4828295 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : (term483 A x' t s x) = (term482 A x' t s x).
Proof. exact (SYM (@lem4828294 A x' t s x)). Qed.
Lemma lem4828296 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term484 A x' t s x) : term484 A x' t s x.
Proof. exact (h1). Qed.
Lemma lem4828299 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term483 A x' t s x) : term483 A x' t s x.
Proof. exact (h1). Qed.
Lemma lem4828300 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : term485 A x' t s x.
Proof. exact (fun h0 : term483 A x' t s x => @lem4828299 A x' t s x h0). Qed.
Lemma lem4828301 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term485 A x' t s x) : term485 A x' t s x.
Proof. exact (h1). Qed.
Lemma lem4828302 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term483 A x' t s x) : term483 A x' t s x.
Proof. exact (h1). Qed.
Lemma lem4828303 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term483 A x' t s x) (h2 : term485 A x' t s x) : term483 A x' t s x.
Proof. exact (@lem4828301 A x' t s x h2 (@lem4828302 A x' t s x h1)). Qed.
Lemma lem4828304 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term483 A x' t s x) : term486 A x' t s x.
Proof. exact (fun h0 : term485 A x' t s x => @lem4828303 A x' t s x h1 h0). Qed.
Lemma lem4828305 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term485 A x' t s x) : term485 A x' t s x.
Proof. exact (h1). Qed.
Lemma lem4828306 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term483 A x' t s x) (h2 : term485 A x' t s x) : term483 A x' t s x.
Proof. exact (@lem4828304 A x' t s x h1 (@lem4828305 A x' t s x h2)). Qed.
Lemma lem4828307 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term485 A x' t s x) : term485 A x' t s x.
Proof. exact (fun h0 : term483 A x' t s x => @lem4828306 A x' t s x h0 h1). Qed.
Lemma lem4828308 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : term487 A x' t s x.
Proof. exact (fun h0 : term485 A x' t s x => @lem4828307 A x' t s x h0). Qed.
Lemma lem4828311 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : term485 A x' t s x.
Proof. exact (@lem4828308 A x' t s x (@lem4828300 A x' t s x)). Qed.
Lemma lem4828312 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : term485 A x' t s x.
Proof. exact (@lem4828311 A x' t s x). Qed.
Lemma lem4828330 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4828331 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : (term483 A x' t s x) = (term488 A x' t s x).
Proof. exact (@lem4828330 (term484 A x' t s x)). Qed.
Lemma lem4828333 (t : Prop) : (term105 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4828334 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : (term488 A x' t s x) = (term482 A x' t s x).
Proof. exact (@lem4828333 (term482 A x' t s x)). Qed.
Lemma lem4828337 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : (term483 A x' t s x) = (term482 A x' t s x).
Proof. exact (TRANS (@lem4828331 A x' t s x) (@lem4828334 A x' t s x)). Qed.
Lemma lem4828350 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term489 A t s x) = (term490 A t s x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4828337 A x' t s x)). Qed.
Lemma lem4828351 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828352 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term491 A t s x) = (term492 A t s x).
Proof. exact (MK_COMB (@lem4828351 A) (@lem4828350 A t s x)). Qed.
Lemma lem4828357 {A : Type'} (s : type686 A) (x : A -> Prop) : (term493 A s x) = (term494 A s x).
Proof. exact (fun_ext (fun t : type686 A => @lem4828352 A t s x)). Qed.
Lemma lem4828358 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4828359 {A : Type'} (s : type686 A) (x : A -> Prop) : (term495 A s x) = (term496 A s x).
Proof. exact (MK_COMB (@lem4828358 A) (@lem4828357 A s x)). Qed.
Lemma lem4828364 {A : Type'} (x : A -> Prop) : (term497 A x) = (term498 A x).
Proof. exact (fun_ext (fun s : type686 A => @lem4828359 A s x)). Qed.
Lemma lem4828365 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4828366 {A : Type'} (x : A -> Prop) : (term499 A x) = (term500 A x).
Proof. exact (MK_COMB (@lem4828365 A) (@lem4828364 A x)). Qed.
Lemma lem4828371 {A : Type'} : (term501 A) = (term502 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4828366 A x)). Qed.
Lemma lem4828372 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828381 {A : Type'} : (term503 A) = (term504 A).
Proof. exact (MK_COMB (@lem4828372 A) (@lem4828371 A)). Qed.
Lemma lem4828382 {A : Type'} (s : type686 A) (x : A -> Prop) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4828387 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term235 A t s x) = (term235 A t s x).
Proof. exact (eq_refl (term235 A t s x)). Qed.
Lemma lem4828388 {A : Type'} (t : type686 A) (s : type686 A) : (term237 A t s) = (term237 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4828387 A t s x)). Qed.
Lemma lem4828389 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828390 {A : Type'} (t : type686 A) (s : type686 A) : (term238 A t s) = (term238 A t s).
Proof. exact (MK_COMB (@lem4828389 A) (@lem4828388 A t s)). Qed.
Lemma lem4828393 {A : Type'} (t : type686 A) (x : A -> Prop) : (term251 A t x) = (term251 A t x).
Proof. exact (eq_refl (term251 A t x)). Qed.
Lemma lem4828394 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) : (term478 A x t s) = (term478 A x t s).
Proof. exact (MK_COMB (@lem4828393 A t x) (@lem4828390 A t s)). Qed.
Lemma lem4828397 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term251 A s x') = (term251 A s x').
Proof. exact (eq_refl (term251 A s x')). Qed.
Lemma lem4828398 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term479 A x' x t s) = (term479 A x' x t s).
Proof. exact (MK_COMB (@lem4828397 A s x') (@lem4828394 A x t s)). Qed.
Lemma lem4828403 {A : Type'} (t : type686 A) (x' : A -> Prop) : (term287 A t x') = (term287 A t x').
Proof. exact (eq_refl (term287 A t x')). Qed.
Lemma lem4828404 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term480 A x' x t s) = (term480 A x' x t s).
Proof. exact (MK_COMB (@lem4828403 A t x') (@lem4828398 A x' x t s)). Qed.
Lemma lem4828405 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4828406 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term481 A x' x t s) = (term481 A x' x t s).
Proof. exact (MK_COMB (@lem4828405) (@lem4828404 A x' x t s)). Qed.
Lemma lem4828407 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : (term482 A x' t s x) = (term482 A x' t s x).
Proof. exact (MK_COMB (@lem4828406 A x' x t s) (@lem4828382 A s x)). Qed.
Lemma lem4828408 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term490 A t s x) = (term490 A t s x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4828407 A x' t s x)). Qed.
Lemma lem4828409 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828410 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term492 A t s x) = (term492 A t s x).
Proof. exact (MK_COMB (@lem4828409 A) (@lem4828408 A t s x)). Qed.
Lemma lem4828411 {A : Type'} (s : type686 A) (x : A -> Prop) : (term494 A s x) = (term494 A s x).
Proof. exact (fun_ext (fun t : type686 A => @lem4828410 A t s x)). Qed.
Lemma lem4828412 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4828413 {A : Type'} (s : type686 A) (x : A -> Prop) : (term496 A s x) = (term496 A s x).
Proof. exact (MK_COMB (@lem4828412 A) (@lem4828411 A s x)). Qed.
Lemma lem4828414 {A : Type'} (x : A -> Prop) : (term498 A x) = (term498 A x).
Proof. exact (fun_ext (fun s : type686 A => @lem4828413 A s x)). Qed.
Lemma lem4828415 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4828416 {A : Type'} (x : A -> Prop) : (term500 A x) = (term500 A x).
Proof. exact (MK_COMB (@lem4828415 A) (@lem4828414 A x)). Qed.
Lemma lem4828417 {A : Type'} : (term502 A) = (term502 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4828416 A x)). Qed.
Lemma lem4828418 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828419 {A : Type'} : (term504 A) = (term504 A).
Proof. exact (MK_COMB (@lem4828418 A) (@lem4828417 A)). Qed.
Lemma lem4828462 {A : Type'} : (term503 A) = (term504 A).
Proof. exact (TRANS (@lem4828381 A) (@lem4828419 A)). Qed.
Lemma lem4828463 {A : Type'} : (term504 A) = (term503 A).
Proof. exact (SYM (@lem4828462 A)). Qed.
Lemma lem4828464 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term480 A x' x t s.
Proof. exact (h1). Qed.
Lemma lem4828466 (p : Prop) : p = (term98 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4828467 {A : Type'} (s : type686 A) (x : A -> Prop) : (s x) = (term505 A s x).
Proof. exact (@lem4828466 (s x)). Qed.
Lemma lem4828468 {A : Type'} (s : type686 A) (x : A -> Prop) : (term505 A s x) = (s x).
Proof. exact (SYM (@lem4828467 A s x)). Qed.
Lemma lem4828469 {A : Type'} (s : type686 A) (x : A -> Prop) (h1 : term253 A s x) : term253 A s x.
Proof. exact (h1). Qed.
Lemma lem4828479 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term235 A t s x) = (term278 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem4828480 {A : Type'} (t : type686 A) (s : type686 A) : (term237 A t s) = (term279 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4828479 A t s x)). Qed.
Lemma lem4828481 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828482 {A : Type'} (t : type686 A) (s : type686 A) : (term238 A t s) = (term280 A t s).
Proof. exact (MK_COMB (@lem4828481 A) (@lem4828480 A t s)). Qed.
Lemma lem4828484 {A : Type'} (t : type686 A) (x : A -> Prop) : (term251 A t x) = (term251 A t x).
Proof. exact (eq_refl (term251 A t x)). Qed.
Lemma lem4828485 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) : (term478 A x t s) = (term506 A x t s).
Proof. exact (MK_COMB (@lem4828484 A t x) (@lem4828482 A t s)). Qed.
Lemma lem4828487 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term251 A s x') = (term251 A s x').
Proof. exact (eq_refl (term251 A s x')). Qed.
Lemma lem4828488 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term479 A x' x t s) = (term507 A x' x t s).
Proof. exact (MK_COMB (@lem4828487 A s x') (@lem4828485 A x t s)). Qed.
Lemma lem4828490 {A : Type'} (t : type686 A) (x' : A -> Prop) : (term287 A t x') = (term287 A t x').
Proof. exact (eq_refl (term287 A t x')). Qed.
Lemma lem4828527 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term480 A x' x t s) = (term508 A x' x t s).
Proof. exact (MK_COMB (@lem4828490 A t x') (@lem4828488 A x' x t s)). Qed.
Lemma lem4828528 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term508 A x' x t s.
Proof. exact (EQ_MP (@lem4828527 A x' x t s) (@lem4828464 A x' x t s h1)). Qed.
Lemma lem4828534 {A : Type'} (s : type686 A) (x : A -> Prop) (h1 : term253 A s x) : term253 A s x.
Proof. exact (h1). Qed.
Lemma lem4828545 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term278 A t s x) = (term278 A t s x).
Proof. exact (eq_refl (term278 A t s x)). Qed.
Lemma lem4828546 {A : Type'} (t : type686 A) (s : type686 A) : (term279 A t s) = (term279 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4828545 A t s x)). Qed.
Lemma lem4828547 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828548 {A : Type'} (t : type686 A) (s : type686 A) : (term280 A t s) = (term280 A t s).
Proof. exact (MK_COMB (@lem4828547 A) (@lem4828546 A t s)). Qed.
Lemma lem4828553 {A : Type'} (t : type686 A) (x : A -> Prop) : (term251 A t x) = (term251 A t x).
Proof. exact (eq_refl (term251 A t x)). Qed.
Lemma lem4828554 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) : (term506 A x t s) = (term506 A x t s).
Proof. exact (MK_COMB (@lem4828553 A t x) (@lem4828548 A t s)). Qed.
Lemma lem4828559 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term251 A s x') = (term251 A s x').
Proof. exact (eq_refl (term251 A s x')). Qed.
Lemma lem4828560 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term507 A x' x t s) = (term507 A x' x t s).
Proof. exact (MK_COMB (@lem4828559 A s x') (@lem4828554 A x t s)). Qed.
Lemma lem4828567 {A : Type'} (t : type686 A) (x' : A -> Prop) : (term287 A t x') = (term287 A t x').
Proof. exact (eq_refl (term287 A t x')). Qed.
Lemma lem4828568 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term508 A x' x t s) = (term508 A x' x t s).
Proof. exact (MK_COMB (@lem4828567 A t x') (@lem4828560 A x' x t s)). Qed.
Lemma lem4828569 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term508 A x' x t s.
Proof. exact (EQ_MP (@lem4828568 A x' x t s) (@lem4828528 A x' x t s h1)). Qed.
Lemma lem4828575 {A : Type'} (s : type686 A) (x : A -> Prop) (h1 : term253 A s x) : term253 A s x.
Proof. exact (h1). Qed.
Lemma lem4828576 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term507 A x' x t s.
Proof. exact (proj2 (@lem4828569 A x' x t s h1)). Qed.
Lemma lem4828578 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term506 A x t s.
Proof. exact (proj2 (@lem4828576 A x' x t s h1)). Qed.
Lemma lem4828580 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term280 A t s.
Proof. exact (proj2 (@lem4828578 A x' x t s h1)). Qed.
Lemma lem4828585 {A : Type'} (s : type686 A) (x : A -> Prop) (h1 : term253 A s x) : term253 A s x.
Proof. exact (h1). Qed.
Lemma lem4828605 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term278 A t s x) = (term278 A t s x).
Proof. exact (eq_refl (term278 A t s x)). Qed.
Lemma lem4828606 {A : Type'} (t : type686 A) (s : type686 A) : (term279 A t s) = (term279 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4828605 A t s x)). Qed.
Lemma lem4828607 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828609 {A : Type'} (t : type686 A) (s : type686 A) : (term280 A t s) = (term280 A t s).
Proof. exact (MK_COMB (@lem4828607 A) (@lem4828606 A t s)). Qed.
Lemma lem4828610 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term280 A t s.
Proof. exact (EQ_MP (@lem4828609 A t s) (@lem4828580 A x' x t s h1)). Qed.
Lemma lem4828611 {A : Type'} (_59828 : A -> Prop) (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term509 A t s _59828.
Proof. exact (@lem4828610 A x' x t s h1 _59828). Qed.
Lemma lem4828612 {A : Type'} (t : type686 A) (s : type686 A) (_59828 : A -> Prop) : (term509 A t s _59828) = (term278 A t s _59828).
Proof. exact (eq_refl (term509 A t s _59828)). Qed.
Lemma lem4828615 {A : Type'} (s : type686 A) (x : A -> Prop) (h1 : term253 A s x) : term253 A s x.
Proof. exact (h1). Qed.
Lemma lem4828627 {A : Type'} (_59828 : A -> Prop) (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term278 A t s _59828.
Proof. exact (EQ_MP (@lem4828612 A t s _59828) (@lem4828611 A _59828 x' x t s h1)). Qed.
Lemma lem4828629 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : t x.
Proof. exact (proj1 (@lem4828578 A x' x t s h1)). Qed.
Lemma lem4828630 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term319 A t x.
Proof. exact (fun h0 : term253 A t x => @lem4828629 A x' x t s h1). Qed.
Lemma lem4828632 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4828633 {A : Type'} (t : type686 A) (x : A -> Prop) : (term319 A t x) = (t x).
Proof. exact (@lem4828632 (t x)). Qed.
Lemma lem4828634 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : t x.
Proof. exact (EQ_MP (@lem4828633 A t x) (@lem4828630 A x' x t s h1)). Qed.
Lemma lem4828640 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4828641 {A : Type'} (s : type686 A) (t : type686 A) (_59828 : A -> Prop) : (term278 A t s _59828) = (term510 A s t _59828).
Proof. exact (@lem4828640 (s _59828) (term253 A t _59828)). Qed.
Lemma lem4828647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4828648 {A : Type'} (s : type686 A) (t : type686 A) (_59828 : A -> Prop) : (term511 A t s _59828) = (term512 A s t _59828).
Proof. exact (MK_COMB (@lem4828647) (@lem4828641 A s t _59828)). Qed.
Lemma lem4828654 {A : Type'} (s : type686 A) (t : type686 A) (_59828 : A -> Prop) : (term510 A s t _59828) = (term510 A s t _59828).
Proof. exact (eq_refl (term510 A s t _59828)). Qed.
Lemma lem4828655 {A : Type'} (s : type686 A) (t : type686 A) (_59828 : A -> Prop) : ((term278 A t s _59828) = (term510 A s t _59828)) = ((term510 A s t _59828) = (term510 A s t _59828)).
Proof. exact (MK_COMB (@lem4828648 A s t _59828) (@lem4828654 A s t _59828)). Qed.
Lemma lem4828657 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4828658 (x : Prop) : (x = x) = True.
Proof. exact (@lem4828657 Prop x). Qed.
Lemma lem4828659 {A : Type'} (s : type686 A) (t : type686 A) (_59828 : A -> Prop) : ((term510 A s t _59828) = (term510 A s t _59828)) = True.
Proof. exact (@lem4828658 (term510 A s t _59828)). Qed.
Lemma lem4828660 {A : Type'} (s : type686 A) (t : type686 A) (_59828 : A -> Prop) : ((term278 A t s _59828) = (term510 A s t _59828)) = True.
Proof. exact (TRANS (@lem4828655 A s t _59828) (@lem4828659 A s t _59828)). Qed.
Lemma lem4828661 {A : Type'} (s : type686 A) (t : type686 A) (_59828 : A -> Prop) : True = ((term278 A t s _59828) = (term510 A s t _59828)).
Proof. exact (SYM (@lem4828660 A s t _59828)). Qed.
Lemma lem4828662 {A : Type'} (s : type686 A) (t : type686 A) (_59828 : A -> Prop) : (term278 A t s _59828) = (term510 A s t _59828).
Proof. exact (EQ_MP (@lem4828661 A s t _59828) (@lem0)). Qed.
Lemma lem4828663 {A : Type'} (_59828 : A -> Prop) (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term510 A s t _59828.
Proof. exact (EQ_MP (@lem4828662 A s t _59828) (@lem4828627 A _59828 x' x t s h1)). Qed.
Lemma lem4828665 (b : Prop) (a : Prop) : (a \/ b) = (term184 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4828666 {A : Type'} (t : type686 A) (s : type686 A) (_59828 : A -> Prop) : (term510 A s t _59828) = (term513 A t s _59828).
Proof. exact (@lem4828665 (term253 A t _59828) (s _59828)). Qed.
Lemma lem4828668 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4828669 {A : Type'} (t : type686 A) (_59828 : A -> Prop) : (term283 A t _59828) = (t _59828).
Proof. exact (@lem4828668 (t _59828)). Qed.
Lemma lem4828670 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4828671 {A : Type'} (t : type686 A) (_59828 : A -> Prop) : (term324 A t _59828) = (term233 A t _59828).
Proof. exact (MK_COMB (@lem4828670) (@lem4828669 A t _59828)). Qed.
Lemma lem4828672 {A : Type'} (s : type686 A) (_59828 : A -> Prop) : (s _59828) = (s _59828).
Proof. exact (eq_refl (s _59828)). Qed.
Lemma lem4828673 {A : Type'} (t : type686 A) (s : type686 A) (_59828 : A -> Prop) : (term513 A t s _59828) = (term235 A t s _59828).
Proof. exact (MK_COMB (@lem4828671 A t _59828) (@lem4828672 A s _59828)). Qed.
Lemma lem4828674 {A : Type'} (t : type686 A) (s : type686 A) (_59828 : A -> Prop) : (term510 A s t _59828) = (term235 A t s _59828).
Proof. exact (TRANS (@lem4828666 A t s _59828) (@lem4828673 A t s _59828)). Qed.
Lemma lem4828677 {A : Type'} (_59828 : A -> Prop) (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term235 A t s _59828.
Proof. exact (EQ_MP (@lem4828674 A t s _59828) (@lem4828663 A _59828 x' x t s h1)). Qed.
Lemma lem4828678 {A : Type'} (_59828 : A -> Prop) (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term235 A t s _59828.
Proof. exact (@lem4828677 A _59828 x' x t s h1). Qed.
Lemma lem4828679 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term235 A t s x.
Proof. exact (@lem4828678 A x x' x t s h1). Qed.
Lemma lem4828682 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : s x.
Proof. exact (@lem4828679 A x' x t s h1 (@lem4828634 A x' x t s h1)). Qed.
Lemma lem4828683 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term319 A s x.
Proof. exact (fun h0 : term253 A s x => @lem4828682 A x' x t s h1). Qed.
Lemma lem4828685 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4828686 {A : Type'} (s : type686 A) (x : A -> Prop) : (term319 A s x) = (s x).
Proof. exact (@lem4828685 (s x)). Qed.
Lemma lem4828687 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : s x.
Proof. exact (EQ_MP (@lem4828686 A s x) (@lem4828683 A x' x t s h1)). Qed.
Lemma lem4828690 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4828692 {A : Type'} (s : type686 A) (x : A -> Prop) : (term253 A s x) = (term328 A s x).
Proof. exact (@lem4828690 (s x)). Qed.
Lemma lem4828695 {A : Type'} (s : type686 A) (x : A -> Prop) (h1 : term253 A s x) : term328 A s x.
Proof. exact (EQ_MP (@lem4828692 A s x) (@lem4828615 A s x h1)). Qed.
Lemma lem4828698 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x) (h2 : term480 A x' x t s) : False.
Proof. exact (@lem4828695 A s x h1 (@lem4828687 A x' x t s h2)). Qed.
Lemma lem4828699 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x) (h2 : term480 A x' x t s) : term197.
Proof. exact (fun h0 : ~ False => @lem4828698 A x' x t s h1 h2). Qed.
Lemma lem4828701 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4828702 : term197 = False.
Proof. exact (@lem4828701 False). Qed.
Lemma lem4828703 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x) (h2 : term480 A x' x t s) : False.
Proof. exact (EQ_MP (@lem4828702) (@lem4828699 A x' x t s h1 h2)). Qed.
Lemma lem4828704 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x) (h2 : term480 A x' x t s) : (term253 A s x) = False.
Proof. exact (prop_ext (fun h3 : term253 A s x => @lem4828703 A x' x t s h1 h2) (fun h3 : False => @lem4828615 A s x h1)). Qed.
Lemma lem4828705 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x) (h2 : term480 A x' x t s) : False.
Proof. exact (EQ_MP (@lem4828704 A x' x t s h1 h2) (@lem4828615 A s x h1)). Qed.
Lemma lem4828706 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x) (h2 : term480 A x' x t s) : (term253 A s x) = False.
Proof. exact (prop_ext (fun h3 : term253 A s x => @lem4828705 A x' x t s h1 h2) (fun h3 : False => @lem4828585 A s x h1)). Qed.
Lemma lem4828707 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x) (h2 : term480 A x' x t s) : False.
Proof. exact (EQ_MP (@lem4828706 A x' x t s h1 h2) (@lem4828585 A s x h1)). Qed.
Lemma lem4828708 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x) (h2 : term480 A x' x t s) : (term253 A s x) = False.
Proof. exact (prop_ext (fun h3 : term253 A s x => @lem4828707 A x' x t s h1 h2) (fun h3 : False => @lem4828585 A s x h1)). Qed.
Lemma lem4828709 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x) (h2 : term480 A x' x t s) : False.
Proof. exact (EQ_MP (@lem4828708 A x' x t s h1 h2) (@lem4828585 A s x h1)). Qed.
Lemma lem4828710 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x) (h2 : term480 A x' x t s) : (term253 A s x) = False.
Proof. exact (prop_ext (fun h3 : term253 A s x => @lem4828709 A x' x t s h1 h2) (fun h3 : False => @lem4828575 A s x h1)). Qed.
Lemma lem4828711 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x) (h2 : term480 A x' x t s) : False.
Proof. exact (EQ_MP (@lem4828710 A x' x t s h1 h2) (@lem4828575 A s x h1)). Qed.
Lemma lem4828712 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x) (h2 : term480 A x' x t s) : (term253 A s x) = False.
Proof. exact (prop_ext (fun h3 : term253 A s x => @lem4828711 A x' x t s h1 h2) (fun h3 : False => @lem4828534 A s x h1)). Qed.
Lemma lem4828713 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x) (h2 : term480 A x' x t s) : False.
Proof. exact (EQ_MP (@lem4828712 A x' x t s h1 h2) (@lem4828534 A s x h1)). Qed.
Lemma lem4828714 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x) (h2 : term480 A x' x t s) : (term253 A s x) = False.
Proof. exact (prop_ext (fun h3 : term253 A s x => @lem4828713 A x' x t s h1 h2) (fun h3 : False => @lem4828469 A s x h1)). Qed.
Lemma lem4828715 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x) (h2 : term480 A x' x t s) : False.
Proof. exact (EQ_MP (@lem4828714 A x' x t s h1 h2) (@lem4828469 A s x h1)). Qed.
Lemma lem4828716 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term505 A s x.
Proof. exact (fun h0 : term253 A s x => @lem4828715 A x' x t s h0 h1). Qed.
Lemma lem4828717 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : s x.
Proof. exact (EQ_MP (@lem4828468 A s x) (@lem4828716 A x' x t s h1)). Qed.
Lemma lem4828718 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : term482 A x' t s x.
Proof. exact (fun h0 : term480 A x' x t s => @lem4828717 A x' x t s h0). Qed.
Lemma lem4828723 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : term492 A t s x.
Proof. exact (fun x' : A -> Prop => @lem4828718 A x' t s x). Qed.
Lemma lem4828728 {A : Type'} (s : type686 A) (x : A -> Prop) : term496 A s x.
Proof. exact (fun t : type686 A => @lem4828723 A t s x). Qed.
Lemma lem4828733 {A : Type'} (x : A -> Prop) : term500 A x.
Proof. exact (fun s : type686 A => @lem4828728 A s x). Qed.
Lemma lem4828738 {A : Type'} : term504 A.
Proof. exact (fun x : A -> Prop => @lem4828733 A x). Qed.
Lemma lem4828739 {A : Type'} : term503 A.
Proof. exact (EQ_MP (@lem4828463 A) (@lem4828738 A)). Qed.
Lemma lem4828740 {A : Type'} (x : A -> Prop) : term514 A x.
Proof. exact (@lem4828739 A x). Qed.
Lemma lem4828741 {A : Type'} (x : A -> Prop) : (term514 A x) = (term499 A x).
Proof. exact (eq_refl (term514 A x)). Qed.
Lemma lem4828742 {A : Type'} (x : A -> Prop) : term499 A x.
Proof. exact (EQ_MP (@lem4828741 A x) (@lem4828740 A x)). Qed.
Lemma lem4828743 {A : Type'} (x : A -> Prop) (s : type686 A) : term515 A x s.
Proof. exact (@lem4828742 A x s). Qed.
Lemma lem4828744 {A : Type'} (s : type686 A) (x : A -> Prop) : (term515 A x s) = (term495 A s x).
Proof. exact (eq_refl (term515 A x s)). Qed.
Lemma lem4828745 {A : Type'} (s : type686 A) (x : A -> Prop) : term495 A s x.
Proof. exact (EQ_MP (@lem4828744 A s x) (@lem4828743 A x s)). Qed.
Lemma lem4828746 {A : Type'} (s : type686 A) (x : A -> Prop) (t : type686 A) : term516 A s x t.
Proof. exact (@lem4828745 A s x t). Qed.
Lemma lem4828747 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term516 A s x t) = (term491 A t s x).
Proof. exact (eq_refl (term516 A s x t)). Qed.
Lemma lem4828748 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : term491 A t s x.
Proof. exact (EQ_MP (@lem4828747 A t s x) (@lem4828746 A s x t)). Qed.
Lemma lem4828749 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) (x' : A -> Prop) : term517 A t s x x'.
Proof. exact (@lem4828748 A t s x x'). Qed.
Lemma lem4828750 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : (term517 A t s x x') = (term483 A x' t s x).
Proof. exact (eq_refl (term517 A t s x x')). Qed.
Lemma lem4828751 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : term483 A x' t s x.
Proof. exact (EQ_MP (@lem4828750 A x' t s x) (@lem4828749 A t s x x')). Qed.
Lemma lem4828753 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : term483 A x' t s x.
Proof. exact (@lem4828312 A x' t s x (@lem4828751 A x' t s x)). Qed.
Lemma lem4828754 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term484 A x' t s x) : False.
Proof. exact (@lem4828753 A x' t s x (@lem4828296 A x' t s x h1)). Qed.
Lemma lem4828755 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term484 A x' t s x) : (term484 A x' t s x) = False.
Proof. exact (prop_ext (fun h2 : term484 A x' t s x => @lem4828754 A x' t s x h1) (fun h2 : False => @lem4828296 A x' t s x h1)). Qed.
Lemma lem4828756 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) (h1 : term484 A x' t s x) : False.
Proof. exact (EQ_MP (@lem4828755 A x' t s x h1) (@lem4828296 A x' t s x h1)). Qed.
Lemma lem4828757 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : term483 A x' t s x.
Proof. exact (fun h0 : term484 A x' t s x => @lem4828756 A x' t s x h0). Qed.
Lemma lem4828758 {A : Type'} (x' : A -> Prop) (t : type686 A) (s : type686 A) (x : A -> Prop) : term482 A x' t s x.
Proof. exact (EQ_MP (@lem4828295 A x' t s x) (@lem4828757 A x' t s x)). Qed.
Lemma lem4828759 {A : Type'} (x' : A -> Prop) (t : type686 A) (x : A -> Prop) (s : type686 A) : term477 A x' t x s.
Proof. exact (EQ_MP (@lem4828291 A x' t x s) (@lem4828758 A x' t s x)). Qed.
Lemma lem4828760 {A : Type'} (x' : A -> Prop) (t : type686 A) (x : A -> Prop) (s : type686 A) : term476 A x' t x s.
Proof. exact (EQ_MP (@lem4828218 A x' t x s) (@lem4828759 A x' t x s)). Qed.
Lemma lem4828761 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term252 A x' t) (h2 : @IN (A -> Prop) x t) (h3 : @IN (A -> Prop) x' s) (h4 : @SUBSET (A -> Prop) t s) : @IN (A -> Prop) x s.
Proof. exact (@lem4828760 A x' t x s (@lem4828181 A x x' t s h1 h2 h3 h4)). Qed.
Lemma lem4828772 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : @IN (A -> Prop) x t) (h2 : @SUBSET (A -> Prop) t s) : term467 A x t s.
Proof. exact (conj (@lem4828138 A x t h1) (@lem4826912 A t s h2)). Qed.
Lemma lem4828773 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : @IN (A -> Prop) x t) (h2 : @IN (A -> Prop) x' s) (h3 : @SUBSET (A -> Prop) t s) : term468 A x' x t s.
Proof. exact (conj (@lem4828141 A x' s h2) (@lem4828772 A x t s h1 h3)). Qed.
Lemma lem4828774 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term252 A x' t) (h2 : @IN (A -> Prop) x t) (h3 : @IN (A -> Prop) x' s) (h4 : @SUBSET (A -> Prop) t s) : term469 A x' x t s.
Proof. exact (conj (@lem4828140 A x' t h1) (@lem4828773 A x x' t s h2 h3 h4)). Qed.
Lemma lem4828784 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term220 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4828785 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term221 A s t).
Proof. exact (@lem4828784 (A -> Prop) s t). Qed.
Lemma lem4828786 {A : Type'} (t : type686 A) (s : type686 A) : (@SUBSET (A -> Prop) t s) = (term221 A t s).
Proof. exact (@lem4828785 A t s). Qed.
Lemma lem4828793 {A : Type'} (x : A -> Prop) (t : type686 A) : (term250 A x t) = (term250 A x t).
Proof. exact (eq_refl (term250 A x t)). Qed.
Lemma lem4828794 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) : (term467 A x t s) = (term470 A x t s).
Proof. exact (MK_COMB (@lem4828793 A x t) (@lem4828786 A t s)). Qed.
Lemma lem4828797 {A : Type'} (x' : A -> Prop) (s : type686 A) : (term250 A x' s) = (term250 A x' s).
Proof. exact (eq_refl (term250 A x' s)). Qed.
Lemma lem4828798 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term468 A x' x t s) = (term471 A x' x t s).
Proof. exact (MK_COMB (@lem4828797 A x' s) (@lem4828794 A x t s)). Qed.
Lemma lem4828801 {A : Type'} (x' : A -> Prop) (t : type686 A) : (term472 A x' t) = (term472 A x' t).
Proof. exact (eq_refl (term472 A x' t)). Qed.
Lemma lem4828802 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term469 A x' x t s) = (term473 A x' x t s).
Proof. exact (MK_COMB (@lem4828801 A x' t) (@lem4828798 A x' x t s)). Qed.
Lemma lem4828805 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4828806 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term474 A x' x t s) = (term475 A x' x t s).
Proof. exact (MK_COMB (@lem4828805) (@lem4828802 A x' x t s)). Qed.
Lemma lem4828807 {A : Type'} (x' : A -> Prop) (s : type686 A) : (@IN (A -> Prop) x' s) = (@IN (A -> Prop) x' s).
Proof. exact (eq_refl (@IN (A -> Prop) x' s)). Qed.
Lemma lem4828808 {A : Type'} (x : A -> Prop) (t : type686 A) (x' : A -> Prop) (s : type686 A) : (term518 A x t x' s) = (term519 A x t x' s).
Proof. exact (MK_COMB (@lem4828806 A x' x t s) (@lem4828807 A x' s)). Qed.
Lemma lem4828811 {A : Type'} (x : A -> Prop) (t : type686 A) (x' : A -> Prop) (s : type686 A) : (term519 A x t x' s) = (term518 A x t x' s).
Proof. exact (SYM (@lem4828808 A x t x' s)). Qed.
Lemma lem4828817 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4828818 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4828817 (A -> Prop) P x). Qed.
Lemma lem4828819 {A : Type'} (t : type686 A) (x' : A -> Prop) : (@IN (A -> Prop) x' t) = (t x').
Proof. exact (@lem4828818 A t x'). Qed.
Lemma lem4828820 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4828821 {A : Type'} (t : type686 A) (x' : A -> Prop) : (term252 A x' t) = (term253 A t x').
Proof. exact (MK_COMB (@lem4828820) (@lem4828819 A t x')). Qed.
Lemma lem4828822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4828823 {A : Type'} (t : type686 A) (x' : A -> Prop) : (term472 A x' t) = (term287 A t x').
Proof. exact (MK_COMB (@lem4828822) (@lem4828821 A t x')). Qed.
Lemma lem4828827 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4828828 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4828827 (A -> Prop) P x). Qed.
Lemma lem4828829 {A : Type'} (s : type686 A) (x' : A -> Prop) : (@IN (A -> Prop) x' s) = (s x').
Proof. exact (@lem4828828 A s x'). Qed.
Lemma lem4828830 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4828831 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term250 A x' s) = (term251 A s x').
Proof. exact (MK_COMB (@lem4828830) (@lem4828829 A s x')). Qed.
Lemma lem4828835 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4828836 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4828835 (A -> Prop) P x). Qed.
Lemma lem4828837 {A : Type'} (t : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x t) = (t x).
Proof. exact (@lem4828836 A t x). Qed.
Lemma lem4828838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4828839 {A : Type'} (t : type686 A) (x : A -> Prop) : (term250 A x t) = (term251 A t x).
Proof. exact (MK_COMB (@lem4828838) (@lem4828837 A t x)). Qed.
Lemma lem4828847 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4828848 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4828847 (A -> Prop) P x). Qed.
Lemma lem4828849 {A : Type'} (t : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x t) = (t x).
Proof. exact (@lem4828848 A t x). Qed.
Lemma lem4828850 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4828851 {A : Type'} (t : type686 A) (x : A -> Prop) : (term232 A x t) = (term233 A t x).
Proof. exact (MK_COMB (@lem4828850) (@lem4828849 A t x)). Qed.
Lemma lem4828853 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4828854 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4828853 (A -> Prop) P x). Qed.
Lemma lem4828855 {A : Type'} (s : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x s) = (s x).
Proof. exact (@lem4828854 A s x). Qed.
Lemma lem4828856 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term234 A t x s) = (term235 A t s x).
Proof. exact (MK_COMB (@lem4828851 A t x) (@lem4828855 A s x)). Qed.
Lemma lem4828859 {A : Type'} (t : type686 A) (s : type686 A) : (term236 A t s) = (term237 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4828856 A t s x)). Qed.
Lemma lem4828860 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828861 {A : Type'} (t : type686 A) (s : type686 A) : (term221 A t s) = (term238 A t s).
Proof. exact (MK_COMB (@lem4828860 A) (@lem4828859 A t s)). Qed.
Lemma lem4828866 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) : (term470 A x t s) = (term478 A x t s).
Proof. exact (MK_COMB (@lem4828839 A t x) (@lem4828861 A t s)). Qed.
Lemma lem4828869 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term471 A x' x t s) = (term479 A x' x t s).
Proof. exact (MK_COMB (@lem4828831 A s x') (@lem4828866 A x t s)). Qed.
Lemma lem4828872 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term473 A x' x t s) = (term480 A x' x t s).
Proof. exact (MK_COMB (@lem4828823 A t x') (@lem4828869 A x' x t s)). Qed.
Lemma lem4828875 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4828876 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term475 A x' x t s) = (term481 A x' x t s).
Proof. exact (MK_COMB (@lem4828875) (@lem4828872 A x' x t s)). Qed.
Lemma lem4828878 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4828879 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4828878 (A -> Prop) P x). Qed.
Lemma lem4828880 {A : Type'} (s : type686 A) (x' : A -> Prop) : (@IN (A -> Prop) x' s) = (s x').
Proof. exact (@lem4828879 A s x'). Qed.
Lemma lem4828881 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : (term519 A x t x' s) = (term520 A x t s x').
Proof. exact (MK_COMB (@lem4828876 A x' x t s) (@lem4828880 A s x')). Qed.
Lemma lem4828884 {A : Type'} (x : A -> Prop) (t : type686 A) (x' : A -> Prop) (s : type686 A) : (term520 A x t s x') = (term519 A x t x' s).
Proof. exact (SYM (@lem4828881 A x t s x')). Qed.
Lemma lem4828886 (p : Prop) : p = (term98 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4828887 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : (term520 A x t s x') = (term521 A x t s x').
Proof. exact (@lem4828886 (term520 A x t s x')). Qed.
Lemma lem4828888 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : (term521 A x t s x') = (term520 A x t s x').
Proof. exact (SYM (@lem4828887 A x t s x')). Qed.
Lemma lem4828889 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) (h1 : term522 A x t s x') : term522 A x t s x'.
Proof. exact (h1). Qed.
Lemma lem4828892 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) (h1 : term521 A x t s x') : term521 A x t s x'.
Proof. exact (h1). Qed.
Lemma lem4828893 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : term523 A x t s x'.
Proof. exact (fun h0 : term521 A x t s x' => @lem4828892 A x t s x' h0). Qed.
Lemma lem4828894 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) (h1 : term523 A x t s x') : term523 A x t s x'.
Proof. exact (h1). Qed.
Lemma lem4828895 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) (h1 : term521 A x t s x') : term521 A x t s x'.
Proof. exact (h1). Qed.
Lemma lem4828896 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) (h1 : term521 A x t s x') (h2 : term523 A x t s x') : term521 A x t s x'.
Proof. exact (@lem4828894 A x t s x' h2 (@lem4828895 A x t s x' h1)). Qed.
Lemma lem4828897 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) (h1 : term521 A x t s x') : term524 A x t s x'.
Proof. exact (fun h0 : term523 A x t s x' => @lem4828896 A x t s x' h1 h0). Qed.
Lemma lem4828898 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) (h1 : term523 A x t s x') : term523 A x t s x'.
Proof. exact (h1). Qed.
Lemma lem4828899 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) (h1 : term521 A x t s x') (h2 : term523 A x t s x') : term521 A x t s x'.
Proof. exact (@lem4828897 A x t s x' h1 (@lem4828898 A x t s x' h2)). Qed.
Lemma lem4828900 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) (h1 : term523 A x t s x') : term523 A x t s x'.
Proof. exact (fun h0 : term521 A x t s x' => @lem4828899 A x t s x' h0 h1). Qed.
Lemma lem4828901 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : term525 A x t s x'.
Proof. exact (fun h0 : term523 A x t s x' => @lem4828900 A x t s x' h0). Qed.
Lemma lem4828904 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : term523 A x t s x'.
Proof. exact (@lem4828901 A x t s x' (@lem4828893 A x t s x')). Qed.
Lemma lem4828905 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : term523 A x t s x'.
Proof. exact (@lem4828904 A x t s x'). Qed.
Lemma lem4828923 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4828924 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : (term521 A x t s x') = (term526 A x t s x').
Proof. exact (@lem4828923 (term522 A x t s x')). Qed.
Lemma lem4828926 (t : Prop) : (term105 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4828927 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : (term526 A x t s x') = (term520 A x t s x').
Proof. exact (@lem4828926 (term520 A x t s x')). Qed.
Lemma lem4828930 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : (term521 A x t s x') = (term520 A x t s x').
Proof. exact (TRANS (@lem4828924 A x t s x') (@lem4828927 A x t s x')). Qed.
Lemma lem4828943 {A : Type'} (t : type686 A) (s : type686 A) (x' : A -> Prop) : (term527 A t s x') = (term528 A t s x').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4828930 A x t s x')). Qed.
Lemma lem4828944 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828945 {A : Type'} (t : type686 A) (s : type686 A) (x' : A -> Prop) : (term529 A t s x') = (term530 A t s x').
Proof. exact (MK_COMB (@lem4828944 A) (@lem4828943 A t s x')). Qed.
Lemma lem4828950 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term531 A s x') = (term532 A s x').
Proof. exact (fun_ext (fun t : type686 A => @lem4828945 A t s x')). Qed.
Lemma lem4828951 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4828952 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term533 A s x') = (term534 A s x').
Proof. exact (MK_COMB (@lem4828951 A) (@lem4828950 A s x')). Qed.
Lemma lem4828957 {A : Type'} (x' : A -> Prop) : (term535 A x') = (term536 A x').
Proof. exact (fun_ext (fun s : type686 A => @lem4828952 A s x')). Qed.
Lemma lem4828958 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4828959 {A : Type'} (x' : A -> Prop) : (term537 A x') = (term538 A x').
Proof. exact (MK_COMB (@lem4828958 A) (@lem4828957 A x')). Qed.
Lemma lem4828964 {A : Type'} : (term539 A) = (term540 A).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4828959 A x')). Qed.
Lemma lem4828965 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828974 {A : Type'} : (term541 A) = (term542 A).
Proof. exact (MK_COMB (@lem4828965 A) (@lem4828964 A)). Qed.
Lemma lem4828975 {A : Type'} (s : type686 A) (x' : A -> Prop) : (s x') = (s x').
Proof. exact (eq_refl (s x')). Qed.
Lemma lem4828980 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term235 A t s x) = (term235 A t s x).
Proof. exact (eq_refl (term235 A t s x)). Qed.
Lemma lem4828981 {A : Type'} (t : type686 A) (s : type686 A) : (term237 A t s) = (term237 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4828980 A t s x)). Qed.
Lemma lem4828982 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4828983 {A : Type'} (t : type686 A) (s : type686 A) : (term238 A t s) = (term238 A t s).
Proof. exact (MK_COMB (@lem4828982 A) (@lem4828981 A t s)). Qed.
Lemma lem4828986 {A : Type'} (t : type686 A) (x : A -> Prop) : (term251 A t x) = (term251 A t x).
Proof. exact (eq_refl (term251 A t x)). Qed.
Lemma lem4828987 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) : (term478 A x t s) = (term478 A x t s).
Proof. exact (MK_COMB (@lem4828986 A t x) (@lem4828983 A t s)). Qed.
Lemma lem4828990 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term251 A s x') = (term251 A s x').
Proof. exact (eq_refl (term251 A s x')). Qed.
Lemma lem4828991 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term479 A x' x t s) = (term479 A x' x t s).
Proof. exact (MK_COMB (@lem4828990 A s x') (@lem4828987 A x t s)). Qed.
Lemma lem4828996 {A : Type'} (t : type686 A) (x' : A -> Prop) : (term287 A t x') = (term287 A t x').
Proof. exact (eq_refl (term287 A t x')). Qed.
Lemma lem4828997 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term480 A x' x t s) = (term480 A x' x t s).
Proof. exact (MK_COMB (@lem4828996 A t x') (@lem4828991 A x' x t s)). Qed.
Lemma lem4828998 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4828999 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term481 A x' x t s) = (term481 A x' x t s).
Proof. exact (MK_COMB (@lem4828998) (@lem4828997 A x' x t s)). Qed.
Lemma lem4829000 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : (term520 A x t s x') = (term520 A x t s x').
Proof. exact (MK_COMB (@lem4828999 A x' x t s) (@lem4828975 A s x')). Qed.
Lemma lem4829001 {A : Type'} (t : type686 A) (s : type686 A) (x' : A -> Prop) : (term528 A t s x') = (term528 A t s x').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4829000 A x t s x')). Qed.
Lemma lem4829002 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4829003 {A : Type'} (t : type686 A) (s : type686 A) (x' : A -> Prop) : (term530 A t s x') = (term530 A t s x').
Proof. exact (MK_COMB (@lem4829002 A) (@lem4829001 A t s x')). Qed.
Lemma lem4829004 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term532 A s x') = (term532 A s x').
Proof. exact (fun_ext (fun t : type686 A => @lem4829003 A t s x')). Qed.
Lemma lem4829005 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4829006 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term534 A s x') = (term534 A s x').
Proof. exact (MK_COMB (@lem4829005 A) (@lem4829004 A s x')). Qed.
Lemma lem4829007 {A : Type'} (x' : A -> Prop) : (term536 A x') = (term536 A x').
Proof. exact (fun_ext (fun s : type686 A => @lem4829006 A s x')). Qed.
Lemma lem4829008 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4829009 {A : Type'} (x' : A -> Prop) : (term538 A x') = (term538 A x').
Proof. exact (MK_COMB (@lem4829008 A) (@lem4829007 A x')). Qed.
Lemma lem4829010 {A : Type'} : (term540 A) = (term540 A).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4829009 A x')). Qed.
Lemma lem4829011 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4829012 {A : Type'} : (term542 A) = (term542 A).
Proof. exact (MK_COMB (@lem4829011 A) (@lem4829010 A)). Qed.
Lemma lem4829055 {A : Type'} : (term541 A) = (term542 A).
Proof. exact (TRANS (@lem4828974 A) (@lem4829012 A)). Qed.
Lemma lem4829056 {A : Type'} : (term542 A) = (term541 A).
Proof. exact (SYM (@lem4829055 A)). Qed.
Lemma lem4829057 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term480 A x' x t s.
Proof. exact (h1). Qed.
Lemma lem4829059 (p : Prop) : p = (term98 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4829060 {A : Type'} (s : type686 A) (x' : A -> Prop) : (s x') = (term505 A s x').
Proof. exact (@lem4829059 (s x')). Qed.
Lemma lem4829061 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term505 A s x') = (s x').
Proof. exact (SYM (@lem4829060 A s x')). Qed.
Lemma lem4829062 {A : Type'} (s : type686 A) (x' : A -> Prop) (h1 : term253 A s x') : term253 A s x'.
Proof. exact (h1). Qed.
Lemma lem4829072 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term235 A t s x) = (term278 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem4829073 {A : Type'} (t : type686 A) (s : type686 A) : (term237 A t s) = (term279 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4829072 A t s x)). Qed.
Lemma lem4829074 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4829075 {A : Type'} (t : type686 A) (s : type686 A) : (term238 A t s) = (term280 A t s).
Proof. exact (MK_COMB (@lem4829074 A) (@lem4829073 A t s)). Qed.
Lemma lem4829077 {A : Type'} (t : type686 A) (x : A -> Prop) : (term251 A t x) = (term251 A t x).
Proof. exact (eq_refl (term251 A t x)). Qed.
Lemma lem4829078 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) : (term478 A x t s) = (term506 A x t s).
Proof. exact (MK_COMB (@lem4829077 A t x) (@lem4829075 A t s)). Qed.
Lemma lem4829080 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term251 A s x') = (term251 A s x').
Proof. exact (eq_refl (term251 A s x')). Qed.
Lemma lem4829081 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term479 A x' x t s) = (term507 A x' x t s).
Proof. exact (MK_COMB (@lem4829080 A s x') (@lem4829078 A x t s)). Qed.
Lemma lem4829083 {A : Type'} (t : type686 A) (x' : A -> Prop) : (term287 A t x') = (term287 A t x').
Proof. exact (eq_refl (term287 A t x')). Qed.
Lemma lem4829120 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term480 A x' x t s) = (term508 A x' x t s).
Proof. exact (MK_COMB (@lem4829083 A t x') (@lem4829081 A x' x t s)). Qed.
Lemma lem4829121 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term508 A x' x t s.
Proof. exact (EQ_MP (@lem4829120 A x' x t s) (@lem4829057 A x' x t s h1)). Qed.
Lemma lem4829127 {A : Type'} (s : type686 A) (x' : A -> Prop) (h1 : term253 A s x') : term253 A s x'.
Proof. exact (h1). Qed.
Lemma lem4829138 {A : Type'} (t : type686 A) (s : type686 A) (x : A -> Prop) : (term278 A t s x) = (term278 A t s x).
Proof. exact (eq_refl (term278 A t s x)). Qed.
Lemma lem4829139 {A : Type'} (t : type686 A) (s : type686 A) : (term279 A t s) = (term279 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4829138 A t s x)). Qed.
Lemma lem4829140 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4829141 {A : Type'} (t : type686 A) (s : type686 A) : (term280 A t s) = (term280 A t s).
Proof. exact (MK_COMB (@lem4829140 A) (@lem4829139 A t s)). Qed.
Lemma lem4829146 {A : Type'} (t : type686 A) (x : A -> Prop) : (term251 A t x) = (term251 A t x).
Proof. exact (eq_refl (term251 A t x)). Qed.
Lemma lem4829147 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) : (term506 A x t s) = (term506 A x t s).
Proof. exact (MK_COMB (@lem4829146 A t x) (@lem4829141 A t s)). Qed.
Lemma lem4829152 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term251 A s x') = (term251 A s x').
Proof. exact (eq_refl (term251 A s x')). Qed.
Lemma lem4829153 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term507 A x' x t s) = (term507 A x' x t s).
Proof. exact (MK_COMB (@lem4829152 A s x') (@lem4829147 A x t s)). Qed.
Lemma lem4829160 {A : Type'} (t : type686 A) (x' : A -> Prop) : (term287 A t x') = (term287 A t x').
Proof. exact (eq_refl (term287 A t x')). Qed.
Lemma lem4829161 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) : (term508 A x' x t s) = (term508 A x' x t s).
Proof. exact (MK_COMB (@lem4829160 A t x') (@lem4829153 A x' x t s)). Qed.
Lemma lem4829162 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term508 A x' x t s.
Proof. exact (EQ_MP (@lem4829161 A x' x t s) (@lem4829121 A x' x t s h1)). Qed.
Lemma lem4829168 {A : Type'} (s : type686 A) (x' : A -> Prop) (h1 : term253 A s x') : term253 A s x'.
Proof. exact (h1). Qed.
Lemma lem4829169 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term507 A x' x t s.
Proof. exact (proj2 (@lem4829162 A x' x t s h1)). Qed.
Lemma lem4829178 {A : Type'} (s : type686 A) (x' : A -> Prop) (h1 : term253 A s x') : term253 A s x'.
Proof. exact (h1). Qed.
Lemma lem4829208 {A : Type'} (s : type686 A) (x' : A -> Prop) (h1 : term253 A s x') : term253 A s x'.
Proof. exact (h1). Qed.
Lemma lem4829222 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : s x'.
Proof. exact (proj1 (@lem4829169 A x' x t s h1)). Qed.
Lemma lem4829223 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term319 A s x'.
Proof. exact (fun h0 : term253 A s x' => @lem4829222 A x' x t s h1). Qed.
Lemma lem4829225 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4829226 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term319 A s x') = (s x').
Proof. exact (@lem4829225 (s x')). Qed.
Lemma lem4829227 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : s x'.
Proof. exact (EQ_MP (@lem4829226 A s x') (@lem4829223 A x' x t s h1)). Qed.
Lemma lem4829230 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4829232 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term253 A s x') = (term328 A s x').
Proof. exact (@lem4829230 (s x')). Qed.
Lemma lem4829235 {A : Type'} (s : type686 A) (x' : A -> Prop) (h1 : term253 A s x') : term328 A s x'.
Proof. exact (EQ_MP (@lem4829232 A s x') (@lem4829208 A s x' h1)). Qed.
Lemma lem4829238 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x') (h2 : term480 A x' x t s) : False.
Proof. exact (@lem4829235 A s x' h1 (@lem4829227 A x' x t s h2)). Qed.
Lemma lem4829239 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x') (h2 : term480 A x' x t s) : term197.
Proof. exact (fun h0 : ~ False => @lem4829238 A x' x t s h1 h2). Qed.
Lemma lem4829241 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4829242 : term197 = False.
Proof. exact (@lem4829241 False). Qed.
Lemma lem4829243 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x') (h2 : term480 A x' x t s) : False.
Proof. exact (EQ_MP (@lem4829242) (@lem4829239 A x' x t s h1 h2)). Qed.
Lemma lem4829244 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x') (h2 : term480 A x' x t s) : (term253 A s x') = False.
Proof. exact (prop_ext (fun h3 : term253 A s x' => @lem4829243 A x' x t s h1 h2) (fun h3 : False => @lem4829208 A s x' h1)). Qed.
Lemma lem4829245 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x') (h2 : term480 A x' x t s) : False.
Proof. exact (EQ_MP (@lem4829244 A x' x t s h1 h2) (@lem4829208 A s x' h1)). Qed.
Lemma lem4829246 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x') (h2 : term480 A x' x t s) : (term253 A s x') = False.
Proof. exact (prop_ext (fun h3 : term253 A s x' => @lem4829245 A x' x t s h1 h2) (fun h3 : False => @lem4829178 A s x' h1)). Qed.
Lemma lem4829247 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x') (h2 : term480 A x' x t s) : False.
Proof. exact (EQ_MP (@lem4829246 A x' x t s h1 h2) (@lem4829178 A s x' h1)). Qed.
Lemma lem4829248 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x') (h2 : term480 A x' x t s) : (term253 A s x') = False.
Proof. exact (prop_ext (fun h3 : term253 A s x' => @lem4829247 A x' x t s h1 h2) (fun h3 : False => @lem4829178 A s x' h1)). Qed.
Lemma lem4829249 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x') (h2 : term480 A x' x t s) : False.
Proof. exact (EQ_MP (@lem4829248 A x' x t s h1 h2) (@lem4829178 A s x' h1)). Qed.
Lemma lem4829250 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x') (h2 : term480 A x' x t s) : (term253 A s x') = False.
Proof. exact (prop_ext (fun h3 : term253 A s x' => @lem4829249 A x' x t s h1 h2) (fun h3 : False => @lem4829168 A s x' h1)). Qed.
Lemma lem4829251 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x') (h2 : term480 A x' x t s) : False.
Proof. exact (EQ_MP (@lem4829250 A x' x t s h1 h2) (@lem4829168 A s x' h1)). Qed.
Lemma lem4829252 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x') (h2 : term480 A x' x t s) : (term253 A s x') = False.
Proof. exact (prop_ext (fun h3 : term253 A s x' => @lem4829251 A x' x t s h1 h2) (fun h3 : False => @lem4829127 A s x' h1)). Qed.
Lemma lem4829253 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x') (h2 : term480 A x' x t s) : False.
Proof. exact (EQ_MP (@lem4829252 A x' x t s h1 h2) (@lem4829127 A s x' h1)). Qed.
Lemma lem4829254 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x') (h2 : term480 A x' x t s) : (term253 A s x') = False.
Proof. exact (prop_ext (fun h3 : term253 A s x' => @lem4829253 A x' x t s h1 h2) (fun h3 : False => @lem4829062 A s x' h1)). Qed.
Lemma lem4829255 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term253 A s x') (h2 : term480 A x' x t s) : False.
Proof. exact (EQ_MP (@lem4829254 A x' x t s h1 h2) (@lem4829062 A s x' h1)). Qed.
Lemma lem4829256 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : term505 A s x'.
Proof. exact (fun h0 : term253 A s x' => @lem4829255 A x' x t s h0 h1). Qed.
Lemma lem4829257 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term480 A x' x t s) : s x'.
Proof. exact (EQ_MP (@lem4829061 A s x') (@lem4829256 A x' x t s h1)). Qed.
Lemma lem4829258 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : term520 A x t s x'.
Proof. exact (fun h0 : term480 A x' x t s => @lem4829257 A x' x t s h0). Qed.
Lemma lem4829263 {A : Type'} (t : type686 A) (s : type686 A) (x' : A -> Prop) : term530 A t s x'.
Proof. exact (fun x : A -> Prop => @lem4829258 A x t s x'). Qed.
Lemma lem4829268 {A : Type'} (s : type686 A) (x' : A -> Prop) : term534 A s x'.
Proof. exact (fun t : type686 A => @lem4829263 A t s x'). Qed.
Lemma lem4829273 {A : Type'} (x' : A -> Prop) : term538 A x'.
Proof. exact (fun s : type686 A => @lem4829268 A s x'). Qed.
Lemma lem4829278 {A : Type'} : term542 A.
Proof. exact (fun x' : A -> Prop => @lem4829273 A x'). Qed.
Lemma lem4829279 {A : Type'} : term541 A.
Proof. exact (EQ_MP (@lem4829056 A) (@lem4829278 A)). Qed.
Lemma lem4829280 {A : Type'} (x' : A -> Prop) : term543 A x'.
Proof. exact (@lem4829279 A x'). Qed.
Lemma lem4829281 {A : Type'} (x' : A -> Prop) : (term543 A x') = (term537 A x').
Proof. exact (eq_refl (term543 A x')). Qed.
Lemma lem4829282 {A : Type'} (x' : A -> Prop) : term537 A x'.
Proof. exact (EQ_MP (@lem4829281 A x') (@lem4829280 A x')). Qed.
Lemma lem4829283 {A : Type'} (x' : A -> Prop) (s : type686 A) : term544 A x' s.
Proof. exact (@lem4829282 A x' s). Qed.
Lemma lem4829284 {A : Type'} (s : type686 A) (x' : A -> Prop) : (term544 A x' s) = (term533 A s x').
Proof. exact (eq_refl (term544 A x' s)). Qed.
Lemma lem4829285 {A : Type'} (s : type686 A) (x' : A -> Prop) : term533 A s x'.
Proof. exact (EQ_MP (@lem4829284 A s x') (@lem4829283 A x' s)). Qed.
Lemma lem4829286 {A : Type'} (s : type686 A) (x' : A -> Prop) (t : type686 A) : term545 A s x' t.
Proof. exact (@lem4829285 A s x' t). Qed.
Lemma lem4829287 {A : Type'} (t : type686 A) (s : type686 A) (x' : A -> Prop) : (term545 A s x' t) = (term529 A t s x').
Proof. exact (eq_refl (term545 A s x' t)). Qed.
Lemma lem4829288 {A : Type'} (t : type686 A) (s : type686 A) (x' : A -> Prop) : term529 A t s x'.
Proof. exact (EQ_MP (@lem4829287 A t s x') (@lem4829286 A s x' t)). Qed.
Lemma lem4829289 {A : Type'} (t : type686 A) (s : type686 A) (x' : A -> Prop) (x : A -> Prop) : term546 A t s x' x.
Proof. exact (@lem4829288 A t s x' x). Qed.
Lemma lem4829290 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : (term546 A t s x' x) = (term521 A x t s x').
Proof. exact (eq_refl (term546 A t s x' x)). Qed.
Lemma lem4829291 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : term521 A x t s x'.
Proof. exact (EQ_MP (@lem4829290 A x t s x') (@lem4829289 A t s x' x)). Qed.
Lemma lem4829293 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : term521 A x t s x'.
Proof. exact (@lem4828905 A x t s x' (@lem4829291 A x t s x')). Qed.
Lemma lem4829294 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) (h1 : term522 A x t s x') : False.
Proof. exact (@lem4829293 A x t s x' (@lem4828889 A x t s x' h1)). Qed.
Lemma lem4829295 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) (h1 : term522 A x t s x') : (term522 A x t s x') = False.
Proof. exact (prop_ext (fun h2 : term522 A x t s x' => @lem4829294 A x t s x' h1) (fun h2 : False => @lem4828889 A x t s x' h1)). Qed.
Lemma lem4829296 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) (h1 : term522 A x t s x') : False.
Proof. exact (EQ_MP (@lem4829295 A x t s x' h1) (@lem4828889 A x t s x' h1)). Qed.
Lemma lem4829297 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : term521 A x t s x'.
Proof. exact (fun h0 : term522 A x t s x' => @lem4829296 A x t s x' h0). Qed.
Lemma lem4829298 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (x' : A -> Prop) : term520 A x t s x'.
Proof. exact (EQ_MP (@lem4828888 A x t s x') (@lem4829297 A x t s x')). Qed.
Lemma lem4829299 {A : Type'} (x : A -> Prop) (t : type686 A) (x' : A -> Prop) (s : type686 A) : term519 A x t x' s.
Proof. exact (EQ_MP (@lem4828884 A x t x' s) (@lem4829298 A x t s x')). Qed.
Lemma lem4829300 {A : Type'} (x : A -> Prop) (t : type686 A) (x' : A -> Prop) (s : type686 A) : term518 A x t x' s.
Proof. exact (EQ_MP (@lem4828811 A x t x' s) (@lem4829299 A x t x' s)). Qed.
Lemma lem4829301 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term252 A x' t) (h2 : @IN (A -> Prop) x t) (h3 : @IN (A -> Prop) x' s) (h4 : @SUBSET (A -> Prop) t s) : @IN (A -> Prop) x' s.
Proof. exact (@lem4829300 A x t x' s (@lem4828774 A x x' t s h1 h2 h3 h4)). Qed.
Lemma lem4829302 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem4829305 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (h1 : term547 A s t x x') : term547 A s t x x'.
Proof. exact (h1). Qed.
Lemma lem4829306 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : term548 A s t x x'.
Proof. exact (fun h0 : term547 A s t x x' => @lem4829305 A s t x x' h0). Qed.
Lemma lem4829307 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (h1 : term548 A s t x x') : term548 A s t x x'.
Proof. exact (h1). Qed.
Lemma lem4829308 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (h1 : term547 A s t x x') : term547 A s t x x'.
Proof. exact (h1). Qed.
Lemma lem4829309 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (h1 : term548 A s t x x') (h2 : term547 A s t x x') : term547 A s t x x'.
Proof. exact (@lem4829307 A s t x x' h1 (@lem4829308 A s t x x' h2)). Qed.
Lemma lem4829310 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (h1 : term547 A s t x x') : term549 A s t x x'.
Proof. exact (fun h0 : term548 A s t x x' => @lem4829309 A s t x x' h0 h1). Qed.
Lemma lem4829311 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (h1 : term548 A s t x x') : term548 A s t x x'.
Proof. exact (h1). Qed.
Lemma lem4829312 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (h1 : term548 A s t x x') (h2 : term547 A s t x x') : term547 A s t x x'.
Proof. exact (@lem4829310 A s t x x' h2 (@lem4829311 A s t x x' h1)). Qed.
Lemma lem4829313 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (h1 : term548 A s t x x') : term548 A s t x x'.
Proof. exact (fun h0 : term547 A s t x x' => @lem4829312 A s t x x' h1 h0). Qed.
Lemma lem4829314 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : term550 A s t x x'.
Proof. exact (fun h0 : term548 A s t x x' => @lem4829313 A s t x x' h0). Qed.
Lemma lem4829317 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : term548 A s t x x'.
Proof. exact (@lem4829314 A s t x x' (@lem4829306 A s t x x')). Qed.
Lemma lem4829318 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : term548 A s t x x'.
Proof. exact (@lem4829317 A s t x x'). Qed.
Lemma lem4829344 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4829345 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term551 A x x') = (term552 A x x').
Proof. exact (@lem4829344 (x = x')). Qed.
Lemma lem4829346 {A : Type'} (x' : A -> Prop) (t : type686 A) : (term553 A x' t) = (term553 A x' t).
Proof. exact (eq_refl (term553 A x' t)). Qed.
Lemma lem4829347 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term554 A t x x') = (term555 A t x x').
Proof. exact (MK_COMB (@lem4829346 A x' t) (@lem4829345 A x x')). Qed.
Lemma lem4829350 {A : Type'} (x' : A -> Prop) (s : type686 A) : (term232 A x' s) = (term232 A x' s).
Proof. exact (eq_refl (term232 A x' s)). Qed.
Lemma lem4829351 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term556 A s t x x') = (term557 A s t x x').
Proof. exact (MK_COMB (@lem4829350 A x' s) (@lem4829347 A t x x')). Qed.
Lemma lem4829354 {A : Type'} (x : A -> Prop) (t : type686 A) : (term232 A x t) = (term232 A x t).
Proof. exact (eq_refl (term232 A x t)). Qed.
Lemma lem4829355 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term558 A s t x x') = (term559 A s t x x').
Proof. exact (MK_COMB (@lem4829354 A x t) (@lem4829351 A s t x x')). Qed.
Lemma lem4829358 {A : Type'} (t : type686 A) (s : type686 A) : (term560 A t s) = (term560 A t s).
Proof. exact (eq_refl (term560 A t s)). Qed.
Lemma lem4829359 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term547 A s t x x') = (term561 A s t x x').
Proof. exact (MK_COMB (@lem4829358 A t s) (@lem4829355 A s t x x')). Qed.
Lemma lem4829362 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term562 A t x x') = (term563 A t x x').
Proof. exact (fun_ext (fun s : type686 A => @lem4829359 A s t x x')). Qed.
Lemma lem4829363 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4829364 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term564 A t x x') = (term565 A t x x').
Proof. exact (MK_COMB (@lem4829363 A) (@lem4829362 A t x x')). Qed.
Lemma lem4829369 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term566 A x x') = (term567 A x x').
Proof. exact (fun_ext (fun t : type686 A => @lem4829364 A t x x')). Qed.
Lemma lem4829370 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4829371 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term568 A x x') = (term569 A x x').
Proof. exact (MK_COMB (@lem4829370 A) (@lem4829369 A x x')). Qed.
Lemma lem4829376 {A : Type'} (x' : A -> Prop) : (term570 A x') = (term571 A x').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4829371 A x x')). Qed.
Lemma lem4829377 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4829378 {A : Type'} (x' : A -> Prop) : (term572 A x') = (term573 A x').
Proof. exact (MK_COMB (@lem4829377 A) (@lem4829376 A x')). Qed.
Lemma lem4829383 {A : Type'} : (term574 A) = (term575 A).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4829378 A x')). Qed.
Lemma lem4829384 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4829393 {A : Type'} : (term576 A) = (term577 A).
Proof. exact (MK_COMB (@lem4829384 A) (@lem4829383 A)). Qed.
Lemma lem4829414 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term561 A s t x x') = (term561 A s t x x').
Proof. exact (eq_refl (term561 A s t x x')). Qed.
Lemma lem4829415 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term563 A t x x') = (term563 A t x x').
Proof. exact (fun_ext (fun s : type686 A => @lem4829414 A s t x x')). Qed.
Lemma lem4829416 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4829417 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term565 A t x x') = (term565 A t x x').
Proof. exact (MK_COMB (@lem4829416 A) (@lem4829415 A t x x')). Qed.
Lemma lem4829418 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term567 A x x') = (term567 A x x').
Proof. exact (fun_ext (fun t : type686 A => @lem4829417 A t x x')). Qed.
Lemma lem4829419 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4829420 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term569 A x x') = (term569 A x x').
Proof. exact (MK_COMB (@lem4829419 A) (@lem4829418 A x x')). Qed.
Lemma lem4829421 {A : Type'} (x' : A -> Prop) : (term571 A x') = (term571 A x').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4829420 A x x')). Qed.
Lemma lem4829422 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4829423 {A : Type'} (x' : A -> Prop) : (term573 A x') = (term573 A x').
Proof. exact (MK_COMB (@lem4829422 A) (@lem4829421 A x')). Qed.
Lemma lem4829424 {A : Type'} : (term575 A) = (term575 A).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4829423 A x')). Qed.
Lemma lem4829425 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4829426 {A : Type'} : (term577 A) = (term577 A).
Proof. exact (MK_COMB (@lem4829425 A) (@lem4829424 A)). Qed.
Lemma lem4829461 {A : Type'} : (term576 A) = (term577 A).
Proof. exact (TRANS (@lem4829393 A) (@lem4829426 A)). Qed.
Lemma lem4829462 {A : Type'} : (term577 A) = (term576 A).
Proof. exact (SYM (@lem4829461 A)). Qed.
Lemma lem4829479 {A : Type'} (x : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) x t) : @IN (A -> Prop) x t.
Proof. exact (h1). Qed.
Lemma lem4829491 {A : Type'} (x' : A -> Prop) (t : type686 A) (h1 : term252 A x' t) : term252 A x' t.
Proof. exact (h1). Qed.
Lemma lem4829497 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem4829509 {A : Type'} (x : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) x t) : @IN (A -> Prop) x t.
Proof. exact (h1). Qed.
Lemma lem4829523 {A : Type'} (x' : A -> Prop) (t : type686 A) (h1 : term252 A x' t) : term252 A x' t.
Proof. exact (h1). Qed.
Lemma lem4829529 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem4829537 {A : Type'} (x : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) x t) : @IN (A -> Prop) x t.
Proof. exact (h1). Qed.
Lemma lem4829545 {A : Type'} (x' : A -> Prop) (t : type686 A) (h1 : term252 A x' t) : term252 A x' t.
Proof. exact (h1). Qed.
Lemma lem4829549 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem4829553 {A : Type'} (x : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) x t) : @IN (A -> Prop) x t.
Proof. exact (h1). Qed.
Lemma lem4829557 {A : Type'} (x' : A -> Prop) (t : type686 A) (h1 : term252 A x' t) : term252 A x' t.
Proof. exact (h1). Qed.
Lemma lem4829559 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem4829588 {A : Type'} (t : type686 A) : (term355 A t) = (term355 A t).
Proof. exact (eq_refl (term355 A t)). Qed.
Lemma lem4829589 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (h1 : x = x') : (term358 A t x) = (term358 A t x').
Proof. exact (MK_COMB (@lem4829588 A t) (@lem4829559 A x x' h1)). Qed.
Lemma lem4829590 {A : Type'} (x' : A -> Prop) (t : type686 A) : (term358 A t x') = (@IN (A -> Prop) x' t).
Proof. exact (eq_refl (term358 A t x')). Qed.
Lemma lem4829591 {A : Type'} (t : type686 A) (x : A -> Prop) : (term578 A t x) = (term578 A t x).
Proof. exact (eq_refl (term578 A t x)). Qed.
Lemma lem4829592 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) : ((term358 A t x) = (term358 A t x')) = ((term358 A t x) = (@IN (A -> Prop) x' t)).
Proof. exact (MK_COMB (@lem4829591 A t x) (@lem4829590 A x' t)). Qed.
Lemma lem4829593 {A : Type'} (x : A -> Prop) (t : type686 A) : (term358 A t x) = (@IN (A -> Prop) x t).
Proof. exact (eq_refl (term358 A t x)). Qed.
Lemma lem4829594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4829595 {A : Type'} (x : A -> Prop) (t : type686 A) : (term578 A t x) = (term579 A x t).
Proof. exact (MK_COMB (@lem4829594) (@lem4829593 A x t)). Qed.
Lemma lem4829596 {A : Type'} (x' : A -> Prop) (t : type686 A) : (@IN (A -> Prop) x' t) = (@IN (A -> Prop) x' t).
Proof. exact (eq_refl (@IN (A -> Prop) x' t)). Qed.
Lemma lem4829597 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) : ((term358 A t x) = (@IN (A -> Prop) x' t)) = ((@IN (A -> Prop) x t) = (@IN (A -> Prop) x' t)).
Proof. exact (MK_COMB (@lem4829595 A x t) (@lem4829596 A x' t)). Qed.
Lemma lem4829598 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) : ((term358 A t x) = (term358 A t x')) = ((@IN (A -> Prop) x t) = (@IN (A -> Prop) x' t)).
Proof. exact (TRANS (@lem4829592 A x x' t) (@lem4829597 A x x' t)). Qed.
Lemma lem4829599 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (h1 : x = x') : (@IN (A -> Prop) x t) = (@IN (A -> Prop) x' t).
Proof. exact (EQ_MP (@lem4829598 A x x' t) (@lem4829589 A t x x' h1)). Qed.
Lemma lem4829628 {A : Type'} (x' : A -> Prop) (t : type686 A) (h1 : term252 A x' t) : term252 A x' t.
Proof. exact (h1). Qed.
Lemma lem4829630 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : x = x') (h2 : @IN (A -> Prop) x t) : @IN (A -> Prop) x' t.
Proof. exact (EQ_MP (@lem4829599 A t x x' h1) (@lem4829553 A x t h2)). Qed.
Lemma lem4829631 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : x = x') (h2 : @IN (A -> Prop) x t) : term580 A x' t.
Proof. exact (fun h0 : term252 A x' t => @lem4829630 A x' x t h1 h2). Qed.
Lemma lem4829633 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4829634 {A : Type'} (x' : A -> Prop) (t : type686 A) : (term580 A x' t) = (@IN (A -> Prop) x' t).
Proof. exact (@lem4829633 (@IN (A -> Prop) x' t)). Qed.
Lemma lem4829635 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : x = x') (h2 : @IN (A -> Prop) x t) : @IN (A -> Prop) x' t.
Proof. exact (EQ_MP (@lem4829634 A x' t) (@lem4829631 A x' x t h1 h2)). Qed.
Lemma lem4829638 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4829640 {A : Type'} (x' : A -> Prop) (t : type686 A) : (term252 A x' t) = (term581 A x' t).
Proof. exact (@lem4829638 (@IN (A -> Prop) x' t)). Qed.
Lemma lem4829643 {A : Type'} (x' : A -> Prop) (t : type686 A) (h1 : term252 A x' t) : term581 A x' t.
Proof. exact (EQ_MP (@lem4829640 A x' t) (@lem4829628 A x' t h1)). Qed.
Lemma lem4829646 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (@lem4829643 A x' t h1 (@lem4829635 A x' x t h2 h3)). Qed.
Lemma lem4829647 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : term197.
Proof. exact (fun h0 : ~ False => @lem4829646 A x' x t h1 h2 h3). Qed.
Lemma lem4829649 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4829650 : term197 = False.
Proof. exact (@lem4829649 False). Qed.
Lemma lem4829651 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829650) (@lem4829647 A x' x t h1 h2 h3)). Qed.
Lemma lem4829652 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (term252 A x' t) = False.
Proof. exact (prop_ext (fun h4 : term252 A x' t => @lem4829651 A x' x t h1 h2 h3) (fun h4 : False => @lem4829628 A x' t h1)). Qed.
Lemma lem4829654 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829652 A x' x t h1 h2 h3) (@lem4829628 A x' t h1)). Qed.
Lemma lem4829655 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (x = x') = False.
Proof. exact (prop_ext (fun h4 : x = x' => @lem4829654 A x' x t h1 h2 h3) (fun h4 : False => @lem4829559 A x x' h2)). Qed.
Lemma lem4829656 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829655 A x' x t h1 h2 h3) (@lem4829559 A x x' h2)). Qed.
Lemma lem4829657 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (term252 A x' t) = False.
Proof. exact (prop_ext (fun h4 : term252 A x' t => @lem4829656 A x' x t h1 h2 h3) (fun h4 : False => @lem4829557 A x' t h1)). Qed.
Lemma lem4829658 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829657 A x' x t h1 h2 h3) (@lem4829557 A x' t h1)). Qed.
Lemma lem4829659 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (@IN (A -> Prop) x t) = False.
Proof. exact (prop_ext (fun h4 : @IN (A -> Prop) x t => @lem4829658 A x' x t h1 h2 h3) (fun h4 : False => @lem4829553 A x t h3)). Qed.
Lemma lem4829660 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829659 A x' x t h1 h2 h3) (@lem4829553 A x t h3)). Qed.
Lemma lem4829661 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (x = x') = False.
Proof. exact (prop_ext (fun h4 : x = x' => @lem4829660 A x' x t h1 h2 h3) (fun h4 : False => @lem4829549 A x x' h2)). Qed.
Lemma lem4829662 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829661 A x' x t h1 h2 h3) (@lem4829549 A x x' h2)). Qed.
Lemma lem4829663 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (term252 A x' t) = False.
Proof. exact (prop_ext (fun h4 : term252 A x' t => @lem4829662 A x' x t h1 h2 h3) (fun h4 : False => @lem4829545 A x' t h1)). Qed.
Lemma lem4829664 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829663 A x' x t h1 h2 h3) (@lem4829545 A x' t h1)). Qed.
Lemma lem4829665 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (@IN (A -> Prop) x t) = False.
Proof. exact (prop_ext (fun h4 : @IN (A -> Prop) x t => @lem4829664 A x' x t h1 h2 h3) (fun h4 : False => @lem4829537 A x t h3)). Qed.
Lemma lem4829666 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829665 A x' x t h1 h2 h3) (@lem4829537 A x t h3)). Qed.
Lemma lem4829667 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (x = x') = False.
Proof. exact (prop_ext (fun h4 : x = x' => @lem4829666 A x' x t h1 h2 h3) (fun h4 : False => @lem4829549 A x x' h2)). Qed.
Lemma lem4829668 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829667 A x' x t h1 h2 h3) (@lem4829549 A x x' h2)). Qed.
Lemma lem4829669 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (term252 A x' t) = False.
Proof. exact (prop_ext (fun h4 : term252 A x' t => @lem4829668 A x' x t h1 h2 h3) (fun h4 : False => @lem4829545 A x' t h1)). Qed.
Lemma lem4829670 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829669 A x' x t h1 h2 h3) (@lem4829545 A x' t h1)). Qed.
Lemma lem4829671 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (@IN (A -> Prop) x t) = False.
Proof. exact (prop_ext (fun h4 : @IN (A -> Prop) x t => @lem4829670 A x' x t h1 h2 h3) (fun h4 : False => @lem4829537 A x t h3)). Qed.
Lemma lem4829672 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829671 A x' x t h1 h2 h3) (@lem4829537 A x t h3)). Qed.
Lemma lem4829673 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (x = x') = False.
Proof. exact (prop_ext (fun h4 : x = x' => @lem4829672 A x' x t h1 h2 h3) (fun h4 : False => @lem4829529 A x x' h2)). Qed.
Lemma lem4829674 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829673 A x' x t h1 h2 h3) (@lem4829529 A x x' h2)). Qed.
Lemma lem4829675 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (term252 A x' t) = False.
Proof. exact (prop_ext (fun h4 : term252 A x' t => @lem4829674 A x' x t h1 h2 h3) (fun h4 : False => @lem4829523 A x' t h1)). Qed.
Lemma lem4829676 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829675 A x' x t h1 h2 h3) (@lem4829523 A x' t h1)). Qed.
Lemma lem4829677 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (@IN (A -> Prop) x t) = False.
Proof. exact (prop_ext (fun h4 : @IN (A -> Prop) x t => @lem4829676 A x' x t h1 h2 h3) (fun h4 : False => @lem4829509 A x t h3)). Qed.
Lemma lem4829678 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829677 A x' x t h1 h2 h3) (@lem4829509 A x t h3)). Qed.
Lemma lem4829679 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (x = x') = False.
Proof. exact (prop_ext (fun h4 : x = x' => @lem4829678 A x' x t h1 h2 h3) (fun h4 : False => @lem4829497 A x x' h2)). Qed.
Lemma lem4829680 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829679 A x' x t h1 h2 h3) (@lem4829497 A x x' h2)). Qed.
Lemma lem4829681 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (term252 A x' t) = False.
Proof. exact (prop_ext (fun h4 : term252 A x' t => @lem4829680 A x' x t h1 h2 h3) (fun h4 : False => @lem4829491 A x' t h1)). Qed.
Lemma lem4829682 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829681 A x' x t h1 h2 h3) (@lem4829491 A x' t h1)). Qed.
Lemma lem4829683 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : (@IN (A -> Prop) x t) = False.
Proof. exact (prop_ext (fun h4 : @IN (A -> Prop) x t => @lem4829682 A x' x t h1 h2 h3) (fun h4 : False => @lem4829479 A x t h3)). Qed.
Lemma lem4829684 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) : False.
Proof. exact (EQ_MP (@lem4829683 A x' x t h1 h2 h3) (@lem4829479 A x t h3)). Qed.
Lemma lem4829685 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : @IN (A -> Prop) x t) : term551 A x x'.
Proof. exact (fun h0 : x = x' => @lem4829684 A x' x t h1 h0 h2). Qed.
Lemma lem4829686 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term551 A x x') = (term552 A x x').
Proof. exact (@lem69 (x = x')). Qed.
Lemma lem4829687 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : term252 A x' t) (h2 : @IN (A -> Prop) x t) : term552 A x x'.
Proof. exact (EQ_MP (@lem4829686 A x x') (@lem4829685 A x' x t h1 h2)). Qed.
Lemma lem4829688 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) x t) : term555 A t x x'.
Proof. exact (fun h0 : term252 A x' t => @lem4829687 A x' x t h0 h1). Qed.
Lemma lem4829689 {A : Type'} (s : type686 A) (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) x t) : term557 A s t x x'.
Proof. exact (fun h0 : @IN (A -> Prop) x' s => @lem4829688 A x' x t h1). Qed.
Lemma lem4829690 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : term559 A s t x x'.
Proof. exact (fun h0 : @IN (A -> Prop) x t => @lem4829689 A s x' x t h0). Qed.
Lemma lem4829691 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : term561 A s t x x'.
Proof. exact (fun h0 : @SUBSET (A -> Prop) t s => @lem4829690 A s t x x'). Qed.
Lemma lem4829696 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : term565 A t x x'.
Proof. exact (fun s : type686 A => @lem4829691 A s t x x'). Qed.
Lemma lem4829701 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : term569 A x x'.
Proof. exact (fun t : type686 A => @lem4829696 A t x x'). Qed.
Lemma lem4829706 {A : Type'} (x' : A -> Prop) : term573 A x'.
Proof. exact (fun x : A -> Prop => @lem4829701 A x x'). Qed.
Lemma lem4829711 {A : Type'} : term577 A.
Proof. exact (fun x' : A -> Prop => @lem4829706 A x'). Qed.
Lemma lem4829712 {A : Type'} : term576 A.
Proof. exact (EQ_MP (@lem4829462 A) (@lem4829711 A)). Qed.
Lemma lem4829713 {A : Type'} (x' : A -> Prop) : term582 A x'.
Proof. exact (@lem4829712 A x'). Qed.
Lemma lem4829714 {A : Type'} (x' : A -> Prop) : (term582 A x') = (term572 A x').
Proof. exact (eq_refl (term582 A x')). Qed.
Lemma lem4829715 {A : Type'} (x' : A -> Prop) : term572 A x'.
Proof. exact (EQ_MP (@lem4829714 A x') (@lem4829713 A x')). Qed.
Lemma lem4829716 {A : Type'} (x' : A -> Prop) (x : A -> Prop) : term583 A x' x.
Proof. exact (@lem4829715 A x' x). Qed.
Lemma lem4829717 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term583 A x' x) = (term568 A x x').
Proof. exact (eq_refl (term583 A x' x)). Qed.
Lemma lem4829718 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : term568 A x x'.
Proof. exact (EQ_MP (@lem4829717 A x x') (@lem4829716 A x' x)). Qed.
Lemma lem4829719 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) : term584 A x x' t.
Proof. exact (@lem4829718 A x x' t). Qed.
Lemma lem4829720 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term584 A x x' t) = (term564 A t x x').
Proof. exact (eq_refl (term584 A x x' t)). Qed.
Lemma lem4829721 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : term564 A t x x'.
Proof. exact (EQ_MP (@lem4829720 A t x x') (@lem4829719 A x x' t)). Qed.
Lemma lem4829722 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (s : type686 A) : term585 A t x x' s.
Proof. exact (@lem4829721 A t x x' s). Qed.
Lemma lem4829723 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term585 A t x x' s) = (term547 A s t x x').
Proof. exact (eq_refl (term585 A t x x' s)). Qed.
Lemma lem4829724 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : term547 A s t x x'.
Proof. exact (EQ_MP (@lem4829723 A s t x x') (@lem4829722 A t x x' s)). Qed.
Lemma lem4829726 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : term547 A s t x x'.
Proof. exact (@lem4829318 A s t x x' (@lem4829724 A s t x x')). Qed.
Lemma lem4829727 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) : term558 A s t x x'.
Proof. exact (@lem4829726 A s t x x' (@lem4826912 A t s h1)). Qed.
Lemma lem4829728 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : @IN (A -> Prop) x t) (h2 : @SUBSET (A -> Prop) t s) : term556 A s t x x'.
Proof. exact (@lem4829727 A x x' t s h2 (@lem4828138 A x t h1)). Qed.
Lemma lem4829729 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : @IN (A -> Prop) x t) (h2 : @IN (A -> Prop) x' s) (h3 : @SUBSET (A -> Prop) t s) : term554 A t x x'.
Proof. exact (@lem4829728 A x' x t s h1 h3 (@lem4828141 A x' s h2)). Qed.
Lemma lem4829730 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term252 A x' t) (h2 : @IN (A -> Prop) x t) (h3 : @IN (A -> Prop) x' s) (h4 : @SUBSET (A -> Prop) t s) : term551 A x x'.
Proof. exact (@lem4829729 A x x' t s h2 h3 h4 (@lem4828140 A x' t h1)). Qed.
Lemma lem4829731 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) (h4 : @IN (A -> Prop) x' s) (h5 : @SUBSET (A -> Prop) t s) : False.
Proof. exact (@lem4829730 A x x' t s h1 h3 h4 h5 (@lem4829302 A x x' h2)). Qed.
Lemma lem4829732 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) (h4 : @IN (A -> Prop) x' s) (h5 : @SUBSET (A -> Prop) t s) : (x = x') = False.
Proof. exact (prop_ext (fun h6 : x = x' => @lem4829731 A x x' t s h1 h2 h3 h4 h5) (fun h6 : False => @lem4829302 A x x' h2)). Qed.
Lemma lem4829733 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term252 A x' t) (h2 : x = x') (h3 : @IN (A -> Prop) x t) (h4 : @IN (A -> Prop) x' s) (h5 : @SUBSET (A -> Prop) t s) : False.
Proof. exact (EQ_MP (@lem4829732 A x x' t s h1 h2 h3 h4 h5) (@lem4829302 A x x' h2)). Qed.
Lemma lem4829734 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term252 A x' t) (h2 : @IN (A -> Prop) x t) (h3 : @IN (A -> Prop) x' s) (h4 : @SUBSET (A -> Prop) t s) : term551 A x x'.
Proof. exact (fun h0 : x = x' => @lem4829733 A x x' t s h1 h0 h2 h3 h4). Qed.
Lemma lem4829735 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term551 A x x') = (term552 A x x').
Proof. exact (@lem69 (x = x')). Qed.
Lemma lem4829736 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term252 A x' t) (h2 : @IN (A -> Prop) x t) (h3 : @IN (A -> Prop) x' s) (h4 : @SUBSET (A -> Prop) t s) : term552 A x x'.
Proof. exact (EQ_MP (@lem4829735 A x x') (@lem4829734 A x x' t s h1 h2 h3 h4)). Qed.
Lemma lem4829737 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term252 A x' t) (h2 : @IN (A -> Prop) x t) (h3 : @IN (A -> Prop) x' s) (h4 : @SUBSET (A -> Prop) t s) : term586 A s x x'.
Proof. exact (conj (@lem4829301 A x x' t s h1 h2 h3 h4) (@lem4829736 A x x' t s h1 h2 h3 h4)). Qed.
Lemma lem4829738 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term252 A x' t) (h2 : @IN (A -> Prop) x t) (h3 : @IN (A -> Prop) x' s) (h4 : @SUBSET (A -> Prop) t s) : term464 A s x x'.
Proof. exact (conj (@lem4828761 A x x' t s h1 h2 h3 h4) (@lem4829737 A x x' t s h1 h2 h3 h4)). Qed.
Lemma lem4829739 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : term252 A x' t) (h3 : @IN (A -> Prop) x t) (h4 : @IN (A -> Prop) x' s) (h5 : @SUBSET (A -> Prop) t s) : (@INTER A x x') = (@EMPTY A).
Proof. exact (@lem4828168 A x x' s h1 (@lem4829738 A x x' t s h2 h3 h4 h5)). Qed.
Lemma lem4829740 {A : Type'} (s : type686 A) (x' : A -> Prop) (t : type686 A) (h1 : term249 A s x' t) : term252 A x' t.
Proof. exact (proj2 (@lem4828139 A s x' t h1)). Qed.
Lemma lem4829741 {A : Type'} (s : type686 A) (x' : A -> Prop) (t : type686 A) (h1 : term249 A s x' t) : @IN (A -> Prop) x' s.
Proof. exact (proj1 (@lem4828139 A s x' t h1)). Qed.
Lemma lem4829742 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : term252 A x' t) (h3 : @IN (A -> Prop) x t) (h4 : @IN (A -> Prop) x' s) (h5 : @SUBSET (A -> Prop) t s) : (term252 A x' t) = ((@INTER A x x') = (@EMPTY A)).
Proof. exact (prop_ext (fun h6 : term252 A x' t => @lem4829739 A x x' t s h1 h2 h3 h4 h5) (fun h6 : (@INTER A x x') = (@EMPTY A) => @lem4828140 A x' t h2)). Qed.
Lemma lem4829743 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : term252 A x' t) (h3 : @IN (A -> Prop) x t) (h4 : @IN (A -> Prop) x' s) (h5 : @SUBSET (A -> Prop) t s) : (@INTER A x x') = (@EMPTY A).
Proof. exact (EQ_MP (@lem4829742 A x x' t s h1 h2 h3 h4 h5) (@lem4828140 A x' t h2)). Qed.
Lemma lem4829744 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : term252 A x' t) (h3 : @IN (A -> Prop) x t) (h4 : @IN (A -> Prop) x' s) (h5 : @SUBSET (A -> Prop) t s) : (@IN (A -> Prop) x' s) = ((@INTER A x x') = (@EMPTY A)).
Proof. exact (prop_ext (fun h6 : @IN (A -> Prop) x' s => @lem4829743 A x x' t s h1 h2 h3 h4 h5) (fun h6 : (@INTER A x x') = (@EMPTY A) => @lem4828141 A x' s h4)). Qed.
Lemma lem4829745 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : term252 A x' t) (h3 : @IN (A -> Prop) x t) (h4 : @IN (A -> Prop) x' s) (h5 : @SUBSET (A -> Prop) t s) : (@INTER A x x') = (@EMPTY A).
Proof. exact (EQ_MP (@lem4829744 A x x' t s h1 h2 h3 h4 h5) (@lem4828141 A x' s h4)). Qed.
Lemma lem4829746 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : term249 A s x' t) (h3 : @IN (A -> Prop) x t) (h4 : @IN (A -> Prop) x' s) (h5 : @SUBSET (A -> Prop) t s) : (term252 A x' t) = ((@INTER A x x') = (@EMPTY A)).
Proof. exact (prop_ext (fun h6 : term252 A x' t => @lem4829745 A x x' t s h1 h6 h3 h4 h5) (fun h6 : (@INTER A x x') = (@EMPTY A) => @lem4829740 A s x' t h2)). Qed.
Lemma lem4829747 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : term249 A s x' t) (h3 : @IN (A -> Prop) x t) (h4 : @IN (A -> Prop) x' s) (h5 : @SUBSET (A -> Prop) t s) : (@INTER A x x') = (@EMPTY A).
Proof. exact (EQ_MP (@lem4829746 A x x' t s h1 h2 h3 h4 h5) (@lem4829740 A s x' t h2)). Qed.
Lemma lem4829748 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : term249 A s x' t) (h3 : @IN (A -> Prop) x t) (h4 : @SUBSET (A -> Prop) t s) : (@IN (A -> Prop) x' s) = ((@INTER A x x') = (@EMPTY A)).
Proof. exact (prop_ext (fun h5 : @IN (A -> Prop) x' s => @lem4829747 A x x' t s h1 h2 h3 h5 h4) (fun h5 : (@INTER A x x') = (@EMPTY A) => @lem4829741 A s x' t h2)). Qed.
Lemma lem4829749 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : term249 A s x' t) (h3 : @IN (A -> Prop) x t) (h4 : @SUBSET (A -> Prop) t s) : (@INTER A x x') = (@EMPTY A).
Proof. exact (EQ_MP (@lem4829748 A x' x t s h1 h2 h3 h4) (@lem4829741 A s x' t h2)). Qed.
Lemma lem4829750 {A : Type'} (x' : A -> Prop) (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : @IN (A -> Prop) x t) (h3 : @SUBSET (A -> Prop) t s) : term454 A s t x x'.
Proof. exact (fun h0 : term249 A s x' t => @lem4829749 A x' x t s h1 h0 h2 h3). Qed.
Lemma lem4829755 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : @IN (A -> Prop) x t) (h3 : @SUBSET (A -> Prop) t s) : term456 A s t x.
Proof. exact (fun x' : A -> Prop => @lem4829750 A x' x t s h1 h2 h3). Qed.
Lemma lem4829756 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : @IN (A -> Prop) x t) (h3 : @SUBSET (A -> Prop) t s) : (@IN (A -> Prop) x t) = (term456 A s t x).
Proof. exact (prop_ext (fun h4 : @IN (A -> Prop) x t => @lem4829755 A x t s h1 h2 h3) (fun h4 : term456 A s t x => @lem4828138 A x t h2)). Qed.
Lemma lem4829757 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : @IN (A -> Prop) x t) (h3 : @SUBSET (A -> Prop) t s) : term456 A s t x.
Proof. exact (EQ_MP (@lem4829756 A x t s h1 h2 h3) (@lem4828138 A x t h2)). Qed.
Lemma lem4829758 {A : Type'} (x : A -> Prop) (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : @SUBSET (A -> Prop) t s) : term457 A s t x.
Proof. exact (fun h0 : @IN (A -> Prop) x t => @lem4829757 A x t s h1 h0 h2). Qed.
Lemma lem4829763 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : @SUBSET (A -> Prop) t s) : term459 A s t.
Proof. exact (fun x : A -> Prop => @lem4829758 A x t s h1 h2). Qed.
Lemma lem4829764 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : @SUBSET (A -> Prop) t s) : (term450 A s) = (term459 A s t).
Proof. exact (prop_ext (fun h3 : term450 A s => @lem4829763 A t s h1 h2) (fun h3 : term459 A s t => @lem4828137 A s h1)). Qed.
Lemma lem4829765 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term450 A s) (h2 : @SUBSET (A -> Prop) t s) : term459 A s t.
Proof. exact (EQ_MP (@lem4829764 A t s h1 h2) (@lem4828137 A s h1)). Qed.
Lemma lem4829766 {A : Type'} (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) : term461 A s t.
Proof. exact (fun h0 : term450 A s => @lem4829765 A t s h0 h1). Qed.
Lemma lem4829767 {A : Type'} (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) : term460 A s t.
Proof. exact (EQ_MP (@lem4828136 A s t) (@lem4829766 A t s h1)). Qed.
Lemma lem4829768 {A : Type'} (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) (h2 : @pairwise (A -> Prop) (@DISJOINT A) s) : term438 A s t.
Proof. exact (@lem4829767 A t s h1 (@lem4828044 A s h2)). Qed.
Lemma lem4829769 {A : Type'} (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) (h2 : @pairwise (A -> Prop) (@DISJOINT A) s) : term331 A s t.
Proof. exact (EQ_MP (@lem4828039 A s t) (@lem4829768 A t s h1 h2)). Qed.
Lemma lem4829770 {A : Type'} (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) (h2 : @pairwise (A -> Prop) (@DISJOINT A) s) : term587 A s t.
Proof. exact (conj (@lem4827832 A t s h1 h2) (@lem4829769 A t s h1 h2)). Qed.
Lemma lem4829771 {A : Type'} (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) (h2 : @pairwise (A -> Prop) (@DISJOINT A) s) : (term588 A s t) = (term214 A s t).
Proof. exact (@lem4826917 A s t (@lem4829770 A t s h1 h2)). Qed.
Lemma lem4829772 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term212 A t s) : @SUBSET (A -> Prop) t s.
Proof. exact (proj2 (@lem4826911 A t s h1)). Qed.
Lemma lem4829773 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term212 A t s) : @pairwise (A -> Prop) (@DISJOINT A) s.
Proof. exact (proj1 (@lem4826911 A t s h1)). Qed.
Lemma lem4829774 {A : Type'} (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) (h2 : @pairwise (A -> Prop) (@DISJOINT A) s) : (@SUBSET (A -> Prop) t s) = ((term588 A s t) = (term214 A s t)).
Proof. exact (prop_ext (fun h3 : @SUBSET (A -> Prop) t s => @lem4829771 A t s h1 h2) (fun h3 : (term588 A s t) = (term214 A s t) => @lem4826912 A t s h1)). Qed.
Lemma lem4829775 {A : Type'} (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) (h2 : @pairwise (A -> Prop) (@DISJOINT A) s) : (term588 A s t) = (term214 A s t).
Proof. exact (EQ_MP (@lem4829774 A t s h1 h2) (@lem4826912 A t s h1)). Qed.
Lemma lem4829776 {A : Type'} (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) (h2 : @pairwise (A -> Prop) (@DISJOINT A) s) : (@pairwise (A -> Prop) (@DISJOINT A) s) = ((term588 A s t) = (term214 A s t)).
Proof. exact (prop_ext (fun h3 : @pairwise (A -> Prop) (@DISJOINT A) s => @lem4829775 A t s h1 h2) (fun h3 : (term588 A s t) = (term214 A s t) => @lem4826913 A s h2)). Qed.
Lemma lem4829777 {A : Type'} (t : type686 A) (s : type686 A) (h1 : @SUBSET (A -> Prop) t s) (h2 : @pairwise (A -> Prop) (@DISJOINT A) s) : (term588 A s t) = (term214 A s t).
Proof. exact (EQ_MP (@lem4829776 A t s h1 h2) (@lem4826913 A s h2)). Qed.
Lemma lem4829778 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term212 A t s) (h2 : @pairwise (A -> Prop) (@DISJOINT A) s) : (@SUBSET (A -> Prop) t s) = ((term588 A s t) = (term214 A s t)).
Proof. exact (prop_ext (fun h3 : @SUBSET (A -> Prop) t s => @lem4829777 A t s h3 h2) (fun h3 : (term588 A s t) = (term214 A s t) => @lem4829772 A t s h1)). Qed.
Lemma lem4829779 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term212 A t s) (h2 : @pairwise (A -> Prop) (@DISJOINT A) s) : (term588 A s t) = (term214 A s t).
Proof. exact (EQ_MP (@lem4829778 A t s h1 h2) (@lem4829772 A t s h1)). Qed.
Lemma lem4829780 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term212 A t s) : (@pairwise (A -> Prop) (@DISJOINT A) s) = ((term588 A s t) = (term214 A s t)).
Proof. exact (prop_ext (fun h2 : @pairwise (A -> Prop) (@DISJOINT A) s => @lem4829779 A t s h1 h2) (fun h2 : (term588 A s t) = (term214 A s t) => @lem4829773 A t s h1)). Qed.
Lemma lem4829781 {A : Type'} (t : type686 A) (s : type686 A) (h1 : term212 A t s) : (term588 A s t) = (term214 A s t).
Proof. exact (EQ_MP (@lem4829780 A t s h1) (@lem4829773 A t s h1)). Qed.
Lemma lem4829782 {A : Type'} (s : type686 A) (t : type686 A) : term589 A s t.
Proof. exact (fun h0 : term212 A t s => @lem4829781 A t s h0). Qed.
Lemma lem4829787 {A : Type'} (s : type686 A) : term590 A s.
Proof. exact (fun t : type686 A => @lem4829782 A s t). Qed.
Lemma lem4829792 {A : Type'} : term591 A.
Proof. exact (fun s : type686 A => @lem4829787 A s). Qed.
