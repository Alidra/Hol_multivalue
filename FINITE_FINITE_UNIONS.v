Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_FINITE_UNIONS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_INDUCT_spec.
Require Import FINITE_RULES_spec.
Require Import FINITE_UNION_spec.
Require Import IN_INSERT_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1856_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3322101_spec.
Require Import thm3322164_spec.
Require Import thm3324017_spec.
Require Import thm3325374_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem3610614 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem3610615 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem3610617 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3606772 A s). Qed.
Lemma lem3610618 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3610619 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3610618 A s) (@lem3610617 A s)). Qed.
Lemma lem3610620 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3610619 A s t). Qed.
Lemma lem3610621 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = ((term3 A s t) = (term4 A s t)).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem3610623 {A : Type'} (x : A) : term5 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3610624 {A : Type'} (x : A) : (term5 A x) = (term6 A x).
Proof. exact (eq_refl (term5 A x)). Qed.
Lemma lem3610625 {A : Type'} (x : A) : term6 A x.
Proof. exact (EQ_MP (@lem3610624 A x) (@lem3610623 A x)). Qed.
Lemma lem3610626 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem3610628 {A : Type'} (x : A) : term8 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3610629 {A : Type'} (x : A) : (term8 A x) = (term9 A x).
Proof. exact (eq_refl (term8 A x)). Qed.
Lemma lem3610630 {A : Type'} (x : A) : term9 A x.
Proof. exact (EQ_MP (@lem3610629 A x) (@lem3610628 A x)). Qed.
Lemma lem3610631 {A : Type'} (x : A) (y : A) : term10 A x y.
Proof. exact (@lem3610630 A x y). Qed.
Lemma lem3610632 {A : Type'} (y : A) (x : A) : (term10 A x y) = (term11 A y x).
Proof. exact (eq_refl (term10 A x y)). Qed.
Lemma lem3610633 {A : Type'} (y : A) (x : A) : term11 A y x.
Proof. exact (EQ_MP (@lem3610632 A y x) (@lem3610631 A x y)). Qed.
Lemma lem3610634 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term12 A y x s.
Proof. exact (@lem3610633 A y x s). Qed.
Lemma lem3610635 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term12 A y x s) = ((term13 A x y s) = (term14 A y x s)).
Proof. exact (eq_refl (term12 A y x s)). Qed.
Lemma lem3610637 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (h1). Qed.
Lemma lem3610638 {A : Type'} (FINITE' : type686 A) (h1 : term15 A) : term16 A FINITE'.
Proof. exact (@lem3610637 A h1 FINITE'). Qed.
Lemma lem3610639 {A : Type'} (FINITE' : type686 A) : (term16 A FINITE') = (term17 A FINITE').
Proof. exact (eq_refl (term16 A FINITE')). Qed.
Lemma lem3610640 {A : Type'} (FINITE' : type686 A) (h1 : term15 A) : term17 A FINITE'.
Proof. exact (EQ_MP (@lem3610639 A FINITE') (@lem3610638 A FINITE' h1)). Qed.
Lemma lem3610641 {A : Type'} (FINITE' : type686 A) (h1 : term18 A FINITE') : term18 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3610642 {A : Type'} (FINITE' : type686 A) (h1 : term15 A) (h2 : term18 A FINITE') : term19 A FINITE'.
Proof. exact (@lem3610640 A FINITE' h1 (@lem3610641 A FINITE' h2)). Qed.
Lemma lem3610643 {A : Type'} (FINITE' : type686 A) (h1 : term18 A FINITE') : term20 A FINITE'.
Proof. exact (fun h0 : term15 A => @lem3610642 A FINITE' h0 h1). Qed.
Lemma lem3610644 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (h1). Qed.
Lemma lem3610645 {A : Type'} (FINITE' : type686 A) (h1 : term15 A) (h2 : term18 A FINITE') : term19 A FINITE'.
Proof. exact (@lem3610643 A FINITE' h2 (@lem3610644 A h1)). Qed.
Lemma lem3610646 {A : Type'} (FINITE' : type686 A) (h1 : term15 A) : term17 A FINITE'.
Proof. exact (fun h0 : term18 A FINITE' => @lem3610645 A FINITE' h1 h0). Qed.
Lemma lem3610647 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (fun FINITE' : type686 A => @lem3610646 A FINITE' h1). Qed.
Lemma lem3610648 {A : Type'} : term21 A.
Proof. exact (fun h0 : term15 A => @lem3610647 A h0). Qed.
Lemma lem3610649 {A : Type'} : term15 A.
Proof. exact (@lem3610648 A (@lem3197567 A)). Qed.
Lemma lem3610650 {A : Type'} (FINITE' : type686 A) : term16 A FINITE'.
Proof. exact (@lem3610649 A FINITE'). Qed.
Lemma lem3610651 {A : Type'} (FINITE' : type686 A) : (term16 A FINITE') = (term17 A FINITE').
Proof. exact (eq_refl (term16 A FINITE')). Qed.
Lemma lem3610654 {A : Type'} (FINITE' : type686 A) : term17 A FINITE'.
Proof. exact (EQ_MP (@lem3610651 A FINITE') (@lem3610650 A FINITE')). Qed.
Lemma lem3610655 {_92445 : Type'} (FINITE' : type180 _92445) : term22 _92445 FINITE'.
Proof. exact (@lem3610654 (_92445 -> Prop) FINITE'). Qed.
Lemma lem3610656 {_92445 : Type'} : term23 _92445.
Proof. exact (@lem3610655 _92445 (term24 _92445)). Qed.
Lemma lem3610657 {_92445 : Type'} : (term25 _92445) = ((term26 _92445) = (term27 _92445)).
Proof. exact (eq_refl (term25 _92445)). Qed.
Lemma lem3610658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3610659 {_92445 : Type'} : (term28 _92445) = (term29 _92445).
Proof. exact (MK_COMB (@lem3610658) (@lem3610657 _92445)). Qed.
Lemma lem3610660 {_92445 : Type'} (s : type686 _92445) : (term30 _92445 s) = ((term31 _92445 s) = (term32 _92445 s)).
Proof. exact (eq_refl (term30 _92445 s)). Qed.
Lemma lem3610661 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3610662 {_92445 : Type'} (s : type686 _92445) : (term33 _92445 s) = (term34 _92445 s).
Proof. exact (MK_COMB (@lem3610661) (@lem3610660 _92445 s)). Qed.
Lemma lem3610663 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term35 _92445 x s) = ((term36 _92445 x s) = (term37 _92445 x s)).
Proof. exact (eq_refl (term35 _92445 x s)). Qed.
Lemma lem3610664 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term38 _92445 x s) = (term39 _92445 x s).
Proof. exact (MK_COMB (@lem3610662 _92445 s) (@lem3610663 _92445 x s)). Qed.
Lemma lem3610665 {_92445 : Type'} (x : _92445 -> Prop) : (term40 _92445 x) = (term41 _92445 x).
Proof. exact (fun_ext (fun s : type686 _92445 => @lem3610664 _92445 x s)). Qed.
Lemma lem3610666 {_92445 : Type'} : (@all ((_92445 -> Prop) -> Prop)) = (@all ((_92445 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_92445 -> Prop) -> Prop))). Qed.
Lemma lem3610667 {_92445 : Type'} (x : _92445 -> Prop) : (term42 _92445 x) = (term43 _92445 x).
Proof. exact (MK_COMB (@lem3610666 _92445) (@lem3610665 _92445 x)). Qed.
Lemma lem3610668 {_92445 : Type'} : (term44 _92445) = (term45 _92445).
Proof. exact (fun_ext (fun x : _92445 -> Prop => @lem3610667 _92445 x)). Qed.
Lemma lem3610669 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3610670 {_92445 : Type'} : (term46 _92445) = (term47 _92445).
Proof. exact (MK_COMB (@lem3610669 _92445) (@lem3610668 _92445)). Qed.
Lemma lem3610671 {_92445 : Type'} : (term48 _92445) = (term49 _92445).
Proof. exact (MK_COMB (@lem3610659 _92445) (@lem3610670 _92445)). Qed.
Lemma lem3610672 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3610673 {_92445 : Type'} : (term50 _92445) = (term51 _92445).
Proof. exact (MK_COMB (@lem3610672) (@lem3610671 _92445)). Qed.
Lemma lem3610674 {_92445 : Type'} (s : type686 _92445) : (term30 _92445 s) = ((term31 _92445 s) = (term32 _92445 s)).
Proof. exact (eq_refl (term30 _92445 s)). Qed.
Lemma lem3610675 {_92445 : Type'} (s : type686 _92445) : (term52 _92445 s) = (term52 _92445 s).
Proof. exact (eq_refl (term52 _92445 s)). Qed.
Lemma lem3610676 {_92445 : Type'} (s : type686 _92445) : (term53 _92445 s) = (term54 _92445 s).
Proof. exact (MK_COMB (@lem3610675 _92445 s) (@lem3610674 _92445 s)). Qed.
Lemma lem3610677 {_92445 : Type'} : (term55 _92445) = (term56 _92445).
Proof. exact (fun_ext (fun s : type686 _92445 => @lem3610676 _92445 s)). Qed.
Lemma lem3610678 {_92445 : Type'} : (@all ((_92445 -> Prop) -> Prop)) = (@all ((_92445 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_92445 -> Prop) -> Prop))). Qed.
Lemma lem3610679 {_92445 : Type'} : (term57 _92445) = (term58 _92445).
Proof. exact (MK_COMB (@lem3610678 _92445) (@lem3610677 _92445)). Qed.
Lemma lem3610680 {_92445 : Type'} : (term23 _92445) = (term59 _92445).
Proof. exact (MK_COMB (@lem3610673 _92445) (@lem3610679 _92445)). Qed.
Lemma lem3610681 {_92445 : Type'} : term59 _92445.
Proof. exact (EQ_MP (@lem3610680 _92445) (@lem3610656 _92445)). Qed.
Lemma lem3610687 {_86801 : Type'} : (@UNIONS _86801 (@EMPTY (_86801 -> Prop))) = (@EMPTY _86801).
Proof. exact (EQ_MP (@lem3322101 _86801) (@lem3322164 _86801)). Qed.
Lemma lem3610688 {_92445 : Type'} : (@UNIONS _92445 (@EMPTY (_92445 -> Prop))) = (@EMPTY _92445).
Proof. exact (@lem3610687 _92445). Qed.
Lemma lem3610689 {_92445 : Type'} : (@FINITE _92445) = (@FINITE _92445).
Proof. exact (eq_refl (@FINITE _92445)). Qed.
Lemma lem3610690 {_92445 : Type'} : (term26 _92445) = (@FINITE _92445 (@EMPTY _92445)).
Proof. exact (MK_COMB (@lem3610689 _92445) (@lem3610688 _92445)). Qed.
Lemma lem3610691 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3610692 {_92445 : Type'} : (term60 _92445) = (term61 _92445).
Proof. exact (MK_COMB (@lem3610691) (@lem3610690 _92445)). Qed.
Lemma lem3610700 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3610626 A x (@lem3610625 A x)). Qed.
Lemma lem3610701 {_92445 : Type'} (x : _92445 -> Prop) : (@IN (_92445 -> Prop) x (@EMPTY (_92445 -> Prop))) = False.
Proof. exact (@lem3610700 (_92445 -> Prop) x). Qed.
Lemma lem3610702 {_92445 : Type'} (t : _92445 -> Prop) : (@IN (_92445 -> Prop) t (@EMPTY (_92445 -> Prop))) = False.
Proof. exact (@lem3610701 _92445 t). Qed.
Lemma lem3610703 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3610704 {_92445 : Type'} (t : _92445 -> Prop) : (term62 _92445 t) = (imp False).
Proof. exact (MK_COMB (@lem3610703) (@lem3610702 _92445 t)). Qed.
Lemma lem3610705 {_92445 : Type'} (t : _92445 -> Prop) : (@FINITE _92445 t) = (@FINITE _92445 t).
Proof. exact (eq_refl (@FINITE _92445 t)). Qed.
Lemma lem3610706 {_92445 : Type'} (t : _92445 -> Prop) : (term63 _92445 t) = (term64 _92445 t).
Proof. exact (MK_COMB (@lem3610704 _92445 t) (@lem3610705 _92445 t)). Qed.
Lemma lem3610708 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3610709 {_92445 : Type'} (t : _92445 -> Prop) : (term64 _92445 t) = True.
Proof. exact (@lem3610708 (@FINITE _92445 t)). Qed.
Lemma lem3610710 {_92445 : Type'} (t : _92445 -> Prop) : (term63 _92445 t) = True.
Proof. exact (TRANS (@lem3610706 _92445 t) (@lem3610709 _92445 t)). Qed.
Lemma lem3610711 {_92445 : Type'} : (term65 _92445) = (term66 _92445).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3610710 _92445 t)). Qed.
Lemma lem3610712 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3610713 {_92445 : Type'} : (term27 _92445) = (term67 _92445).
Proof. exact (MK_COMB (@lem3610712 _92445) (@lem3610711 _92445)). Qed.
Lemma lem3610715 {A : Type'} (t : Prop) : (term68 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3610716 {_92445 : Type'} (t : Prop) : (term69 _92445 t) = t.
Proof. exact (@lem3610715 (_92445 -> Prop) t). Qed.
Lemma lem3610717 {_92445 : Type'} : (term67 _92445) = True.
Proof. exact (@lem3610716 _92445 True). Qed.
Lemma lem3610718 {_92445 : Type'} : (term27 _92445) = True.
Proof. exact (TRANS (@lem3610713 _92445) (@lem3610717 _92445)). Qed.
Lemma lem3610719 {_92445 : Type'} : ((term26 _92445) = (term27 _92445)) = ((@FINITE _92445 (@EMPTY _92445)) = True).
Proof. exact (MK_COMB (@lem3610692 _92445) (@lem3610718 _92445)). Qed.
Lemma lem3610721 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem3610722 {_92445 : Type'} : ((@FINITE _92445 (@EMPTY _92445)) = True) = (@FINITE _92445 (@EMPTY _92445)).
Proof. exact (@lem3610721 (@FINITE _92445 (@EMPTY _92445))). Qed.
Lemma lem3610723 {_92445 : Type'} : ((term26 _92445) = (term27 _92445)) = (@FINITE _92445 (@EMPTY _92445)).
Proof. exact (TRANS (@lem3610719 _92445) (@lem3610722 _92445)). Qed.
Lemma lem3610724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3610725 {_92445 : Type'} : (term29 _92445) = (term70 _92445).
Proof. exact (MK_COMB (@lem3610724) (@lem3610723 _92445)). Qed.
Lemma lem3610749 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term71 _86841 s u) = (term72 _86841 s u).
Proof. exact (EQ_MP (@lem3324017 _86841 s u) (@lem3325374 _86841 s u)). Qed.
Lemma lem3610750 {_92445 : Type'} (s : _92445 -> Prop) (u : type686 _92445) : (term71 _92445 s u) = (term72 _92445 s u).
Proof. exact (@lem3610749 _92445 s u). Qed.
Lemma lem3610751 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term71 _92445 x s) = (term72 _92445 x s).
Proof. exact (@lem3610750 _92445 x s). Qed.
Lemma lem3610752 {_92445 : Type'} : (@FINITE _92445) = (@FINITE _92445).
Proof. exact (eq_refl (@FINITE _92445)). Qed.
Lemma lem3610753 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term36 _92445 x s) = (term73 _92445 x s).
Proof. exact (MK_COMB (@lem3610752 _92445) (@lem3610751 _92445 x s)). Qed.
Lemma lem3610754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3610755 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term74 _92445 x s) = (term75 _92445 x s).
Proof. exact (MK_COMB (@lem3610754) (@lem3610753 _92445 x s)). Qed.
Lemma lem3610763 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term13 A x y s) = (term14 A y x s).
Proof. exact (EQ_MP (@lem3610635 A y x s) (@lem3610634 A y x s)). Qed.
Lemma lem3610764 {_92445 : Type'} (y : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) : (term76 _92445 x y s) = (term77 _92445 y x s).
Proof. exact (@lem3610763 (_92445 -> Prop) y x s). Qed.
Lemma lem3610765 {_92445 : Type'} (x : _92445 -> Prop) (t : _92445 -> Prop) (s : type686 _92445) : (term76 _92445 t x s) = (term77 _92445 x t s).
Proof. exact (@lem3610764 _92445 x t s). Qed.
Lemma lem3610770 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3610771 {_92445 : Type'} (x : _92445 -> Prop) (t : _92445 -> Prop) (s : type686 _92445) : (term78 _92445 t x s) = (term79 _92445 x t s).
Proof. exact (MK_COMB (@lem3610770) (@lem3610765 _92445 x t s)). Qed.
Lemma lem3610772 {_92445 : Type'} (t : _92445 -> Prop) : (@FINITE _92445 t) = (@FINITE _92445 t).
Proof. exact (eq_refl (@FINITE _92445 t)). Qed.
Lemma lem3610773 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term80 _92445 x s t) = (term81 _92445 x s t).
Proof. exact (MK_COMB (@lem3610771 _92445 x t s) (@lem3610772 _92445 t)). Qed.
Lemma lem3610776 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term82 _92445 x s) = (term83 _92445 x s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3610773 _92445 x s t)). Qed.
Lemma lem3610777 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3610778 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term37 _92445 x s) = (term84 _92445 x s).
Proof. exact (MK_COMB (@lem3610777 _92445) (@lem3610776 _92445 x s)). Qed.
Lemma lem3610783 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : ((term36 _92445 x s) = (term37 _92445 x s)) = ((term73 _92445 x s) = (term84 _92445 x s)).
Proof. exact (MK_COMB (@lem3610755 _92445 x s) (@lem3610778 _92445 x s)). Qed.
Lemma lem3610786 {_92445 : Type'} (s : type686 _92445) : (term34 _92445 s) = (term34 _92445 s).
Proof. exact (eq_refl (term34 _92445 s)). Qed.
Lemma lem3610787 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term39 _92445 x s) = (term85 _92445 x s).
Proof. exact (MK_COMB (@lem3610786 _92445 s) (@lem3610783 _92445 x s)). Qed.
Lemma lem3610792 {_92445 : Type'} (x : _92445 -> Prop) : (term41 _92445 x) = (term86 _92445 x).
Proof. exact (fun_ext (fun s : type686 _92445 => @lem3610787 _92445 x s)). Qed.
Lemma lem3610793 {_92445 : Type'} : (@all ((_92445 -> Prop) -> Prop)) = (@all ((_92445 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_92445 -> Prop) -> Prop))). Qed.
Lemma lem3610794 {_92445 : Type'} (x : _92445 -> Prop) : (term43 _92445 x) = (term87 _92445 x).
Proof. exact (MK_COMB (@lem3610793 _92445) (@lem3610792 _92445 x)). Qed.
Lemma lem3610799 {_92445 : Type'} : (term45 _92445) = (term88 _92445).
Proof. exact (fun_ext (fun x : _92445 -> Prop => @lem3610794 _92445 x)). Qed.
Lemma lem3610800 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3610801 {_92445 : Type'} : (term47 _92445) = (term89 _92445).
Proof. exact (MK_COMB (@lem3610800 _92445) (@lem3610799 _92445)). Qed.
Lemma lem3610806 {_92445 : Type'} : (term49 _92445) = (term90 _92445).
Proof. exact (MK_COMB (@lem3610725 _92445) (@lem3610801 _92445)). Qed.
Lemma lem3610809 {_92445 : Type'} : (term90 _92445) = (term49 _92445).
Proof. exact (SYM (@lem3610806 _92445)). Qed.
Lemma lem3610813 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem3610615 A) (@lem3610614 A)). Qed.
Lemma lem3610814 {_92445 : Type'} : (@FINITE _92445 (@EMPTY _92445)) = True.
Proof. exact (@lem3610813 _92445). Qed.
Lemma lem3610815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3610816 {_92445 : Type'} : (term70 _92445) = (and True).
Proof. exact (MK_COMB (@lem3610815) (@lem3610814 _92445)). Qed.
Lemma lem3610840 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term3 A s t) = (term4 A s t).
Proof. exact (EQ_MP (@lem3610621 A s t) (@lem3610620 A s t)). Qed.
Lemma lem3610841 {_92445 : Type'} (s : _92445 -> Prop) (t : _92445 -> Prop) : (term3 _92445 s t) = (term4 _92445 s t).
Proof. exact (@lem3610840 _92445 s t). Qed.
Lemma lem3610842 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term73 _92445 x s) = (term91 _92445 x s).
Proof. exact (@lem3610841 _92445 x (@UNIONS _92445 s)). Qed.
Lemma lem3610845 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3610846 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term75 _92445 x s) = (term92 _92445 x s).
Proof. exact (MK_COMB (@lem3610845) (@lem3610842 _92445 x s)). Qed.
Lemma lem3610857 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term84 _92445 x s) = (term84 _92445 x s).
Proof. exact (eq_refl (term84 _92445 x s)). Qed.
Lemma lem3610858 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : ((term73 _92445 x s) = (term84 _92445 x s)) = ((term91 _92445 x s) = (term84 _92445 x s)).
Proof. exact (MK_COMB (@lem3610846 _92445 x s) (@lem3610857 _92445 x s)). Qed.
Lemma lem3610861 {_92445 : Type'} (s : type686 _92445) : (term34 _92445 s) = (term34 _92445 s).
Proof. exact (eq_refl (term34 _92445 s)). Qed.
Lemma lem3610862 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term85 _92445 x s) = (term93 _92445 x s).
Proof. exact (MK_COMB (@lem3610861 _92445 s) (@lem3610858 _92445 x s)). Qed.
Lemma lem3610867 {_92445 : Type'} (x : _92445 -> Prop) : (term86 _92445 x) = (term94 _92445 x).
Proof. exact (fun_ext (fun s : type686 _92445 => @lem3610862 _92445 x s)). Qed.
Lemma lem3610868 {_92445 : Type'} : (@all ((_92445 -> Prop) -> Prop)) = (@all ((_92445 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_92445 -> Prop) -> Prop))). Qed.
Lemma lem3610869 {_92445 : Type'} (x : _92445 -> Prop) : (term87 _92445 x) = (term95 _92445 x).
Proof. exact (MK_COMB (@lem3610868 _92445) (@lem3610867 _92445 x)). Qed.
Lemma lem3610874 {_92445 : Type'} : (term88 _92445) = (term96 _92445).
Proof. exact (fun_ext (fun x : _92445 -> Prop => @lem3610869 _92445 x)). Qed.
Lemma lem3610875 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3610876 {_92445 : Type'} : (term89 _92445) = (term97 _92445).
Proof. exact (MK_COMB (@lem3610875 _92445) (@lem3610874 _92445)). Qed.
Lemma lem3610881 {_92445 : Type'} : (term90 _92445) = (term98 _92445).
Proof. exact (MK_COMB (@lem3610816 _92445) (@lem3610876 _92445)). Qed.
Lemma lem3610883 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3610884 {_92445 : Type'} : (term98 _92445) = (term97 _92445).
Proof. exact (@lem3610883 (term97 _92445)). Qed.
Lemma lem3610919 {_92445 : Type'} : (term90 _92445) = (term97 _92445).
Proof. exact (TRANS (@lem3610881 _92445) (@lem3610884 _92445)). Qed.
Lemma lem3610920 {_92445 : Type'} : (term97 _92445) = (term90 _92445).
Proof. exact (SYM (@lem3610919 _92445)). Qed.
Lemma lem3610922 (p : Prop) : p = (term99 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3610923 {_92445 : Type'} : (term97 _92445) = (term100 _92445).
Proof. exact (@lem3610922 (term97 _92445)). Qed.
Lemma lem3610924 {_92445 : Type'} : (term100 _92445) = (term97 _92445).
Proof. exact (SYM (@lem3610923 _92445)). Qed.
Lemma lem3610925 {_92445 : Type'} (h1 : term101 _92445) : term101 _92445.
Proof. exact (h1). Qed.
Lemma lem3610928 {_92445 : Type'} (h1 : term100 _92445) : term100 _92445.
Proof. exact (h1). Qed.
Lemma lem3610929 {_92445 : Type'} : term102 _92445.
Proof. exact (fun h0 : term100 _92445 => @lem3610928 _92445 h0). Qed.
Lemma lem3610930 {_92445 : Type'} (h1 : term102 _92445) : term102 _92445.
Proof. exact (h1). Qed.
Lemma lem3610931 {_92445 : Type'} (h1 : term100 _92445) : term100 _92445.
Proof. exact (h1). Qed.
Lemma lem3610932 {_92445 : Type'} (h1 : term100 _92445) (h2 : term102 _92445) : term100 _92445.
Proof. exact (@lem3610930 _92445 h2 (@lem3610931 _92445 h1)). Qed.
Lemma lem3610933 {_92445 : Type'} (h1 : term100 _92445) : term103 _92445.
Proof. exact (fun h0 : term102 _92445 => @lem3610932 _92445 h1 h0). Qed.
Lemma lem3610934 {_92445 : Type'} (h1 : term102 _92445) : term102 _92445.
Proof. exact (h1). Qed.
Lemma lem3610935 {_92445 : Type'} (h1 : term100 _92445) (h2 : term102 _92445) : term100 _92445.
Proof. exact (@lem3610933 _92445 h1 (@lem3610934 _92445 h2)). Qed.
Lemma lem3610936 {_92445 : Type'} (h1 : term102 _92445) : term102 _92445.
Proof. exact (fun h0 : term100 _92445 => @lem3610935 _92445 h0 h1). Qed.
Lemma lem3610937 {_92445 : Type'} : term104 _92445.
Proof. exact (fun h0 : term102 _92445 => @lem3610936 _92445 h0). Qed.
Lemma lem3610940 {_92445 : Type'} : term102 _92445.
Proof. exact (@lem3610937 _92445 (@lem3610929 _92445)). Qed.
Lemma lem3610941 {_92445 : Type'} : term102 _92445.
Proof. exact (@lem3610940 _92445). Qed.
Lemma lem3610943 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3610944 {_92445 : Type'} : (term100 _92445) = (term105 _92445).
Proof. exact (@lem3610943 (term101 _92445)). Qed.
Lemma lem3610946 (t : Prop) : (term106 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3610947 {_92445 : Type'} : (term105 _92445) = (term97 _92445).
Proof. exact (@lem3610946 (term97 _92445)). Qed.
Lemma lem3610978 {_92445 : Type'} : (term100 _92445) = (term97 _92445).
Proof. exact (TRANS (@lem3610944 _92445) (@lem3610947 _92445)). Qed.
Lemma lem3610987 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term81 _92445 x s t) = (term81 _92445 x s t).
Proof. exact (eq_refl (term81 _92445 x s t)). Qed.
Lemma lem3610988 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term83 _92445 x s) = (term83 _92445 x s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3610987 _92445 x s t)). Qed.
Lemma lem3610989 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3610990 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term84 _92445 x s) = (term84 _92445 x s).
Proof. exact (MK_COMB (@lem3610989 _92445) (@lem3610988 _92445 x s)). Qed.
Lemma lem3610997 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term92 _92445 x s) = (term92 _92445 x s).
Proof. exact (eq_refl (term92 _92445 x s)). Qed.
Lemma lem3610998 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : ((term91 _92445 x s) = (term84 _92445 x s)) = ((term91 _92445 x s) = (term84 _92445 x s)).
Proof. exact (MK_COMB (@lem3610997 _92445 x s) (@lem3610990 _92445 x s)). Qed.
Lemma lem3611003 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) : (term107 _92445 s t) = (term107 _92445 s t).
Proof. exact (eq_refl (term107 _92445 s t)). Qed.
Lemma lem3611004 {_92445 : Type'} (s : type686 _92445) : (term108 _92445 s) = (term108 _92445 s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611003 _92445 s t)). Qed.
Lemma lem3611005 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3611006 {_92445 : Type'} (s : type686 _92445) : (term32 _92445 s) = (term32 _92445 s).
Proof. exact (MK_COMB (@lem3611005 _92445) (@lem3611004 _92445 s)). Qed.
Lemma lem3611009 {_92445 : Type'} (s : type686 _92445) : (term109 _92445 s) = (term109 _92445 s).
Proof. exact (eq_refl (term109 _92445 s)). Qed.
Lemma lem3611010 {_92445 : Type'} (s : type686 _92445) : ((term31 _92445 s) = (term32 _92445 s)) = ((term31 _92445 s) = (term32 _92445 s)).
Proof. exact (MK_COMB (@lem3611009 _92445 s) (@lem3611006 _92445 s)). Qed.
Lemma lem3611011 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3611012 {_92445 : Type'} (s : type686 _92445) : (term34 _92445 s) = (term34 _92445 s).
Proof. exact (MK_COMB (@lem3611011) (@lem3611010 _92445 s)). Qed.
Lemma lem3611013 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term93 _92445 x s) = (term93 _92445 x s).
Proof. exact (MK_COMB (@lem3611012 _92445 s) (@lem3610998 _92445 x s)). Qed.
Lemma lem3611014 {_92445 : Type'} (x : _92445 -> Prop) : (term94 _92445 x) = (term94 _92445 x).
Proof. exact (fun_ext (fun s : type686 _92445 => @lem3611013 _92445 x s)). Qed.
Lemma lem3611015 {_92445 : Type'} : (@all ((_92445 -> Prop) -> Prop)) = (@all ((_92445 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_92445 -> Prop) -> Prop))). Qed.
Lemma lem3611016 {_92445 : Type'} (x : _92445 -> Prop) : (term95 _92445 x) = (term95 _92445 x).
Proof. exact (MK_COMB (@lem3611015 _92445) (@lem3611014 _92445 x)). Qed.
Lemma lem3611017 {_92445 : Type'} : (term96 _92445) = (term96 _92445).
Proof. exact (fun_ext (fun x : _92445 -> Prop => @lem3611016 _92445 x)). Qed.
Lemma lem3611018 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3611019 {_92445 : Type'} : (term97 _92445) = (term97 _92445).
Proof. exact (MK_COMB (@lem3611018 _92445) (@lem3611017 _92445)). Qed.
Lemma lem3611056 {_92445 : Type'} : (term100 _92445) = (term97 _92445).
Proof. exact (TRANS (@lem3610978 _92445) (@lem3611019 _92445)). Qed.
Lemma lem3611057 {_92445 : Type'} : (term97 _92445) = (term100 _92445).
Proof. exact (SYM (@lem3611056 _92445)). Qed.
Lemma lem3611058 {_92445 : Type'} (s : type686 _92445) (h1 : (term31 _92445 s) = (term32 _92445 s)) : (term31 _92445 s) = (term32 _92445 s).
Proof. exact (h1). Qed.
Lemma lem3611060 (p : Prop) : p = (term99 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3611061 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : ((term91 _92445 x s) = (term84 _92445 x s)) = (term110 _92445 x s).
Proof. exact (@lem3611060 ((term91 _92445 x s) = (term84 _92445 x s))). Qed.
Lemma lem3611062 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term110 _92445 x s) = ((term91 _92445 x s) = (term84 _92445 x s)).
Proof. exact (SYM (@lem3611061 _92445 x s)). Qed.
Lemma lem3611063 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term111 _92445 x s) : term111 _92445 x s.
Proof. exact (h1). Qed.
Lemma lem3611074 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) : (term112 _92445 s t) = (term113 _92445 s t).
Proof. exact (@lem17362 (@IN (_92445 -> Prop) t s) (@FINITE _92445 t)). Qed.
Lemma lem3611079 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) : (term107 _92445 s t) = (term114 _92445 s t).
Proof. exact (@lem17265 (@IN (_92445 -> Prop) t s) (@FINITE _92445 t)). Qed.
Lemma lem3611080 {_92445 : Type'} (P : type686 _92445) : (term115 _92445 P) = (term116 _92445 P).
Proof. exact (@lem18392 (_92445 -> Prop) P). Qed.
Lemma lem3611081 {_92445 : Type'} (s : type686 _92445) : (term117 _92445 s) = (term118 _92445 s).
Proof. exact (@lem3611080 _92445 (term108 _92445 s)). Qed.
Lemma lem3611082 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) : (term119 _92445 s t) = (term107 _92445 s t).
Proof. exact (eq_refl (term119 _92445 s t)). Qed.
Lemma lem3611083 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3611084 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) : (term120 _92445 s t) = (term112 _92445 s t).
Proof. exact (MK_COMB (@lem3611083) (@lem3611082 _92445 s t)). Qed.
Lemma lem3611085 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) : (term120 _92445 s t) = (term113 _92445 s t).
Proof. exact (TRANS (@lem3611084 _92445 s t) (@lem3611074 _92445 s t)). Qed.
Lemma lem3611086 {_92445 : Type'} (s : type686 _92445) : (term121 _92445 s) = (term122 _92445 s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611085 _92445 s t)). Qed.
Lemma lem3611087 {_92445 : Type'} : (@ex (_92445 -> Prop)) = (@ex (_92445 -> Prop)).
Proof. exact (eq_refl (@ex (_92445 -> Prop))). Qed.
Lemma lem3611088 {_92445 : Type'} (s : type686 _92445) : (term118 _92445 s) = (term123 _92445 s).
Proof. exact (MK_COMB (@lem3611087 _92445) (@lem3611086 _92445 s)). Qed.
Lemma lem3611089 {_92445 : Type'} (s : type686 _92445) : (term117 _92445 s) = (term123 _92445 s).
Proof. exact (TRANS (@lem3611081 _92445 s) (@lem3611088 _92445 s)). Qed.
Lemma lem3611090 {_92445 : Type'} (s : type686 _92445) : (term108 _92445 s) = (term124 _92445 s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611079 _92445 s t)). Qed.
Lemma lem3611091 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3611092 {_92445 : Type'} (s : type686 _92445) : (term32 _92445 s) = (term125 _92445 s).
Proof. exact (MK_COMB (@lem3611091 _92445) (@lem3611090 _92445 s)). Qed.
Lemma lem3611094 {_92445 : Type'} (s : type686 _92445) : (term126 _92445 s) = (term126 _92445 s).
Proof. exact (eq_refl (term126 _92445 s)). Qed.
Lemma lem3611095 {_92445 : Type'} (s : type686 _92445) : (term127 _92445 s) = (term128 _92445 s).
Proof. exact (MK_COMB (@lem3611094 _92445 s) (@lem3611089 _92445 s)). Qed.
Lemma lem3611097 {_92445 : Type'} (s : type686 _92445) : (term129 _92445 s) = (term129 _92445 s).
Proof. exact (eq_refl (term129 _92445 s)). Qed.
Lemma lem3611098 {_92445 : Type'} (s : type686 _92445) : (term130 _92445 s) = (term131 _92445 s).
Proof. exact (MK_COMB (@lem3611097 _92445 s) (@lem3611092 _92445 s)). Qed.
Lemma lem3611099 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3611100 {_92445 : Type'} (s : type686 _92445) : (term132 _92445 s) = (term133 _92445 s).
Proof. exact (MK_COMB (@lem3611099) (@lem3611098 _92445 s)). Qed.
Lemma lem3611101 {_92445 : Type'} (s : type686 _92445) : (term134 _92445 s) = (term135 _92445 s).
Proof. exact (MK_COMB (@lem3611100 _92445 s) (@lem3611095 _92445 s)). Qed.
Lemma lem3611102 {_92445 : Type'} (s : type686 _92445) : ((term31 _92445 s) = (term32 _92445 s)) = (term134 _92445 s).
Proof. exact (@lem17500 (term31 _92445 s) (term32 _92445 s)). Qed.
Lemma lem3611103 {_92445 : Type'} (s : type686 _92445) : ((term31 _92445 s) = (term32 _92445 s)) = (term135 _92445 s).
Proof. exact (TRANS (@lem3611102 _92445 s) (@lem3611101 _92445 s)). Qed.
Lemma lem3611186 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3611187 {_92445 : Type'} (P : Prop) (Q : type686 _92445) : (term138 _92445 P Q) = (term139 _92445 P Q).
Proof. exact (@lem3611186 (_92445 -> Prop) P Q). Qed.
Lemma lem3611188 {_92445 : Type'} (s : type686 _92445) : (term140 _92445 s) = (term141 _92445 s).
Proof. exact (@lem3611187 _92445 (term142 _92445 s) (term122 _92445 s)). Qed.
Lemma lem3611189 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) : (term143 _92445 s t) = (term113 _92445 s t).
Proof. exact (eq_refl (term143 _92445 s t)). Qed.
Lemma lem3611190 {_92445 : Type'} (s : type686 _92445) : (term144 _92445 s) = (term122 _92445 s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611189 _92445 s t)). Qed.
Lemma lem3611191 {_92445 : Type'} : (@ex (_92445 -> Prop)) = (@ex (_92445 -> Prop)).
Proof. exact (eq_refl (@ex (_92445 -> Prop))). Qed.
Lemma lem3611192 {_92445 : Type'} (s : type686 _92445) : (term145 _92445 s) = (term123 _92445 s).
Proof. exact (MK_COMB (@lem3611191 _92445) (@lem3611190 _92445 s)). Qed.
Lemma lem3611193 {_92445 : Type'} (s : type686 _92445) : (term126 _92445 s) = (term126 _92445 s).
Proof. exact (eq_refl (term126 _92445 s)). Qed.
Lemma lem3611194 {_92445 : Type'} (s : type686 _92445) : (term140 _92445 s) = (term128 _92445 s).
Proof. exact (MK_COMB (@lem3611193 _92445 s) (@lem3611192 _92445 s)). Qed.
Lemma lem3611195 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3611196 {_92445 : Type'} (s : type686 _92445) : (term146 _92445 s) = (term147 _92445 s).
Proof. exact (MK_COMB (@lem3611195) (@lem3611194 _92445 s)). Qed.
Lemma lem3611197 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) : (term143 _92445 s t) = (term113 _92445 s t).
Proof. exact (eq_refl (term143 _92445 s t)). Qed.
Lemma lem3611198 {_92445 : Type'} (s : type686 _92445) : (term126 _92445 s) = (term126 _92445 s).
Proof. exact (eq_refl (term126 _92445 s)). Qed.
Lemma lem3611199 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) : (term148 _92445 s t) = (term149 _92445 s t).
Proof. exact (MK_COMB (@lem3611198 _92445 s) (@lem3611197 _92445 s t)). Qed.
Lemma lem3611200 {_92445 : Type'} (s : type686 _92445) : (term150 _92445 s) = (term151 _92445 s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611199 _92445 s t)). Qed.
Lemma lem3611201 {_92445 : Type'} : (@ex (_92445 -> Prop)) = (@ex (_92445 -> Prop)).
Proof. exact (eq_refl (@ex (_92445 -> Prop))). Qed.
Lemma lem3611202 {_92445 : Type'} (s : type686 _92445) : (term141 _92445 s) = (term152 _92445 s).
Proof. exact (MK_COMB (@lem3611201 _92445) (@lem3611200 _92445 s)). Qed.
Lemma lem3611203 {_92445 : Type'} (s : type686 _92445) : ((term140 _92445 s) = (term141 _92445 s)) = ((term128 _92445 s) = (term152 _92445 s)).
Proof. exact (MK_COMB (@lem3611196 _92445 s) (@lem3611202 _92445 s)). Qed.
Lemma lem3611204 {_92445 : Type'} (s : type686 _92445) : (term128 _92445 s) = (term152 _92445 s).
Proof. exact (EQ_MP (@lem3611203 _92445 s) (@lem3611188 _92445 s)). Qed.
Lemma lem3611205 {_92445 : Type'} (s : type686 _92445) : (term133 _92445 s) = (term133 _92445 s).
Proof. exact (eq_refl (term133 _92445 s)). Qed.
Lemma lem3611206 {_92445 : Type'} (s : type686 _92445) : (term135 _92445 s) = (term153 _92445 s).
Proof. exact (MK_COMB (@lem3611205 _92445 s) (@lem3611204 _92445 s)). Qed.
Lemma lem3611208 {A : Type'} (P : Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3611209 {_92445 : Type'} (P : Prop) (Q : type686 _92445) : (term156 _92445 P Q) = (term157 _92445 P Q).
Proof. exact (@lem3611208 (_92445 -> Prop) P Q). Qed.
Lemma lem3611210 {_92445 : Type'} (s : type686 _92445) : (term158 _92445 s) = (term159 _92445 s).
Proof. exact (@lem3611209 _92445 (term131 _92445 s) (term151 _92445 s)). Qed.
Lemma lem3611211 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) : (term160 _92445 s t) = (term149 _92445 s t).
Proof. exact (eq_refl (term160 _92445 s t)). Qed.
Lemma lem3611212 {_92445 : Type'} (s : type686 _92445) : (term161 _92445 s) = (term151 _92445 s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611211 _92445 s t)). Qed.
Lemma lem3611213 {_92445 : Type'} : (@ex (_92445 -> Prop)) = (@ex (_92445 -> Prop)).
Proof. exact (eq_refl (@ex (_92445 -> Prop))). Qed.
Lemma lem3611214 {_92445 : Type'} (s : type686 _92445) : (term162 _92445 s) = (term152 _92445 s).
Proof. exact (MK_COMB (@lem3611213 _92445) (@lem3611212 _92445 s)). Qed.
Lemma lem3611215 {_92445 : Type'} (s : type686 _92445) : (term133 _92445 s) = (term133 _92445 s).
Proof. exact (eq_refl (term133 _92445 s)). Qed.
Lemma lem3611216 {_92445 : Type'} (s : type686 _92445) : (term158 _92445 s) = (term153 _92445 s).
Proof. exact (MK_COMB (@lem3611215 _92445 s) (@lem3611214 _92445 s)). Qed.
Lemma lem3611217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3611218 {_92445 : Type'} (s : type686 _92445) : (term163 _92445 s) = (term164 _92445 s).
Proof. exact (MK_COMB (@lem3611217) (@lem3611216 _92445 s)). Qed.
Lemma lem3611219 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) : (term160 _92445 s t) = (term149 _92445 s t).
Proof. exact (eq_refl (term160 _92445 s t)). Qed.
Lemma lem3611220 {_92445 : Type'} (s : type686 _92445) : (term133 _92445 s) = (term133 _92445 s).
Proof. exact (eq_refl (term133 _92445 s)). Qed.
Lemma lem3611221 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) : (term165 _92445 s t) = (term166 _92445 s t).
Proof. exact (MK_COMB (@lem3611220 _92445 s) (@lem3611219 _92445 s t)). Qed.
Lemma lem3611222 {_92445 : Type'} (s : type686 _92445) : (term167 _92445 s) = (term168 _92445 s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611221 _92445 s t)). Qed.
Lemma lem3611223 {_92445 : Type'} : (@ex (_92445 -> Prop)) = (@ex (_92445 -> Prop)).
Proof. exact (eq_refl (@ex (_92445 -> Prop))). Qed.
Lemma lem3611224 {_92445 : Type'} (s : type686 _92445) : (term159 _92445 s) = (term169 _92445 s).
Proof. exact (MK_COMB (@lem3611223 _92445) (@lem3611222 _92445 s)). Qed.
Lemma lem3611225 {_92445 : Type'} (s : type686 _92445) : ((term158 _92445 s) = (term159 _92445 s)) = ((term153 _92445 s) = (term169 _92445 s)).
Proof. exact (MK_COMB (@lem3611218 _92445 s) (@lem3611224 _92445 s)). Qed.
Lemma lem3611226 {_92445 : Type'} (s : type686 _92445) : (term153 _92445 s) = (term169 _92445 s).
Proof. exact (EQ_MP (@lem3611225 _92445 s) (@lem3611210 _92445 s)). Qed.
Lemma lem3611228 {_92445 : Type'} (s : type686 _92445) : (term135 _92445 s) = (term169 _92445 s).
Proof. exact (TRANS (@lem3611206 _92445 s) (@lem3611226 _92445 s)). Qed.
Lemma lem3611229 {_92445 : Type'} (s : type686 _92445) : ((term31 _92445 s) = (term32 _92445 s)) = (term169 _92445 s).
Proof. exact (TRANS (@lem3611103 _92445 s) (@lem3611228 _92445 s)). Qed.
Lemma lem3611230 {_92445 : Type'} (s : type686 _92445) (h1 : (term31 _92445 s) = (term32 _92445 s)) : term169 _92445 s.
Proof. exact (EQ_MP (@lem3611229 _92445 s) (@lem3611058 _92445 s h1)). Qed.
Lemma lem3611239 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term170 _92445 x s) = (term171 _92445 x s).
Proof. exact (@lem17045 (@FINITE _92445 x) (term31 _92445 s)). Qed.
Lemma lem3611251 {_92445 : Type'} (x : _92445 -> Prop) (t : _92445 -> Prop) (s : type686 _92445) : (term172 _92445 x t s) = (term173 _92445 x t s).
Proof. exact (@lem17160 (t = x) (@IN (_92445 -> Prop) t s)). Qed.
Lemma lem3611256 {_92445 : Type'} (t : _92445 -> Prop) : (@FINITE _92445 t) = (@FINITE _92445 t).
Proof. exact (eq_refl (@FINITE _92445 t)). Qed.
Lemma lem3611261 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term174 _92445 x s t) = (term175 _92445 x s t).
Proof. exact (@lem17362 (term77 _92445 x t s) (@FINITE _92445 t)). Qed.
Lemma lem3611262 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3611263 {_92445 : Type'} (x : _92445 -> Prop) (t : _92445 -> Prop) (s : type686 _92445) : (term176 _92445 x t s) = (term177 _92445 x t s).
Proof. exact (MK_COMB (@lem3611262) (@lem3611251 _92445 x t s)). Qed.
Lemma lem3611264 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term178 _92445 x s t) = (term179 _92445 x s t).
Proof. exact (MK_COMB (@lem3611263 _92445 x t s) (@lem3611256 _92445 t)). Qed.
Lemma lem3611265 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term81 _92445 x s t) = (term178 _92445 x s t).
Proof. exact (@lem17265 (term77 _92445 x t s) (@FINITE _92445 t)). Qed.
Lemma lem3611266 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term81 _92445 x s t) = (term179 _92445 x s t).
Proof. exact (TRANS (@lem3611265 _92445 x s t) (@lem3611264 _92445 x s t)). Qed.
Lemma lem3611267 {_92445 : Type'} (P : type686 _92445) : (term115 _92445 P) = (term116 _92445 P).
Proof. exact (@lem18392 (_92445 -> Prop) P). Qed.
Lemma lem3611268 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term180 _92445 x s) = (term181 _92445 x s).
Proof. exact (@lem3611267 _92445 (term83 _92445 x s)). Qed.
Lemma lem3611269 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term182 _92445 x s t) = (term81 _92445 x s t).
Proof. exact (eq_refl (term182 _92445 x s t)). Qed.
Lemma lem3611270 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3611271 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term183 _92445 x s t) = (term174 _92445 x s t).
Proof. exact (MK_COMB (@lem3611270) (@lem3611269 _92445 x s t)). Qed.
Lemma lem3611272 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term183 _92445 x s t) = (term175 _92445 x s t).
Proof. exact (TRANS (@lem3611271 _92445 x s t) (@lem3611261 _92445 x s t)). Qed.
Lemma lem3611273 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term184 _92445 x s) = (term185 _92445 x s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611272 _92445 x s t)). Qed.
Lemma lem3611274 {_92445 : Type'} : (@ex (_92445 -> Prop)) = (@ex (_92445 -> Prop)).
Proof. exact (eq_refl (@ex (_92445 -> Prop))). Qed.
Lemma lem3611275 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term181 _92445 x s) = (term186 _92445 x s).
Proof. exact (MK_COMB (@lem3611274 _92445) (@lem3611273 _92445 x s)). Qed.
Lemma lem3611276 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term180 _92445 x s) = (term186 _92445 x s).
Proof. exact (TRANS (@lem3611268 _92445 x s) (@lem3611275 _92445 x s)). Qed.
Lemma lem3611277 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term83 _92445 x s) = (term187 _92445 x s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611266 _92445 x s t)). Qed.
Lemma lem3611278 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3611279 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term84 _92445 x s) = (term188 _92445 x s).
Proof. exact (MK_COMB (@lem3611278 _92445) (@lem3611277 _92445 x s)). Qed.
Lemma lem3611280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3611281 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term189 _92445 x s) = (term190 _92445 x s).
Proof. exact (MK_COMB (@lem3611280) (@lem3611239 _92445 x s)). Qed.
Lemma lem3611282 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term191 _92445 x s) = (term192 _92445 x s).
Proof. exact (MK_COMB (@lem3611281 _92445 x s) (@lem3611279 _92445 x s)). Qed.
Lemma lem3611284 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term193 _92445 x s) = (term193 _92445 x s).
Proof. exact (eq_refl (term193 _92445 x s)). Qed.
Lemma lem3611285 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term194 _92445 x s) = (term195 _92445 x s).
Proof. exact (MK_COMB (@lem3611284 _92445 x s) (@lem3611276 _92445 x s)). Qed.
Lemma lem3611286 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3611287 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term196 _92445 x s) = (term197 _92445 x s).
Proof. exact (MK_COMB (@lem3611286) (@lem3611285 _92445 x s)). Qed.
Lemma lem3611288 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term198 _92445 x s) = (term199 _92445 x s).
Proof. exact (MK_COMB (@lem3611287 _92445 x s) (@lem3611282 _92445 x s)). Qed.
Lemma lem3611289 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term111 _92445 x s) = (term198 _92445 x s).
Proof. exact (@lem17646 (term91 _92445 x s) (term84 _92445 x s)). Qed.
Lemma lem3611290 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term111 _92445 x s) = (term199 _92445 x s).
Proof. exact (TRANS (@lem3611289 _92445 x s) (@lem3611288 _92445 x s)). Qed.
Lemma lem3611373 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3611374 {_92445 : Type'} (P : Prop) (Q : type686 _92445) : (term138 _92445 P Q) = (term139 _92445 P Q).
Proof. exact (@lem3611373 (_92445 -> Prop) P Q). Qed.
Lemma lem3611375 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term200 _92445 x s) = (term201 _92445 x s).
Proof. exact (@lem3611374 _92445 (term91 _92445 x s) (term185 _92445 x s)). Qed.
Lemma lem3611376 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term202 _92445 x s t) = (term175 _92445 x s t).
Proof. exact (eq_refl (term202 _92445 x s t)). Qed.
Lemma lem3611377 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term203 _92445 x s) = (term185 _92445 x s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611376 _92445 x s t)). Qed.
Lemma lem3611378 {_92445 : Type'} : (@ex (_92445 -> Prop)) = (@ex (_92445 -> Prop)).
Proof. exact (eq_refl (@ex (_92445 -> Prop))). Qed.
Lemma lem3611379 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term204 _92445 x s) = (term186 _92445 x s).
Proof. exact (MK_COMB (@lem3611378 _92445) (@lem3611377 _92445 x s)). Qed.
Lemma lem3611380 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term193 _92445 x s) = (term193 _92445 x s).
Proof. exact (eq_refl (term193 _92445 x s)). Qed.
Lemma lem3611381 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term200 _92445 x s) = (term195 _92445 x s).
Proof. exact (MK_COMB (@lem3611380 _92445 x s) (@lem3611379 _92445 x s)). Qed.
Lemma lem3611382 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3611383 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term205 _92445 x s) = (term206 _92445 x s).
Proof. exact (MK_COMB (@lem3611382) (@lem3611381 _92445 x s)). Qed.
Lemma lem3611384 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term202 _92445 x s t) = (term175 _92445 x s t).
Proof. exact (eq_refl (term202 _92445 x s t)). Qed.
Lemma lem3611385 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term193 _92445 x s) = (term193 _92445 x s).
Proof. exact (eq_refl (term193 _92445 x s)). Qed.
Lemma lem3611386 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term207 _92445 x s t) = (term208 _92445 x s t).
Proof. exact (MK_COMB (@lem3611385 _92445 x s) (@lem3611384 _92445 x s t)). Qed.
Lemma lem3611387 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term209 _92445 x s) = (term210 _92445 x s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611386 _92445 x s t)). Qed.
Lemma lem3611388 {_92445 : Type'} : (@ex (_92445 -> Prop)) = (@ex (_92445 -> Prop)).
Proof. exact (eq_refl (@ex (_92445 -> Prop))). Qed.
Lemma lem3611389 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term201 _92445 x s) = (term211 _92445 x s).
Proof. exact (MK_COMB (@lem3611388 _92445) (@lem3611387 _92445 x s)). Qed.
Lemma lem3611390 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : ((term200 _92445 x s) = (term201 _92445 x s)) = ((term195 _92445 x s) = (term211 _92445 x s)).
Proof. exact (MK_COMB (@lem3611383 _92445 x s) (@lem3611389 _92445 x s)). Qed.
Lemma lem3611391 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term195 _92445 x s) = (term211 _92445 x s).
Proof. exact (EQ_MP (@lem3611390 _92445 x s) (@lem3611375 _92445 x s)). Qed.
Lemma lem3611392 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3611393 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term197 _92445 x s) = (term212 _92445 x s).
Proof. exact (MK_COMB (@lem3611392) (@lem3611391 _92445 x s)). Qed.
Lemma lem3611394 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term192 _92445 x s) = (term192 _92445 x s).
Proof. exact (eq_refl (term192 _92445 x s)). Qed.
Lemma lem3611395 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term199 _92445 x s) = (term213 _92445 x s).
Proof. exact (MK_COMB (@lem3611393 _92445 x s) (@lem3611394 _92445 x s)). Qed.
Lemma lem3611397 {A : Type'} (P : A -> Prop) (Q : Prop) : (term214 A P Q) = (term215 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3611398 {_92445 : Type'} (P : type686 _92445) (Q : Prop) : (term216 _92445 P Q) = (term217 _92445 P Q).
Proof. exact (@lem3611397 (_92445 -> Prop) P Q). Qed.
Lemma lem3611399 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term218 _92445 x s) = (term219 _92445 x s).
Proof. exact (@lem3611398 _92445 (term210 _92445 x s) (term192 _92445 x s)). Qed.
Lemma lem3611400 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term220 _92445 x s t) = (term208 _92445 x s t).
Proof. exact (eq_refl (term220 _92445 x s t)). Qed.
Lemma lem3611401 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term221 _92445 x s) = (term210 _92445 x s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611400 _92445 x s t)). Qed.
Lemma lem3611402 {_92445 : Type'} : (@ex (_92445 -> Prop)) = (@ex (_92445 -> Prop)).
Proof. exact (eq_refl (@ex (_92445 -> Prop))). Qed.
Lemma lem3611403 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term222 _92445 x s) = (term211 _92445 x s).
Proof. exact (MK_COMB (@lem3611402 _92445) (@lem3611401 _92445 x s)). Qed.
Lemma lem3611404 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3611405 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term223 _92445 x s) = (term212 _92445 x s).
Proof. exact (MK_COMB (@lem3611404) (@lem3611403 _92445 x s)). Qed.
Lemma lem3611406 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term192 _92445 x s) = (term192 _92445 x s).
Proof. exact (eq_refl (term192 _92445 x s)). Qed.
Lemma lem3611407 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term218 _92445 x s) = (term213 _92445 x s).
Proof. exact (MK_COMB (@lem3611405 _92445 x s) (@lem3611406 _92445 x s)). Qed.
Lemma lem3611408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3611409 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term224 _92445 x s) = (term225 _92445 x s).
Proof. exact (MK_COMB (@lem3611408) (@lem3611407 _92445 x s)). Qed.
Lemma lem3611410 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term220 _92445 x s t) = (term208 _92445 x s t).
Proof. exact (eq_refl (term220 _92445 x s t)). Qed.
Lemma lem3611411 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3611412 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term226 _92445 x s t) = (term227 _92445 x s t).
Proof. exact (MK_COMB (@lem3611411) (@lem3611410 _92445 x s t)). Qed.
Lemma lem3611413 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term192 _92445 x s) = (term192 _92445 x s).
Proof. exact (eq_refl (term192 _92445 x s)). Qed.
Lemma lem3611414 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) : (term228 _92445 t x s) = (term229 _92445 t x s).
Proof. exact (MK_COMB (@lem3611412 _92445 x s t) (@lem3611413 _92445 x s)). Qed.
Lemma lem3611415 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term230 _92445 x s) = (term231 _92445 x s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611414 _92445 t x s)). Qed.
Lemma lem3611416 {_92445 : Type'} : (@ex (_92445 -> Prop)) = (@ex (_92445 -> Prop)).
Proof. exact (eq_refl (@ex (_92445 -> Prop))). Qed.
Lemma lem3611417 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term219 _92445 x s) = (term232 _92445 x s).
Proof. exact (MK_COMB (@lem3611416 _92445) (@lem3611415 _92445 x s)). Qed.
Lemma lem3611418 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : ((term218 _92445 x s) = (term219 _92445 x s)) = ((term213 _92445 x s) = (term232 _92445 x s)).
Proof. exact (MK_COMB (@lem3611409 _92445 x s) (@lem3611417 _92445 x s)). Qed.
Lemma lem3611419 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term213 _92445 x s) = (term232 _92445 x s).
Proof. exact (EQ_MP (@lem3611418 _92445 x s) (@lem3611399 _92445 x s)). Qed.
Lemma lem3611421 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term199 _92445 x s) = (term232 _92445 x s).
Proof. exact (TRANS (@lem3611395 _92445 x s) (@lem3611419 _92445 x s)). Qed.
Lemma lem3611422 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term111 _92445 x s) = (term232 _92445 x s).
Proof. exact (TRANS (@lem3611290 _92445 x s) (@lem3611421 _92445 x s)). Qed.
Lemma lem3611423 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term111 _92445 x s) : term232 _92445 x s.
Proof. exact (EQ_MP (@lem3611422 _92445 x s) (@lem3611063 _92445 x s h1)). Qed.
Lemma lem3611424 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term229 _92445 t x s) : term229 _92445 t x s.
Proof. exact (h1). Qed.
Lemma lem3611425 {_92445 : Type'} (s : type686 _92445) (t' : _92445 -> Prop) (h1 : term166 _92445 s t') : term166 _92445 s t'.
Proof. exact (h1). Qed.
Lemma lem3611448 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term179 _92445 x s t) = (term179 _92445 x s t).
Proof. exact (eq_refl (term179 _92445 x s t)). Qed.
Lemma lem3611449 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term187 _92445 x s) = (term187 _92445 x s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611448 _92445 x s t)). Qed.
Lemma lem3611450 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3611451 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term188 _92445 x s) = (term188 _92445 x s).
Proof. exact (MK_COMB (@lem3611450 _92445) (@lem3611449 _92445 x s)). Qed.
Lemma lem3611468 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term190 _92445 x s) = (term190 _92445 x s).
Proof. exact (eq_refl (term190 _92445 x s)). Qed.
Lemma lem3611469 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term192 _92445 x s) = (term192 _92445 x s).
Proof. exact (MK_COMB (@lem3611468 _92445 x s) (@lem3611451 _92445 x s)). Qed.
Lemma lem3611506 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term227 _92445 x s t) = (term227 _92445 x s t).
Proof. exact (eq_refl (term227 _92445 x s t)). Qed.
Lemma lem3611507 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) : (term229 _92445 t x s) = (term229 _92445 t x s).
Proof. exact (MK_COMB (@lem3611506 _92445 x s t) (@lem3611469 _92445 x s)). Qed.
Lemma lem3611508 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term229 _92445 t x s) : term229 _92445 t x s.
Proof. exact (EQ_MP (@lem3611507 _92445 t x s) (@lem3611424 _92445 t x s h1)). Qed.
Lemma lem3611531 {_92445 : Type'} (s : type686 _92445) (t' : _92445 -> Prop) : (term149 _92445 s t') = (term149 _92445 s t').
Proof. exact (eq_refl (term149 _92445 s t')). Qed.
Lemma lem3611544 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) : (term114 _92445 s t) = (term114 _92445 s t).
Proof. exact (eq_refl (term114 _92445 s t)). Qed.
Lemma lem3611545 {_92445 : Type'} (s : type686 _92445) : (term124 _92445 s) = (term124 _92445 s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611544 _92445 s t)). Qed.
Lemma lem3611546 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3611547 {_92445 : Type'} (s : type686 _92445) : (term125 _92445 s) = (term125 _92445 s).
Proof. exact (MK_COMB (@lem3611546 _92445) (@lem3611545 _92445 s)). Qed.
Lemma lem3611554 {_92445 : Type'} (s : type686 _92445) : (term129 _92445 s) = (term129 _92445 s).
Proof. exact (eq_refl (term129 _92445 s)). Qed.
Lemma lem3611555 {_92445 : Type'} (s : type686 _92445) : (term131 _92445 s) = (term131 _92445 s).
Proof. exact (MK_COMB (@lem3611554 _92445 s) (@lem3611547 _92445 s)). Qed.
Lemma lem3611556 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3611557 {_92445 : Type'} (s : type686 _92445) : (term133 _92445 s) = (term133 _92445 s).
Proof. exact (MK_COMB (@lem3611556) (@lem3611555 _92445 s)). Qed.
Lemma lem3611558 {_92445 : Type'} (s : type686 _92445) (t' : _92445 -> Prop) : (term166 _92445 s t') = (term166 _92445 s t').
Proof. exact (MK_COMB (@lem3611557 _92445 s) (@lem3611531 _92445 s t')). Qed.
Lemma lem3611559 {_92445 : Type'} (s : type686 _92445) (t' : _92445 -> Prop) (h1 : term166 _92445 s t') : term166 _92445 s t'.
Proof. exact (EQ_MP (@lem3611558 _92445 s t') (@lem3611425 _92445 s t' h1)). Qed.
Lemma lem3611560 {_92445 : Type'} (s : type686 _92445) (h1 : term131 _92445 s) : term131 _92445 s.
Proof. exact (h1). Qed.
Lemma lem3611561 {_92445 : Type'} (s : type686 _92445) (t' : _92445 -> Prop) (h1 : term149 _92445 s t') : term149 _92445 s t'.
Proof. exact (h1). Qed.
Lemma lem3611562 {_92445 : Type'} (s : type686 _92445) (h1 : term131 _92445 s) : term125 _92445 s.
Proof. exact (proj2 (@lem3611560 _92445 s h1)). Qed.
Lemma lem3611564 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term208 _92445 x s t.
Proof. exact (h1). Qed.
Lemma lem3611565 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term192 _92445 x s.
Proof. exact (h1). Qed.
Lemma lem3611566 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term175 _92445 x s t.
Proof. exact (proj2 (@lem3611564 _92445 x s t h1)). Qed.
Lemma lem3611567 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term91 _92445 x s.
Proof. exact (proj1 (@lem3611564 _92445 x s t h1)). Qed.
Lemma lem3611569 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term77 _92445 x t s.
Proof. exact (proj1 (@lem3611566 _92445 x s t h1)). Qed.
Lemma lem3611574 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term188 _92445 x s.
Proof. exact (proj2 (@lem3611565 _92445 x s h1)). Qed.
Lemma lem3611575 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term171 _92445 x s.
Proof. exact (proj1 (@lem3611565 _92445 x s h1)). Qed.
Lemma lem3611578 {_92445 : Type'} (s : type686 _92445) (t' : _92445 -> Prop) (h1 : term149 _92445 s t') : term113 _92445 s t'.
Proof. exact (proj2 (@lem3611561 _92445 s t' h1)). Qed.
Lemma lem3611582 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term208 _92445 x s t.
Proof. exact (h1). Qed.
Lemma lem3611583 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term192 _92445 x s.
Proof. exact (h1). Qed.
Lemma lem3611584 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term175 _92445 x s t.
Proof. exact (proj2 (@lem3611582 _92445 x s t h1)). Qed.
Lemma lem3611585 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term91 _92445 x s.
Proof. exact (proj1 (@lem3611582 _92445 x s t h1)). Qed.
Lemma lem3611587 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term77 _92445 x t s.
Proof. exact (proj1 (@lem3611584 _92445 x s t h1)). Qed.
Lemma lem3611592 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term188 _92445 x s.
Proof. exact (proj2 (@lem3611583 _92445 x s h1)). Qed.
Lemma lem3611593 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term171 _92445 x s.
Proof. exact (proj1 (@lem3611583 _92445 x s h1)). Qed.
Lemma lem3611628 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : t = x) : t = x.
Proof. exact (h1). Qed.
Lemma lem3611640 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) : (term114 _92445 s t) = (term114 _92445 s t).
Proof. exact (eq_refl (term114 _92445 s t)). Qed.
Lemma lem3611641 {_92445 : Type'} (s : type686 _92445) : (term124 _92445 s) = (term124 _92445 s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611640 _92445 s t)). Qed.
Lemma lem3611642 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3611644 {_92445 : Type'} (s : type686 _92445) : (term125 _92445 s) = (term125 _92445 s).
Proof. exact (MK_COMB (@lem3611642 _92445) (@lem3611641 _92445 s)). Qed.
Lemma lem3611645 {_92445 : Type'} (s : type686 _92445) (h1 : term131 _92445 s) : term125 _92445 s.
Proof. exact (EQ_MP (@lem3611644 _92445 s) (@lem3611562 _92445 s h1)). Qed.
Lemma lem3611661 {_92445 : Type'} (t : _92445 -> Prop) (s : type686 _92445) (h1 : @IN (_92445 -> Prop) t s) : @IN (_92445 -> Prop) t s.
Proof. exact (h1). Qed.
Lemma lem3611696 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term179 _92445 x s t) = (term233 _92445 x s t).
Proof. exact (@lem19699 (term234 _92445 t x) (term235 _92445 t s) (@FINITE _92445 t)). Qed.
Lemma lem3611697 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term187 _92445 x s) = (term236 _92445 x s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611696 _92445 x s t)). Qed.
Lemma lem3611698 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3611700 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term188 _92445 x s) = (term237 _92445 x s).
Proof. exact (MK_COMB (@lem3611698 _92445) (@lem3611697 _92445 x s)). Qed.
Lemma lem3611701 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term237 _92445 x s.
Proof. exact (EQ_MP (@lem3611700 _92445 x s) (@lem3611574 _92445 x s h1)). Qed.
Lemma lem3611705 {_92445 : Type'} (x : _92445 -> Prop) (h1 : term238 _92445 x) : term238 _92445 x.
Proof. exact (h1). Qed.
Lemma lem3611749 {_92445 : Type'} (s : type686 _92445) (h1 : term142 _92445 s) : term142 _92445 s.
Proof. exact (h1). Qed.
Lemma lem3611777 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : t = x) : t = x.
Proof. exact (h1). Qed.
Lemma lem3611835 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term179 _92445 x s t) = (term233 _92445 x s t).
Proof. exact (@lem19699 (term234 _92445 t x) (term235 _92445 t s) (@FINITE _92445 t)). Qed.
Lemma lem3611836 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term187 _92445 x s) = (term236 _92445 x s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611835 _92445 x s t)). Qed.
Lemma lem3611837 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3611839 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term188 _92445 x s) = (term237 _92445 x s).
Proof. exact (MK_COMB (@lem3611837 _92445) (@lem3611836 _92445 x s)). Qed.
Lemma lem3611840 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term237 _92445 x s.
Proof. exact (EQ_MP (@lem3611839 _92445 x s) (@lem3611592 _92445 x s h1)). Qed.
Lemma lem3611844 {_92445 : Type'} (x : _92445 -> Prop) (h1 : term238 _92445 x) : term238 _92445 x.
Proof. exact (h1). Qed.
Lemma lem3611874 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) : (term179 _92445 x s t) = (term233 _92445 x s t).
Proof. exact (@lem19699 (term234 _92445 t x) (term235 _92445 t s) (@FINITE _92445 t)). Qed.
Lemma lem3611875 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term187 _92445 x s) = (term236 _92445 x s).
Proof. exact (fun_ext (fun t : _92445 -> Prop => @lem3611874 _92445 x s t)). Qed.
Lemma lem3611876 {_92445 : Type'} : (@all (_92445 -> Prop)) = (@all (_92445 -> Prop)).
Proof. exact (eq_refl (@all (_92445 -> Prop))). Qed.
Lemma lem3611878 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : (term188 _92445 x s) = (term237 _92445 x s).
Proof. exact (MK_COMB (@lem3611876 _92445) (@lem3611875 _92445 x s)). Qed.
Lemma lem3611879 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term237 _92445 x s.
Proof. exact (EQ_MP (@lem3611878 _92445 x s) (@lem3611592 _92445 x s h1)). Qed.
Lemma lem3611887 {_92445 : Type'} (_39141 : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) : term239 _92445 s _39141.
Proof. exact (@lem3611645 _92445 s h1 _39141). Qed.
Lemma lem3611888 {_92445 : Type'} (s : type686 _92445) (_39141 : _92445 -> Prop) : (term239 _92445 s _39141) = (term114 _92445 s _39141).
Proof. exact (eq_refl (term239 _92445 s _39141)). Qed.
Lemma lem3611893 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term240 _92445 x s _39143.
Proof. exact (@lem3611701 _92445 x s h1 _39143). Qed.
Lemma lem3611894 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (_39143 : _92445 -> Prop) : (term240 _92445 x s _39143) = (term233 _92445 x s _39143).
Proof. exact (eq_refl (term240 _92445 x s _39143)). Qed.
Lemma lem3611895 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term233 _92445 x s _39143.
Proof. exact (EQ_MP (@lem3611894 _92445 x s _39143) (@lem3611893 _92445 _39143 x s h1)). Qed.
Lemma lem3611902 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term240 _92445 x s _39146.
Proof. exact (@lem3611840 _92445 x s h1 _39146). Qed.
Lemma lem3611903 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (_39146 : _92445 -> Prop) : (term240 _92445 x s _39146) = (term233 _92445 x s _39146).
Proof. exact (eq_refl (term240 _92445 x s _39146)). Qed.
Lemma lem3611904 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term233 _92445 x s _39146.
Proof. exact (EQ_MP (@lem3611903 _92445 x s _39146) (@lem3611902 _92445 _39146 x s h1)). Qed.
Lemma lem3611905 {_92445 : Type'} (_39147 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term240 _92445 x s _39147.
Proof. exact (@lem3611879 _92445 x s h1 _39147). Qed.
Lemma lem3611906 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (_39147 : _92445 -> Prop) : (term240 _92445 x s _39147) = (term233 _92445 x s _39147).
Proof. exact (eq_refl (term240 _92445 x s _39147)). Qed.
Lemma lem3611907 {_92445 : Type'} (_39147 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term233 _92445 x s _39147.
Proof. exact (EQ_MP (@lem3611906 _92445 x s _39147) (@lem3611905 _92445 _39147 x s h1)). Qed.
Lemma lem3611925 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term238 _92445 t.
Proof. exact (proj2 (@lem3611566 _92445 x s t h1)). Qed.
Lemma lem3611931 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : t = x) : t = x.
Proof. exact (h1). Qed.
Lemma lem3611939 {_92445 : Type'} (_39141 : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) : term114 _92445 s _39141.
Proof. exact (EQ_MP (@lem3611888 _92445 s _39141) (@lem3611887 _92445 _39141 s h1)). Qed.
Lemma lem3611941 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term238 _92445 t.
Proof. exact (proj2 (@lem3611566 _92445 x s t h1)). Qed.
Lemma lem3611947 {_92445 : Type'} (t : _92445 -> Prop) (s : type686 _92445) (h1 : @IN (_92445 -> Prop) t s) : @IN (_92445 -> Prop) t s.
Proof. exact (h1). Qed.
Lemma lem3611957 {_92445 : Type'} (x : _92445 -> Prop) (h1 : term238 _92445 x) : term238 _92445 x.
Proof. exact (h1). Qed.
Lemma lem3611963 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term241 _92445 x _39143.
Proof. exact (proj1 (@lem3611895 _92445 _39143 x s h1)). Qed.
Lemma lem3611979 {_92445 : Type'} (s : type686 _92445) (h1 : term142 _92445 s) : term142 _92445 s.
Proof. exact (h1). Qed.
Lemma lem3611999 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term238 _92445 t.
Proof. exact (proj2 (@lem3611584 _92445 x s t h1)). Qed.
Lemma lem3612005 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : t = x) : t = x.
Proof. exact (h1). Qed.
Lemma lem3612007 {_92445 : Type'} (s : type686 _92445) (t' : _92445 -> Prop) (h1 : term149 _92445 s t') : term142 _92445 s.
Proof. exact (proj1 (@lem3611561 _92445 s t' h1)). Qed.
Lemma lem3612027 {_92445 : Type'} (x : _92445 -> Prop) (h1 : term238 _92445 x) : term238 _92445 x.
Proof. exact (h1). Qed.
Lemma lem3612033 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term241 _92445 x _39146.
Proof. exact (proj1 (@lem3611904 _92445 _39146 x s h1)). Qed.
Lemma lem3612045 {_92445 : Type'} (s : type686 _92445) (t' : _92445 -> Prop) (h1 : term149 _92445 s t') : term238 _92445 t'.
Proof. exact (proj2 (@lem3611578 _92445 s t' h1)). Qed.
Lemma lem3612059 {_92445 : Type'} (_39147 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term114 _92445 s _39147.
Proof. exact (proj2 (@lem3611907 _92445 _39147 x s h1)). Qed.
Lemma lem3612102 {_92445 : Type'} : (term242 _92445) = (term242 _92445).
Proof. exact (eq_refl (term242 _92445)). Qed.
Lemma lem3612103 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : t = x) : (term243 _92445 t) = (term243 _92445 x).
Proof. exact (MK_COMB (@lem3612102 _92445) (@lem3611931 _92445 t x h1)). Qed.
Lemma lem3612104 {_92445 : Type'} (x : _92445 -> Prop) : (term243 _92445 x) = (term238 _92445 x).
Proof. exact (eq_refl (term243 _92445 x)). Qed.
Lemma lem3612105 {_92445 : Type'} (t : _92445 -> Prop) : (term244 _92445 t) = (term244 _92445 t).
Proof. exact (eq_refl (term244 _92445 t)). Qed.
Lemma lem3612106 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) : ((term243 _92445 t) = (term243 _92445 x)) = ((term243 _92445 t) = (term238 _92445 x)).
Proof. exact (MK_COMB (@lem3612105 _92445 t) (@lem3612104 _92445 x)). Qed.
Lemma lem3612107 {_92445 : Type'} (t : _92445 -> Prop) : (term243 _92445 t) = (term238 _92445 t).
Proof. exact (eq_refl (term243 _92445 t)). Qed.
Lemma lem3612108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3612109 {_92445 : Type'} (t : _92445 -> Prop) : (term244 _92445 t) = (term245 _92445 t).
Proof. exact (MK_COMB (@lem3612108) (@lem3612107 _92445 t)). Qed.
Lemma lem3612110 {_92445 : Type'} (x : _92445 -> Prop) : (term238 _92445 x) = (term238 _92445 x).
Proof. exact (eq_refl (term238 _92445 x)). Qed.
Lemma lem3612111 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) : ((term243 _92445 t) = (term238 _92445 x)) = ((term238 _92445 t) = (term238 _92445 x)).
Proof. exact (MK_COMB (@lem3612109 _92445 t) (@lem3612110 _92445 x)). Qed.
Lemma lem3612112 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) : ((term243 _92445 t) = (term243 _92445 x)) = ((term238 _92445 t) = (term238 _92445 x)).
Proof. exact (TRANS (@lem3612106 _92445 t x) (@lem3612111 _92445 t x)). Qed.
Lemma lem3612113 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : t = x) : (term238 _92445 t) = (term238 _92445 x).
Proof. exact (EQ_MP (@lem3612112 _92445 t x) (@lem3612103 _92445 t x h1)). Qed.
Lemma lem3612114 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : term238 _92445 x.
Proof. exact (EQ_MP (@lem3612113 _92445 t x h2) (@lem3611925 _92445 x s t h1)). Qed.
Lemma lem3612199 {_92445 : Type'} : (term242 _92445) = (term242 _92445).
Proof. exact (eq_refl (term242 _92445)). Qed.
Lemma lem3612200 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : t = x) : (term243 _92445 t) = (term243 _92445 x).
Proof. exact (MK_COMB (@lem3612199 _92445) (@lem3612005 _92445 t x h1)). Qed.
Lemma lem3612201 {_92445 : Type'} (x : _92445 -> Prop) : (term243 _92445 x) = (term238 _92445 x).
Proof. exact (eq_refl (term243 _92445 x)). Qed.
Lemma lem3612202 {_92445 : Type'} (t : _92445 -> Prop) : (term244 _92445 t) = (term244 _92445 t).
Proof. exact (eq_refl (term244 _92445 t)). Qed.
Lemma lem3612203 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) : ((term243 _92445 t) = (term243 _92445 x)) = ((term243 _92445 t) = (term238 _92445 x)).
Proof. exact (MK_COMB (@lem3612202 _92445 t) (@lem3612201 _92445 x)). Qed.
Lemma lem3612204 {_92445 : Type'} (t : _92445 -> Prop) : (term243 _92445 t) = (term238 _92445 t).
Proof. exact (eq_refl (term243 _92445 t)). Qed.
Lemma lem3612205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3612206 {_92445 : Type'} (t : _92445 -> Prop) : (term244 _92445 t) = (term245 _92445 t).
Proof. exact (MK_COMB (@lem3612205) (@lem3612204 _92445 t)). Qed.
Lemma lem3612207 {_92445 : Type'} (x : _92445 -> Prop) : (term238 _92445 x) = (term238 _92445 x).
Proof. exact (eq_refl (term238 _92445 x)). Qed.
Lemma lem3612208 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) : ((term243 _92445 t) = (term238 _92445 x)) = ((term238 _92445 t) = (term238 _92445 x)).
Proof. exact (MK_COMB (@lem3612206 _92445 t) (@lem3612207 _92445 x)). Qed.
Lemma lem3612209 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) : ((term243 _92445 t) = (term243 _92445 x)) = ((term238 _92445 t) = (term238 _92445 x)).
Proof. exact (TRANS (@lem3612203 _92445 t x) (@lem3612208 _92445 t x)). Qed.
Lemma lem3612210 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : t = x) : (term238 _92445 t) = (term238 _92445 x).
Proof. exact (EQ_MP (@lem3612209 _92445 t x) (@lem3612200 _92445 t x h1)). Qed.
Lemma lem3612211 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : term238 _92445 x.
Proof. exact (EQ_MP (@lem3612210 _92445 t x h2) (@lem3611999 _92445 x s t h1)). Qed.
Lemma lem3612241 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : @FINITE _92445 x.
Proof. exact (proj1 (@lem3611567 _92445 x s t h1)). Qed.
Lemma lem3612242 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term246 _92445 x.
Proof. exact (fun h0 : term238 _92445 x => @lem3612241 _92445 x s t h1). Qed.
Lemma lem3612244 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612245 {_92445 : Type'} (x : _92445 -> Prop) : (term246 _92445 x) = (@FINITE _92445 x).
Proof. exact (@lem3612244 (@FINITE _92445 x)). Qed.
Lemma lem3612246 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : @FINITE _92445 x.
Proof. exact (EQ_MP (@lem3612245 _92445 x) (@lem3612242 _92445 x s t h1)). Qed.
Lemma lem3612249 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3612251 {_92445 : Type'} (x : _92445 -> Prop) : (term238 _92445 x) = (term248 _92445 x).
Proof. exact (@lem3612249 (@FINITE _92445 x)). Qed.
Lemma lem3612254 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : term248 _92445 x.
Proof. exact (EQ_MP (@lem3612251 _92445 x) (@lem3612114 _92445 s t x h1 h2)). Qed.
Lemma lem3612257 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : False.
Proof. exact (@lem3612254 _92445 s t x h1 h2 (@lem3612246 _92445 x s t h1)). Qed.
Lemma lem3612258 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : term249.
Proof. exact (fun h0 : ~ False => @lem3612257 _92445 s t x h1 h2). Qed.
Lemma lem3612260 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612261 : term249 = False.
Proof. exact (@lem3612260 False). Qed.
Lemma lem3612264 {_92445 : Type'} (t : _92445 -> Prop) (s : type686 _92445) (h1 : @IN (_92445 -> Prop) t s) : @IN (_92445 -> Prop) t s.
Proof. exact (h1). Qed.
Lemma lem3612265 {_92445 : Type'} (t : _92445 -> Prop) (s : type686 _92445) (h1 : @IN (_92445 -> Prop) t s) : term250 _92445 t s.
Proof. exact (fun h0 : term235 _92445 t s => @lem3612264 _92445 t s h1). Qed.
Lemma lem3612267 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612268 {_92445 : Type'} (t : _92445 -> Prop) (s : type686 _92445) : (term250 _92445 t s) = (@IN (_92445 -> Prop) t s).
Proof. exact (@lem3612267 (@IN (_92445 -> Prop) t s)). Qed.
Lemma lem3612269 {_92445 : Type'} (t : _92445 -> Prop) (s : type686 _92445) (h1 : @IN (_92445 -> Prop) t s) : @IN (_92445 -> Prop) t s.
Proof. exact (EQ_MP (@lem3612268 _92445 t s) (@lem3612265 _92445 t s h1)). Qed.
Lemma lem3612275 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3612276 {_92445 : Type'} (_39141 : _92445 -> Prop) (s : type686 _92445) : (term114 _92445 s _39141) = (term251 _92445 _39141 s).
Proof. exact (@lem3612275 (@FINITE _92445 _39141) (term235 _92445 _39141 s)). Qed.
Lemma lem3612282 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3612283 {_92445 : Type'} (_39141 : _92445 -> Prop) (s : type686 _92445) : (term252 _92445 s _39141) = (term253 _92445 _39141 s).
Proof. exact (MK_COMB (@lem3612282) (@lem3612276 _92445 _39141 s)). Qed.
Lemma lem3612289 {_92445 : Type'} (_39141 : _92445 -> Prop) (s : type686 _92445) : (term251 _92445 _39141 s) = (term251 _92445 _39141 s).
Proof. exact (eq_refl (term251 _92445 _39141 s)). Qed.
Lemma lem3612290 {_92445 : Type'} (_39141 : _92445 -> Prop) (s : type686 _92445) : ((term114 _92445 s _39141) = (term251 _92445 _39141 s)) = ((term251 _92445 _39141 s) = (term251 _92445 _39141 s)).
Proof. exact (MK_COMB (@lem3612283 _92445 _39141 s) (@lem3612289 _92445 _39141 s)). Qed.
Lemma lem3612292 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3612293 (x : Prop) : (x = x) = True.
Proof. exact (@lem3612292 Prop x). Qed.
Lemma lem3612294 {_92445 : Type'} (_39141 : _92445 -> Prop) (s : type686 _92445) : ((term251 _92445 _39141 s) = (term251 _92445 _39141 s)) = True.
Proof. exact (@lem3612293 (term251 _92445 _39141 s)). Qed.
Lemma lem3612295 {_92445 : Type'} (_39141 : _92445 -> Prop) (s : type686 _92445) : ((term114 _92445 s _39141) = (term251 _92445 _39141 s)) = True.
Proof. exact (TRANS (@lem3612290 _92445 _39141 s) (@lem3612294 _92445 _39141 s)). Qed.
Lemma lem3612296 {_92445 : Type'} (_39141 : _92445 -> Prop) (s : type686 _92445) : True = ((term114 _92445 s _39141) = (term251 _92445 _39141 s)).
Proof. exact (SYM (@lem3612295 _92445 _39141 s)). Qed.
Lemma lem3612297 {_92445 : Type'} (_39141 : _92445 -> Prop) (s : type686 _92445) : (term114 _92445 s _39141) = (term251 _92445 _39141 s).
Proof. exact (EQ_MP (@lem3612296 _92445 _39141 s) (@lem0)). Qed.
Lemma lem3612298 {_92445 : Type'} (_39141 : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) : term251 _92445 _39141 s.
Proof. exact (EQ_MP (@lem3612297 _92445 _39141 s) (@lem3611939 _92445 _39141 s h1)). Qed.
Lemma lem3612300 (b : Prop) (a : Prop) : (a \/ b) = (term254 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3612301 {_92445 : Type'} (s : type686 _92445) (_39141 : _92445 -> Prop) : (term251 _92445 _39141 s) = (term255 _92445 s _39141).
Proof. exact (@lem3612300 (term235 _92445 _39141 s) (@FINITE _92445 _39141)). Qed.
Lemma lem3612303 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3612304 {_92445 : Type'} (_39141 : _92445 -> Prop) (s : type686 _92445) : (term256 _92445 _39141 s) = (@IN (_92445 -> Prop) _39141 s).
Proof. exact (@lem3612303 (@IN (_92445 -> Prop) _39141 s)). Qed.
Lemma lem3612305 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3612306 {_92445 : Type'} (_39141 : _92445 -> Prop) (s : type686 _92445) : (term257 _92445 _39141 s) = (term258 _92445 _39141 s).
Proof. exact (MK_COMB (@lem3612305) (@lem3612304 _92445 _39141 s)). Qed.
Lemma lem3612307 {_92445 : Type'} (_39141 : _92445 -> Prop) : (@FINITE _92445 _39141) = (@FINITE _92445 _39141).
Proof. exact (eq_refl (@FINITE _92445 _39141)). Qed.
Lemma lem3612308 {_92445 : Type'} (s : type686 _92445) (_39141 : _92445 -> Prop) : (term255 _92445 s _39141) = (term107 _92445 s _39141).
Proof. exact (MK_COMB (@lem3612306 _92445 _39141 s) (@lem3612307 _92445 _39141)). Qed.
Lemma lem3612309 {_92445 : Type'} (s : type686 _92445) (_39141 : _92445 -> Prop) : (term251 _92445 _39141 s) = (term107 _92445 s _39141).
Proof. exact (TRANS (@lem3612301 _92445 s _39141) (@lem3612308 _92445 s _39141)). Qed.
Lemma lem3612312 {_92445 : Type'} (_39141 : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) : term107 _92445 s _39141.
Proof. exact (EQ_MP (@lem3612309 _92445 s _39141) (@lem3612298 _92445 _39141 s h1)). Qed.
Lemma lem3612313 {_92445 : Type'} (_39141 : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) : term107 _92445 s _39141.
Proof. exact (@lem3612312 _92445 _39141 s h1). Qed.
Lemma lem3612314 {_92445 : Type'} (t : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) : term107 _92445 s t.
Proof. exact (@lem3612313 _92445 t s h1). Qed.
Lemma lem3612317 {_92445 : Type'} (t : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) (h2 : @IN (_92445 -> Prop) t s) : @FINITE _92445 t.
Proof. exact (@lem3612314 _92445 t s h1 (@lem3612269 _92445 t s h2)). Qed.
Lemma lem3612318 {_92445 : Type'} (t : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) (h2 : @IN (_92445 -> Prop) t s) : term246 _92445 t.
Proof. exact (fun h0 : term238 _92445 t => @lem3612317 _92445 t s h1 h2). Qed.
Lemma lem3612320 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612321 {_92445 : Type'} (t : _92445 -> Prop) : (term246 _92445 t) = (@FINITE _92445 t).
Proof. exact (@lem3612320 (@FINITE _92445 t)). Qed.
Lemma lem3612322 {_92445 : Type'} (t : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) (h2 : @IN (_92445 -> Prop) t s) : @FINITE _92445 t.
Proof. exact (EQ_MP (@lem3612321 _92445 t) (@lem3612318 _92445 t s h1 h2)). Qed.
Lemma lem3612325 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3612327 {_92445 : Type'} (t : _92445 -> Prop) : (term238 _92445 t) = (term248 _92445 t).
Proof. exact (@lem3612325 (@FINITE _92445 t)). Qed.
Lemma lem3612330 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term248 _92445 t.
Proof. exact (EQ_MP (@lem3612327 _92445 t) (@lem3611941 _92445 x s t h1)). Qed.
Lemma lem3612333 {_92445 : Type'} (x : _92445 -> Prop) (t : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) (h2 : term208 _92445 x s t) (h3 : @IN (_92445 -> Prop) t s) : False.
Proof. exact (@lem3612330 _92445 x s t h2 (@lem3612322 _92445 t s h1 h3)). Qed.
Lemma lem3612334 {_92445 : Type'} (x : _92445 -> Prop) (t : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) (h2 : term208 _92445 x s t) (h3 : @IN (_92445 -> Prop) t s) : term249.
Proof. exact (fun h0 : ~ False => @lem3612333 _92445 x t s h1 h2 h3). Qed.
Lemma lem3612336 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612337 : term249 = False.
Proof. exact (@lem3612336 False). Qed.
Lemma lem3612338 {_92445 : Type'} (x : _92445 -> Prop) (t : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) (h2 : term208 _92445 x s t) (h3 : @IN (_92445 -> Prop) t s) : False.
Proof. exact (EQ_MP (@lem3612337) (@lem3612334 _92445 x t s h1 h2 h3)). Qed.
Lemma lem3612383 {_92445 : Type'} (x : _92445 -> Prop) : x = x.
Proof. exact (@lem21386 (_92445 -> Prop) x). Qed.
Lemma lem3612384 {_92445 : Type'} (x : _92445 -> Prop) : x = x.
Proof. exact (@lem3612383 _92445 x). Qed.
Lemma lem3612385 {_92445 : Type'} (x : _92445 -> Prop) : term259 _92445 x.
Proof. exact (fun h0 : term260 _92445 x => @lem3612384 _92445 x). Qed.
Lemma lem3612387 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612388 {_92445 : Type'} (x : _92445 -> Prop) : (term259 _92445 x) = (x = x).
Proof. exact (@lem3612387 (x = x)). Qed.
Lemma lem3612389 {_92445 : Type'} (x : _92445 -> Prop) : x = x.
Proof. exact (EQ_MP (@lem3612388 _92445 x) (@lem3612385 _92445 x)). Qed.
Lemma lem3612395 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3612396 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) : (term241 _92445 x _39143) = (term261 _92445 _39143 x).
Proof. exact (@lem3612395 (@FINITE _92445 _39143) (term234 _92445 _39143 x)). Qed.
Lemma lem3612404 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3612405 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) : (term262 _92445 x _39143) = (term263 _92445 _39143 x).
Proof. exact (MK_COMB (@lem3612404) (@lem3612396 _92445 _39143 x)). Qed.
Lemma lem3612413 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) : (term261 _92445 _39143 x) = (term261 _92445 _39143 x).
Proof. exact (eq_refl (term261 _92445 _39143 x)). Qed.
Lemma lem3612414 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) : ((term241 _92445 x _39143) = (term261 _92445 _39143 x)) = ((term261 _92445 _39143 x) = (term261 _92445 _39143 x)).
Proof. exact (MK_COMB (@lem3612405 _92445 _39143 x) (@lem3612413 _92445 _39143 x)). Qed.
Lemma lem3612416 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3612417 (x : Prop) : (x = x) = True.
Proof. exact (@lem3612416 Prop x). Qed.
Lemma lem3612418 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) : ((term261 _92445 _39143 x) = (term261 _92445 _39143 x)) = True.
Proof. exact (@lem3612417 (term261 _92445 _39143 x)). Qed.
Lemma lem3612419 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) : ((term241 _92445 x _39143) = (term261 _92445 _39143 x)) = True.
Proof. exact (TRANS (@lem3612414 _92445 _39143 x) (@lem3612418 _92445 _39143 x)). Qed.
Lemma lem3612420 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) : True = ((term241 _92445 x _39143) = (term261 _92445 _39143 x)).
Proof. exact (SYM (@lem3612419 _92445 _39143 x)). Qed.
Lemma lem3612421 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) : (term241 _92445 x _39143) = (term261 _92445 _39143 x).
Proof. exact (EQ_MP (@lem3612420 _92445 _39143 x) (@lem0)). Qed.
Lemma lem3612422 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term261 _92445 _39143 x.
Proof. exact (EQ_MP (@lem3612421 _92445 _39143 x) (@lem3611963 _92445 _39143 x s h1)). Qed.
Lemma lem3612424 (b : Prop) (a : Prop) : (a \/ b) = (term254 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3612425 {_92445 : Type'} (x : _92445 -> Prop) (_39143 : _92445 -> Prop) : (term261 _92445 _39143 x) = (term264 _92445 x _39143).
Proof. exact (@lem3612424 (term234 _92445 _39143 x) (@FINITE _92445 _39143)). Qed.
Lemma lem3612427 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3612428 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) : (term265 _92445 _39143 x) = (_39143 = x).
Proof. exact (@lem3612427 (_39143 = x)). Qed.
Lemma lem3612429 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3612430 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) : (term266 _92445 _39143 x) = (term267 _92445 _39143 x).
Proof. exact (MK_COMB (@lem3612429) (@lem3612428 _92445 _39143 x)). Qed.
Lemma lem3612431 {_92445 : Type'} (_39143 : _92445 -> Prop) : (@FINITE _92445 _39143) = (@FINITE _92445 _39143).
Proof. exact (eq_refl (@FINITE _92445 _39143)). Qed.
Lemma lem3612432 {_92445 : Type'} (x : _92445 -> Prop) (_39143 : _92445 -> Prop) : (term264 _92445 x _39143) = (term268 _92445 x _39143).
Proof. exact (MK_COMB (@lem3612430 _92445 _39143 x) (@lem3612431 _92445 _39143)). Qed.
Lemma lem3612433 {_92445 : Type'} (x : _92445 -> Prop) (_39143 : _92445 -> Prop) : (term261 _92445 _39143 x) = (term268 _92445 x _39143).
Proof. exact (TRANS (@lem3612425 _92445 x _39143) (@lem3612432 _92445 x _39143)). Qed.
Lemma lem3612436 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term268 _92445 x _39143.
Proof. exact (EQ_MP (@lem3612433 _92445 x _39143) (@lem3612422 _92445 _39143 x s h1)). Qed.
Lemma lem3612437 {_92445 : Type'} (_39143 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term268 _92445 x _39143.
Proof. exact (@lem3612436 _92445 _39143 x s h1). Qed.
Lemma lem3612438 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term269 _92445 x.
Proof. exact (@lem3612437 _92445 x x s h1). Qed.
Lemma lem3612441 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : @FINITE _92445 x.
Proof. exact (@lem3612438 _92445 x s h1 (@lem3612389 _92445 x)). Qed.
Lemma lem3612442 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term246 _92445 x.
Proof. exact (fun h0 : term238 _92445 x => @lem3612441 _92445 x s h1). Qed.
Lemma lem3612444 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612445 {_92445 : Type'} (x : _92445 -> Prop) : (term246 _92445 x) = (@FINITE _92445 x).
Proof. exact (@lem3612444 (@FINITE _92445 x)). Qed.
Lemma lem3612446 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : @FINITE _92445 x.
Proof. exact (EQ_MP (@lem3612445 _92445 x) (@lem3612442 _92445 x s h1)). Qed.
Lemma lem3612449 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3612451 {_92445 : Type'} (x : _92445 -> Prop) : (term238 _92445 x) = (term248 _92445 x).
Proof. exact (@lem3612449 (@FINITE _92445 x)). Qed.
Lemma lem3612454 {_92445 : Type'} (x : _92445 -> Prop) (h1 : term238 _92445 x) : term248 _92445 x.
Proof. exact (EQ_MP (@lem3612451 _92445 x) (@lem3611957 _92445 x h1)). Qed.
Lemma lem3612457 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : False.
Proof. exact (@lem3612454 _92445 x h1 (@lem3612446 _92445 x s h2)). Qed.
Lemma lem3612458 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : term249.
Proof. exact (fun h0 : ~ False => @lem3612457 _92445 x s h1 h2). Qed.
Lemma lem3612460 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612461 : term249 = False.
Proof. exact (@lem3612460 False). Qed.
Lemma lem3612462 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : False.
Proof. exact (EQ_MP (@lem3612461) (@lem3612458 _92445 x s h1 h2)). Qed.
Lemma lem3612507 {_92445 : Type'} (s : type686 _92445) (h1 : term131 _92445 s) : term31 _92445 s.
Proof. exact (proj1 (@lem3611560 _92445 s h1)). Qed.
Lemma lem3612508 {_92445 : Type'} (s : type686 _92445) (h1 : term131 _92445 s) : term270 _92445 s.
Proof. exact (fun h0 : term142 _92445 s => @lem3612507 _92445 s h1). Qed.
Lemma lem3612510 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612511 {_92445 : Type'} (s : type686 _92445) : (term270 _92445 s) = (term31 _92445 s).
Proof. exact (@lem3612510 (term31 _92445 s)). Qed.
Lemma lem3612512 {_92445 : Type'} (s : type686 _92445) (h1 : term131 _92445 s) : term31 _92445 s.
Proof. exact (EQ_MP (@lem3612511 _92445 s) (@lem3612508 _92445 s h1)). Qed.
Lemma lem3612515 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3612517 {_92445 : Type'} (s : type686 _92445) : (term142 _92445 s) = (term271 _92445 s).
Proof. exact (@lem3612515 (term31 _92445 s)). Qed.
Lemma lem3612520 {_92445 : Type'} (s : type686 _92445) (h1 : term142 _92445 s) : term271 _92445 s.
Proof. exact (EQ_MP (@lem3612517 _92445 s) (@lem3611979 _92445 s h1)). Qed.
Lemma lem3612523 {_92445 : Type'} (s : type686 _92445) (h1 : term142 _92445 s) (h2 : term131 _92445 s) : False.
Proof. exact (@lem3612520 _92445 s h1 (@lem3612512 _92445 s h2)). Qed.
Lemma lem3612524 {_92445 : Type'} (s : type686 _92445) (h1 : term142 _92445 s) (h2 : term131 _92445 s) : term249.
Proof. exact (fun h0 : ~ False => @lem3612523 _92445 s h1 h2). Qed.
Lemma lem3612526 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612527 : term249 = False.
Proof. exact (@lem3612526 False). Qed.
Lemma lem3612528 {_92445 : Type'} (s : type686 _92445) (h1 : term142 _92445 s) (h2 : term131 _92445 s) : False.
Proof. exact (EQ_MP (@lem3612527) (@lem3612524 _92445 s h1 h2)). Qed.
Lemma lem3612530 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : @FINITE _92445 x.
Proof. exact (proj1 (@lem3611585 _92445 x s t h1)). Qed.
Lemma lem3612531 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term246 _92445 x.
Proof. exact (fun h0 : term238 _92445 x => @lem3612530 _92445 x s t h1). Qed.
Lemma lem3612533 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612534 {_92445 : Type'} (x : _92445 -> Prop) : (term246 _92445 x) = (@FINITE _92445 x).
Proof. exact (@lem3612533 (@FINITE _92445 x)). Qed.
Lemma lem3612535 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : @FINITE _92445 x.
Proof. exact (EQ_MP (@lem3612534 _92445 x) (@lem3612531 _92445 x s t h1)). Qed.
Lemma lem3612538 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3612540 {_92445 : Type'} (x : _92445 -> Prop) : (term238 _92445 x) = (term248 _92445 x).
Proof. exact (@lem3612538 (@FINITE _92445 x)). Qed.
Lemma lem3612543 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : term248 _92445 x.
Proof. exact (EQ_MP (@lem3612540 _92445 x) (@lem3612211 _92445 s t x h1 h2)). Qed.
Lemma lem3612546 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : False.
Proof. exact (@lem3612543 _92445 s t x h1 h2 (@lem3612535 _92445 x s t h1)). Qed.
Lemma lem3612547 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : term249.
Proof. exact (fun h0 : ~ False => @lem3612546 _92445 s t x h1 h2). Qed.
Lemma lem3612549 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612550 : term249 = False.
Proof. exact (@lem3612549 False). Qed.
Lemma lem3612553 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term31 _92445 s.
Proof. exact (proj2 (@lem3611585 _92445 x s t h1)). Qed.
Lemma lem3612554 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term270 _92445 s.
Proof. exact (fun h0 : term142 _92445 s => @lem3612553 _92445 x s t h1). Qed.
Lemma lem3612556 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612557 {_92445 : Type'} (s : type686 _92445) : (term270 _92445 s) = (term31 _92445 s).
Proof. exact (@lem3612556 (term31 _92445 s)). Qed.
Lemma lem3612558 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term208 _92445 x s t) : term31 _92445 s.
Proof. exact (EQ_MP (@lem3612557 _92445 s) (@lem3612554 _92445 x s t h1)). Qed.
Lemma lem3612561 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3612563 {_92445 : Type'} (s : type686 _92445) : (term142 _92445 s) = (term271 _92445 s).
Proof. exact (@lem3612561 (term31 _92445 s)). Qed.
Lemma lem3612566 {_92445 : Type'} (s : type686 _92445) (t' : _92445 -> Prop) (h1 : term149 _92445 s t') : term271 _92445 s.
Proof. exact (EQ_MP (@lem3612563 _92445 s) (@lem3612007 _92445 s t' h1)). Qed.
Lemma lem3612569 {_92445 : Type'} (t' : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term149 _92445 s t') (h2 : term208 _92445 x s t) : False.
Proof. exact (@lem3612566 _92445 s t' h1 (@lem3612558 _92445 x s t h2)). Qed.
Lemma lem3612570 {_92445 : Type'} (t' : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term149 _92445 s t') (h2 : term208 _92445 x s t) : term249.
Proof. exact (fun h0 : ~ False => @lem3612569 _92445 t' x s t h1 h2). Qed.
Lemma lem3612572 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612573 : term249 = False.
Proof. exact (@lem3612572 False). Qed.
Lemma lem3612574 {_92445 : Type'} (t' : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term149 _92445 s t') (h2 : term208 _92445 x s t) : False.
Proof. exact (EQ_MP (@lem3612573) (@lem3612570 _92445 t' x s t h1 h2)). Qed.
Lemma lem3612619 {_92445 : Type'} (x : _92445 -> Prop) : x = x.
Proof. exact (@lem21386 (_92445 -> Prop) x). Qed.
Lemma lem3612620 {_92445 : Type'} (x : _92445 -> Prop) : x = x.
Proof. exact (@lem3612619 _92445 x). Qed.
Lemma lem3612621 {_92445 : Type'} (x : _92445 -> Prop) : term259 _92445 x.
Proof. exact (fun h0 : term260 _92445 x => @lem3612620 _92445 x). Qed.
Lemma lem3612623 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612624 {_92445 : Type'} (x : _92445 -> Prop) : (term259 _92445 x) = (x = x).
Proof. exact (@lem3612623 (x = x)). Qed.
Lemma lem3612625 {_92445 : Type'} (x : _92445 -> Prop) : x = x.
Proof. exact (EQ_MP (@lem3612624 _92445 x) (@lem3612621 _92445 x)). Qed.
Lemma lem3612631 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3612632 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) : (term241 _92445 x _39146) = (term261 _92445 _39146 x).
Proof. exact (@lem3612631 (@FINITE _92445 _39146) (term234 _92445 _39146 x)). Qed.
Lemma lem3612640 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3612641 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) : (term262 _92445 x _39146) = (term263 _92445 _39146 x).
Proof. exact (MK_COMB (@lem3612640) (@lem3612632 _92445 _39146 x)). Qed.
Lemma lem3612649 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) : (term261 _92445 _39146 x) = (term261 _92445 _39146 x).
Proof. exact (eq_refl (term261 _92445 _39146 x)). Qed.
Lemma lem3612650 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) : ((term241 _92445 x _39146) = (term261 _92445 _39146 x)) = ((term261 _92445 _39146 x) = (term261 _92445 _39146 x)).
Proof. exact (MK_COMB (@lem3612641 _92445 _39146 x) (@lem3612649 _92445 _39146 x)). Qed.
Lemma lem3612652 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3612653 (x : Prop) : (x = x) = True.
Proof. exact (@lem3612652 Prop x). Qed.
Lemma lem3612654 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) : ((term261 _92445 _39146 x) = (term261 _92445 _39146 x)) = True.
Proof. exact (@lem3612653 (term261 _92445 _39146 x)). Qed.
Lemma lem3612655 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) : ((term241 _92445 x _39146) = (term261 _92445 _39146 x)) = True.
Proof. exact (TRANS (@lem3612650 _92445 _39146 x) (@lem3612654 _92445 _39146 x)). Qed.
Lemma lem3612656 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) : True = ((term241 _92445 x _39146) = (term261 _92445 _39146 x)).
Proof. exact (SYM (@lem3612655 _92445 _39146 x)). Qed.
Lemma lem3612657 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) : (term241 _92445 x _39146) = (term261 _92445 _39146 x).
Proof. exact (EQ_MP (@lem3612656 _92445 _39146 x) (@lem0)). Qed.
Lemma lem3612658 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term261 _92445 _39146 x.
Proof. exact (EQ_MP (@lem3612657 _92445 _39146 x) (@lem3612033 _92445 _39146 x s h1)). Qed.
Lemma lem3612660 (b : Prop) (a : Prop) : (a \/ b) = (term254 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3612661 {_92445 : Type'} (x : _92445 -> Prop) (_39146 : _92445 -> Prop) : (term261 _92445 _39146 x) = (term264 _92445 x _39146).
Proof. exact (@lem3612660 (term234 _92445 _39146 x) (@FINITE _92445 _39146)). Qed.
Lemma lem3612663 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3612664 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) : (term265 _92445 _39146 x) = (_39146 = x).
Proof. exact (@lem3612663 (_39146 = x)). Qed.
Lemma lem3612665 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3612666 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) : (term266 _92445 _39146 x) = (term267 _92445 _39146 x).
Proof. exact (MK_COMB (@lem3612665) (@lem3612664 _92445 _39146 x)). Qed.
Lemma lem3612667 {_92445 : Type'} (_39146 : _92445 -> Prop) : (@FINITE _92445 _39146) = (@FINITE _92445 _39146).
Proof. exact (eq_refl (@FINITE _92445 _39146)). Qed.
Lemma lem3612668 {_92445 : Type'} (x : _92445 -> Prop) (_39146 : _92445 -> Prop) : (term264 _92445 x _39146) = (term268 _92445 x _39146).
Proof. exact (MK_COMB (@lem3612666 _92445 _39146 x) (@lem3612667 _92445 _39146)). Qed.
Lemma lem3612669 {_92445 : Type'} (x : _92445 -> Prop) (_39146 : _92445 -> Prop) : (term261 _92445 _39146 x) = (term268 _92445 x _39146).
Proof. exact (TRANS (@lem3612661 _92445 x _39146) (@lem3612668 _92445 x _39146)). Qed.
Lemma lem3612672 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term268 _92445 x _39146.
Proof. exact (EQ_MP (@lem3612669 _92445 x _39146) (@lem3612658 _92445 _39146 x s h1)). Qed.
Lemma lem3612673 {_92445 : Type'} (_39146 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term268 _92445 x _39146.
Proof. exact (@lem3612672 _92445 _39146 x s h1). Qed.
Lemma lem3612674 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term269 _92445 x.
Proof. exact (@lem3612673 _92445 x x s h1). Qed.
Lemma lem3612677 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : @FINITE _92445 x.
Proof. exact (@lem3612674 _92445 x s h1 (@lem3612625 _92445 x)). Qed.
Lemma lem3612678 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term246 _92445 x.
Proof. exact (fun h0 : term238 _92445 x => @lem3612677 _92445 x s h1). Qed.
Lemma lem3612680 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612681 {_92445 : Type'} (x : _92445 -> Prop) : (term246 _92445 x) = (@FINITE _92445 x).
Proof. exact (@lem3612680 (@FINITE _92445 x)). Qed.
Lemma lem3612682 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : @FINITE _92445 x.
Proof. exact (EQ_MP (@lem3612681 _92445 x) (@lem3612678 _92445 x s h1)). Qed.
Lemma lem3612685 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3612687 {_92445 : Type'} (x : _92445 -> Prop) : (term238 _92445 x) = (term248 _92445 x).
Proof. exact (@lem3612685 (@FINITE _92445 x)). Qed.
Lemma lem3612690 {_92445 : Type'} (x : _92445 -> Prop) (h1 : term238 _92445 x) : term248 _92445 x.
Proof. exact (EQ_MP (@lem3612687 _92445 x) (@lem3612027 _92445 x h1)). Qed.
Lemma lem3612693 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : False.
Proof. exact (@lem3612690 _92445 x h1 (@lem3612682 _92445 x s h2)). Qed.
Lemma lem3612694 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : term249.
Proof. exact (fun h0 : ~ False => @lem3612693 _92445 x s h1 h2). Qed.
Lemma lem3612696 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612697 : term249 = False.
Proof. exact (@lem3612696 False). Qed.
Lemma lem3612698 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : False.
Proof. exact (EQ_MP (@lem3612697) (@lem3612694 _92445 x s h1 h2)). Qed.
Lemma lem3612743 {_92445 : Type'} (s : type686 _92445) (t' : _92445 -> Prop) (h1 : term149 _92445 s t') : @IN (_92445 -> Prop) t' s.
Proof. exact (proj1 (@lem3611578 _92445 s t' h1)). Qed.
Lemma lem3612744 {_92445 : Type'} (s : type686 _92445) (t' : _92445 -> Prop) (h1 : term149 _92445 s t') : term250 _92445 t' s.
Proof. exact (fun h0 : term235 _92445 t' s => @lem3612743 _92445 s t' h1). Qed.
Lemma lem3612746 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612747 {_92445 : Type'} (t' : _92445 -> Prop) (s : type686 _92445) : (term250 _92445 t' s) = (@IN (_92445 -> Prop) t' s).
Proof. exact (@lem3612746 (@IN (_92445 -> Prop) t' s)). Qed.
Lemma lem3612748 {_92445 : Type'} (s : type686 _92445) (t' : _92445 -> Prop) (h1 : term149 _92445 s t') : @IN (_92445 -> Prop) t' s.
Proof. exact (EQ_MP (@lem3612747 _92445 t' s) (@lem3612744 _92445 s t' h1)). Qed.
Lemma lem3612754 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3612755 {_92445 : Type'} (_39147 : _92445 -> Prop) (s : type686 _92445) : (term114 _92445 s _39147) = (term251 _92445 _39147 s).
Proof. exact (@lem3612754 (@FINITE _92445 _39147) (term235 _92445 _39147 s)). Qed.
Lemma lem3612761 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3612762 {_92445 : Type'} (_39147 : _92445 -> Prop) (s : type686 _92445) : (term252 _92445 s _39147) = (term253 _92445 _39147 s).
Proof. exact (MK_COMB (@lem3612761) (@lem3612755 _92445 _39147 s)). Qed.
Lemma lem3612768 {_92445 : Type'} (_39147 : _92445 -> Prop) (s : type686 _92445) : (term251 _92445 _39147 s) = (term251 _92445 _39147 s).
Proof. exact (eq_refl (term251 _92445 _39147 s)). Qed.
Lemma lem3612769 {_92445 : Type'} (_39147 : _92445 -> Prop) (s : type686 _92445) : ((term114 _92445 s _39147) = (term251 _92445 _39147 s)) = ((term251 _92445 _39147 s) = (term251 _92445 _39147 s)).
Proof. exact (MK_COMB (@lem3612762 _92445 _39147 s) (@lem3612768 _92445 _39147 s)). Qed.
Lemma lem3612771 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3612772 (x : Prop) : (x = x) = True.
Proof. exact (@lem3612771 Prop x). Qed.
Lemma lem3612773 {_92445 : Type'} (_39147 : _92445 -> Prop) (s : type686 _92445) : ((term251 _92445 _39147 s) = (term251 _92445 _39147 s)) = True.
Proof. exact (@lem3612772 (term251 _92445 _39147 s)). Qed.
Lemma lem3612774 {_92445 : Type'} (_39147 : _92445 -> Prop) (s : type686 _92445) : ((term114 _92445 s _39147) = (term251 _92445 _39147 s)) = True.
Proof. exact (TRANS (@lem3612769 _92445 _39147 s) (@lem3612773 _92445 _39147 s)). Qed.
Lemma lem3612775 {_92445 : Type'} (_39147 : _92445 -> Prop) (s : type686 _92445) : True = ((term114 _92445 s _39147) = (term251 _92445 _39147 s)).
Proof. exact (SYM (@lem3612774 _92445 _39147 s)). Qed.
Lemma lem3612776 {_92445 : Type'} (_39147 : _92445 -> Prop) (s : type686 _92445) : (term114 _92445 s _39147) = (term251 _92445 _39147 s).
Proof. exact (EQ_MP (@lem3612775 _92445 _39147 s) (@lem0)). Qed.
Lemma lem3612777 {_92445 : Type'} (_39147 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term251 _92445 _39147 s.
Proof. exact (EQ_MP (@lem3612776 _92445 _39147 s) (@lem3612059 _92445 _39147 x s h1)). Qed.
Lemma lem3612779 (b : Prop) (a : Prop) : (a \/ b) = (term254 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3612780 {_92445 : Type'} (s : type686 _92445) (_39147 : _92445 -> Prop) : (term251 _92445 _39147 s) = (term255 _92445 s _39147).
Proof. exact (@lem3612779 (term235 _92445 _39147 s) (@FINITE _92445 _39147)). Qed.
Lemma lem3612782 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3612783 {_92445 : Type'} (_39147 : _92445 -> Prop) (s : type686 _92445) : (term256 _92445 _39147 s) = (@IN (_92445 -> Prop) _39147 s).
Proof. exact (@lem3612782 (@IN (_92445 -> Prop) _39147 s)). Qed.
Lemma lem3612784 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3612785 {_92445 : Type'} (_39147 : _92445 -> Prop) (s : type686 _92445) : (term257 _92445 _39147 s) = (term258 _92445 _39147 s).
Proof. exact (MK_COMB (@lem3612784) (@lem3612783 _92445 _39147 s)). Qed.
Lemma lem3612786 {_92445 : Type'} (_39147 : _92445 -> Prop) : (@FINITE _92445 _39147) = (@FINITE _92445 _39147).
Proof. exact (eq_refl (@FINITE _92445 _39147)). Qed.
Lemma lem3612787 {_92445 : Type'} (s : type686 _92445) (_39147 : _92445 -> Prop) : (term255 _92445 s _39147) = (term107 _92445 s _39147).
Proof. exact (MK_COMB (@lem3612785 _92445 _39147 s) (@lem3612786 _92445 _39147)). Qed.
Lemma lem3612788 {_92445 : Type'} (s : type686 _92445) (_39147 : _92445 -> Prop) : (term251 _92445 _39147 s) = (term107 _92445 s _39147).
Proof. exact (TRANS (@lem3612780 _92445 s _39147) (@lem3612787 _92445 s _39147)). Qed.
Lemma lem3612791 {_92445 : Type'} (_39147 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term107 _92445 s _39147.
Proof. exact (EQ_MP (@lem3612788 _92445 s _39147) (@lem3612777 _92445 _39147 x s h1)). Qed.
Lemma lem3612792 {_92445 : Type'} (_39147 : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term107 _92445 s _39147.
Proof. exact (@lem3612791 _92445 _39147 x s h1). Qed.
Lemma lem3612793 {_92445 : Type'} (t' : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term192 _92445 x s) : term107 _92445 s t'.
Proof. exact (@lem3612792 _92445 t' x s h1). Qed.
Lemma lem3612796 {_92445 : Type'} (t' : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term149 _92445 s t') (h2 : term192 _92445 x s) : @FINITE _92445 t'.
Proof. exact (@lem3612793 _92445 t' x s h2 (@lem3612748 _92445 s t' h1)). Qed.
Lemma lem3612797 {_92445 : Type'} (t' : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term149 _92445 s t') (h2 : term192 _92445 x s) : term246 _92445 t'.
Proof. exact (fun h0 : term238 _92445 t' => @lem3612796 _92445 t' x s h1 h2). Qed.
Lemma lem3612799 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612800 {_92445 : Type'} (t' : _92445 -> Prop) : (term246 _92445 t') = (@FINITE _92445 t').
Proof. exact (@lem3612799 (@FINITE _92445 t')). Qed.
Lemma lem3612801 {_92445 : Type'} (t' : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term149 _92445 s t') (h2 : term192 _92445 x s) : @FINITE _92445 t'.
Proof. exact (EQ_MP (@lem3612800 _92445 t') (@lem3612797 _92445 t' x s h1 h2)). Qed.
Lemma lem3612804 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3612806 {_92445 : Type'} (t' : _92445 -> Prop) : (term238 _92445 t') = (term248 _92445 t').
Proof. exact (@lem3612804 (@FINITE _92445 t')). Qed.
Lemma lem3612809 {_92445 : Type'} (s : type686 _92445) (t' : _92445 -> Prop) (h1 : term149 _92445 s t') : term248 _92445 t'.
Proof. exact (EQ_MP (@lem3612806 _92445 t') (@lem3612045 _92445 s t' h1)). Qed.
Lemma lem3612812 {_92445 : Type'} (t' : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term149 _92445 s t') (h2 : term192 _92445 x s) : False.
Proof. exact (@lem3612809 _92445 s t' h1 (@lem3612801 _92445 t' x s h1 h2)). Qed.
Lemma lem3612813 {_92445 : Type'} (t' : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term149 _92445 s t') (h2 : term192 _92445 x s) : term249.
Proof. exact (fun h0 : ~ False => @lem3612812 _92445 t' x s h1 h2). Qed.
Lemma lem3612815 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3612816 : term249 = False.
Proof. exact (@lem3612815 False). Qed.
Lemma lem3612817 {_92445 : Type'} (t' : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term149 _92445 s t') (h2 : term192 _92445 x s) : False.
Proof. exact (EQ_MP (@lem3612816) (@lem3612813 _92445 t' x s h1 h2)). Qed.
Lemma lem3612818 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : False.
Proof. exact (EQ_MP (@lem3612550) (@lem3612547 _92445 s t x h1 h2)). Qed.
Lemma lem3612819 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : False.
Proof. exact (EQ_MP (@lem3612261) (@lem3612258 _92445 s t x h1 h2)). Qed.
Lemma lem3612820 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : (term238 _92445 x) = False.
Proof. exact (prop_ext (fun h3 : term238 _92445 x => @lem3612698 _92445 x s h1 h2) (fun h3 : False => @lem3612027 _92445 x h1)). Qed.
Lemma lem3612821 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : False.
Proof. exact (EQ_MP (@lem3612820 _92445 x s h1 h2) (@lem3612027 _92445 x h1)). Qed.
Lemma lem3612822 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : (t = x) = False.
Proof. exact (prop_ext (fun h3 : t = x => @lem3612818 _92445 s t x h1 h2) (fun h3 : False => @lem3612005 _92445 t x h2)). Qed.
Lemma lem3612823 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : False.
Proof. exact (EQ_MP (@lem3612822 _92445 s t x h1 h2) (@lem3612005 _92445 t x h2)). Qed.
Lemma lem3612824 {_92445 : Type'} (s : type686 _92445) (h1 : term142 _92445 s) (h2 : term131 _92445 s) : (term142 _92445 s) = False.
Proof. exact (prop_ext (fun h3 : term142 _92445 s => @lem3612528 _92445 s h1 h2) (fun h3 : False => @lem3611979 _92445 s h1)). Qed.
Lemma lem3612825 {_92445 : Type'} (s : type686 _92445) (h1 : term142 _92445 s) (h2 : term131 _92445 s) : False.
Proof. exact (EQ_MP (@lem3612824 _92445 s h1 h2) (@lem3611979 _92445 s h1)). Qed.
Lemma lem3612826 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : (term238 _92445 x) = False.
Proof. exact (prop_ext (fun h3 : term238 _92445 x => @lem3612462 _92445 x s h1 h2) (fun h3 : False => @lem3611957 _92445 x h1)). Qed.
Lemma lem3612827 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : False.
Proof. exact (EQ_MP (@lem3612826 _92445 x s h1 h2) (@lem3611957 _92445 x h1)). Qed.
Lemma lem3612828 {_92445 : Type'} (x : _92445 -> Prop) (t : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) (h2 : term208 _92445 x s t) (h3 : @IN (_92445 -> Prop) t s) : (@IN (_92445 -> Prop) t s) = False.
Proof. exact (prop_ext (fun h4 : @IN (_92445 -> Prop) t s => @lem3612338 _92445 x t s h1 h2 h3) (fun h4 : False => @lem3611947 _92445 t s h3)). Qed.
Lemma lem3612829 {_92445 : Type'} (x : _92445 -> Prop) (t : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) (h2 : term208 _92445 x s t) (h3 : @IN (_92445 -> Prop) t s) : False.
Proof. exact (EQ_MP (@lem3612828 _92445 x t s h1 h2 h3) (@lem3611947 _92445 t s h3)). Qed.
Lemma lem3612830 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : (t = x) = False.
Proof. exact (prop_ext (fun h3 : t = x => @lem3612819 _92445 s t x h1 h2) (fun h3 : False => @lem3611931 _92445 t x h2)). Qed.
Lemma lem3612831 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : False.
Proof. exact (EQ_MP (@lem3612830 _92445 s t x h1 h2) (@lem3611931 _92445 t x h2)). Qed.
Lemma lem3612832 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : (term238 _92445 x) = False.
Proof. exact (prop_ext (fun h3 : term238 _92445 x => @lem3612821 _92445 x s h1 h2) (fun h3 : False => @lem3611844 _92445 x h1)). Qed.
Lemma lem3612833 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : False.
Proof. exact (EQ_MP (@lem3612832 _92445 x s h1 h2) (@lem3611844 _92445 x h1)). Qed.
Lemma lem3612834 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : (t = x) = False.
Proof. exact (prop_ext (fun h3 : t = x => @lem3612823 _92445 s t x h1 h2) (fun h3 : False => @lem3611777 _92445 t x h2)). Qed.
Lemma lem3612835 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : False.
Proof. exact (EQ_MP (@lem3612834 _92445 s t x h1 h2) (@lem3611777 _92445 t x h2)). Qed.
Lemma lem3612836 {_92445 : Type'} (s : type686 _92445) (h1 : term142 _92445 s) (h2 : term131 _92445 s) : (term142 _92445 s) = False.
Proof. exact (prop_ext (fun h3 : term142 _92445 s => @lem3612825 _92445 s h1 h2) (fun h3 : False => @lem3611749 _92445 s h1)). Qed.
Lemma lem3612837 {_92445 : Type'} (s : type686 _92445) (h1 : term142 _92445 s) (h2 : term131 _92445 s) : False.
Proof. exact (EQ_MP (@lem3612836 _92445 s h1 h2) (@lem3611749 _92445 s h1)). Qed.
Lemma lem3612838 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : (term238 _92445 x) = False.
Proof. exact (prop_ext (fun h3 : term238 _92445 x => @lem3612827 _92445 x s h1 h2) (fun h3 : False => @lem3611705 _92445 x h1)). Qed.
Lemma lem3612839 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : False.
Proof. exact (EQ_MP (@lem3612838 _92445 x s h1 h2) (@lem3611705 _92445 x h1)). Qed.
Lemma lem3612840 {_92445 : Type'} (x : _92445 -> Prop) (t : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) (h2 : term208 _92445 x s t) (h3 : @IN (_92445 -> Prop) t s) : (@IN (_92445 -> Prop) t s) = False.
Proof. exact (prop_ext (fun h4 : @IN (_92445 -> Prop) t s => @lem3612829 _92445 x t s h1 h2 h3) (fun h4 : False => @lem3611661 _92445 t s h3)). Qed.
Lemma lem3612841 {_92445 : Type'} (x : _92445 -> Prop) (t : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) (h2 : term208 _92445 x s t) (h3 : @IN (_92445 -> Prop) t s) : False.
Proof. exact (EQ_MP (@lem3612840 _92445 x t s h1 h2 h3) (@lem3611661 _92445 t s h3)). Qed.
Lemma lem3612842 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : (t = x) = False.
Proof. exact (prop_ext (fun h3 : t = x => @lem3612831 _92445 s t x h1 h2) (fun h3 : False => @lem3611628 _92445 t x h2)). Qed.
Lemma lem3612843 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : False.
Proof. exact (EQ_MP (@lem3612842 _92445 s t x h1 h2) (@lem3611628 _92445 t x h2)). Qed.
Lemma lem3612844 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : (term238 _92445 x) = False.
Proof. exact (prop_ext (fun h3 : term238 _92445 x => @lem3612833 _92445 x s h1 h2) (fun h3 : False => @lem3611844 _92445 x h1)). Qed.
Lemma lem3612845 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : False.
Proof. exact (EQ_MP (@lem3612844 _92445 x s h1 h2) (@lem3611844 _92445 x h1)). Qed.
Lemma lem3612846 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : (t = x) = False.
Proof. exact (prop_ext (fun h3 : t = x => @lem3612835 _92445 s t x h1 h2) (fun h3 : False => @lem3611777 _92445 t x h2)). Qed.
Lemma lem3612847 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : False.
Proof. exact (EQ_MP (@lem3612846 _92445 s t x h1 h2) (@lem3611777 _92445 t x h2)). Qed.
Lemma lem3612848 {_92445 : Type'} (s : type686 _92445) (h1 : term142 _92445 s) (h2 : term131 _92445 s) : (term142 _92445 s) = False.
Proof. exact (prop_ext (fun h3 : term142 _92445 s => @lem3612837 _92445 s h1 h2) (fun h3 : False => @lem3611749 _92445 s h1)). Qed.
Lemma lem3612849 {_92445 : Type'} (s : type686 _92445) (h1 : term142 _92445 s) (h2 : term131 _92445 s) : False.
Proof. exact (EQ_MP (@lem3612848 _92445 s h1 h2) (@lem3611749 _92445 s h1)). Qed.
Lemma lem3612850 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : (term238 _92445 x) = False.
Proof. exact (prop_ext (fun h3 : term238 _92445 x => @lem3612839 _92445 x s h1 h2) (fun h3 : False => @lem3611705 _92445 x h1)). Qed.
Lemma lem3612851 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term238 _92445 x) (h2 : term192 _92445 x s) : False.
Proof. exact (EQ_MP (@lem3612850 _92445 x s h1 h2) (@lem3611705 _92445 x h1)). Qed.
Lemma lem3612852 {_92445 : Type'} (x : _92445 -> Prop) (t : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) (h2 : term208 _92445 x s t) (h3 : @IN (_92445 -> Prop) t s) : (@IN (_92445 -> Prop) t s) = False.
Proof. exact (prop_ext (fun h4 : @IN (_92445 -> Prop) t s => @lem3612841 _92445 x t s h1 h2 h3) (fun h4 : False => @lem3611661 _92445 t s h3)). Qed.
Lemma lem3612853 {_92445 : Type'} (x : _92445 -> Prop) (t : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) (h2 : term208 _92445 x s t) (h3 : @IN (_92445 -> Prop) t s) : False.
Proof. exact (EQ_MP (@lem3612852 _92445 x t s h1 h2 h3) (@lem3611661 _92445 t s h3)). Qed.
Lemma lem3612854 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : (t = x) = False.
Proof. exact (prop_ext (fun h3 : t = x => @lem3612843 _92445 s t x h1 h2) (fun h3 : False => @lem3611628 _92445 t x h2)). Qed.
Lemma lem3612855 {_92445 : Type'} (s : type686 _92445) (t : _92445 -> Prop) (x : _92445 -> Prop) (h1 : term208 _92445 x s t) (h2 : t = x) : False.
Proof. exact (EQ_MP (@lem3612854 _92445 s t x h1 h2) (@lem3611628 _92445 t x h2)). Qed.
Lemma lem3612856 {_92445 : Type'} (t' : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term149 _92445 s t') (h2 : term192 _92445 x s) : False.
Proof. exact (or_elim (@lem3611593 _92445 x s h2) (fun h0 : term238 _92445 x => @lem3612845 _92445 x s h0 h2) (fun h0 : term142 _92445 s => @lem3612817 _92445 t' x s h1 h2)). Qed.
Lemma lem3612857 {_92445 : Type'} (t' : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term149 _92445 s t') (h2 : term208 _92445 x s t) : False.
Proof. exact (or_elim (@lem3611587 _92445 x s t h2) (fun h0 : t = x => @lem3612847 _92445 s t x h2 h0) (fun h0 : @IN (_92445 -> Prop) t s => @lem3612574 _92445 t' x s t h1 h2)). Qed.
Lemma lem3612858 {_92445 : Type'} (t' : _92445 -> Prop) (t : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term149 _92445 s t') (h2 : term229 _92445 t x s) : False.
Proof. exact (or_elim (@lem3611508 _92445 t x s h2) (fun h0 : term208 _92445 x s t => @lem3612857 _92445 t' x s t h1 h0) (fun h0 : term192 _92445 x s => @lem3612856 _92445 t' x s h1 h0)). Qed.
Lemma lem3612859 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) (h2 : term192 _92445 x s) : False.
Proof. exact (or_elim (@lem3611575 _92445 x s h2) (fun h0 : term238 _92445 x => @lem3612851 _92445 x s h0 h2) (fun h0 : term142 _92445 s => @lem3612849 _92445 s h0 h1)). Qed.
Lemma lem3612860 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (t : _92445 -> Prop) (h1 : term131 _92445 s) (h2 : term208 _92445 x s t) : False.
Proof. exact (or_elim (@lem3611569 _92445 x s t h2) (fun h0 : t = x => @lem3612855 _92445 s t x h2 h0) (fun h0 : @IN (_92445 -> Prop) t s => @lem3612853 _92445 x t s h1 h2 h0)). Qed.
Lemma lem3612861 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term131 _92445 s) (h2 : term229 _92445 t x s) : False.
Proof. exact (or_elim (@lem3611508 _92445 t x s h2) (fun h0 : term208 _92445 x s t => @lem3612860 _92445 x s t h1 h0) (fun h0 : term192 _92445 x s => @lem3612859 _92445 x s h1 h0)). Qed.
Lemma lem3612862 {_92445 : Type'} (t' : _92445 -> Prop) (t : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term166 _92445 s t') (h2 : term229 _92445 t x s) : False.
Proof. exact (or_elim (@lem3611559 _92445 s t' h1) (fun h0 : term131 _92445 s => @lem3612861 _92445 t x s h0 h2) (fun h0 : term149 _92445 s t' => @lem3612858 _92445 t' t x s h0 h2)). Qed.
Lemma lem3612863 {_92445 : Type'} (t' : _92445 -> Prop) (t : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term166 _92445 s t') (h2 : term229 _92445 t x s) : (term166 _92445 s t') = False.
Proof. exact (prop_ext (fun h3 : term166 _92445 s t' => @lem3612862 _92445 t' t x s h1 h2) (fun h3 : False => @lem3611559 _92445 s t' h1)). Qed.
Lemma lem3612864 {_92445 : Type'} (t' : _92445 -> Prop) (t : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term166 _92445 s t') (h2 : term229 _92445 t x s) : False.
Proof. exact (EQ_MP (@lem3612863 _92445 t' t x s h1 h2) (@lem3611559 _92445 s t' h1)). Qed.
Lemma lem3612865 {_92445 : Type'} (t' : _92445 -> Prop) (t : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term166 _92445 s t') (h2 : term229 _92445 t x s) : (term229 _92445 t x s) = False.
Proof. exact (prop_ext (fun h3 : term229 _92445 t x s => @lem3612864 _92445 t' t x s h1 h2) (fun h3 : False => @lem3611508 _92445 t x s h2)). Qed.
Lemma lem3612866 {_92445 : Type'} (t' : _92445 -> Prop) (t : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : term166 _92445 s t') (h2 : term229 _92445 t x s) : False.
Proof. exact (EQ_MP (@lem3612865 _92445 t' t x s h1 h2) (@lem3611508 _92445 t x s h2)). Qed.
Lemma lem3612867 {_92445 : Type'} (t : _92445 -> Prop) (x : _92445 -> Prop) (s : type686 _92445) (h1 : (term31 _92445 s) = (term32 _92445 s)) (h2 : term229 _92445 t x s) : False.
Proof. exact (ex_elim (@lem3611230 _92445 s h1) (fun t' : _92445 -> Prop => fun h0 : term168 _92445 s t' => @lem3612866 _92445 t' t x s h0 h2)). Qed.
Lemma lem3612868 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term111 _92445 x s) (h2 : (term31 _92445 s) = (term32 _92445 s)) : False.
Proof. exact (ex_elim (@lem3611423 _92445 x s h1) (fun t : _92445 -> Prop => fun h0 : term231 _92445 x s t => @lem3612867 _92445 t x s h2 h0)). Qed.
Lemma lem3612869 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term111 _92445 x s) (h2 : (term31 _92445 s) = (term32 _92445 s)) : (term111 _92445 x s) = False.
Proof. exact (prop_ext (fun h3 : term111 _92445 x s => @lem3612868 _92445 x s h1 h2) (fun h3 : False => @lem3611063 _92445 x s h1)). Qed.
Lemma lem3612870 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : term111 _92445 x s) (h2 : (term31 _92445 s) = (term32 _92445 s)) : False.
Proof. exact (EQ_MP (@lem3612869 _92445 x s h1 h2) (@lem3611063 _92445 x s h1)). Qed.
Lemma lem3612871 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : (term31 _92445 s) = (term32 _92445 s)) : term110 _92445 x s.
Proof. exact (fun h0 : term111 _92445 x s => @lem3612870 _92445 x s h0 h1). Qed.
Lemma lem3612872 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) (h1 : (term31 _92445 s) = (term32 _92445 s)) : (term91 _92445 x s) = (term84 _92445 x s).
Proof. exact (EQ_MP (@lem3611062 _92445 x s) (@lem3612871 _92445 x s h1)). Qed.
Lemma lem3612873 {_92445 : Type'} (x : _92445 -> Prop) (s : type686 _92445) : term93 _92445 x s.
Proof. exact (fun h0 : (term31 _92445 s) = (term32 _92445 s) => @lem3612872 _92445 x s h0). Qed.
Lemma lem3612878 {_92445 : Type'} (x : _92445 -> Prop) : term95 _92445 x.
Proof. exact (fun s : type686 _92445 => @lem3612873 _92445 x s). Qed.
Lemma lem3612883 {_92445 : Type'} : term97 _92445.
Proof. exact (fun x : _92445 -> Prop => @lem3612878 _92445 x). Qed.
Lemma lem3612884 {_92445 : Type'} : term100 _92445.
Proof. exact (EQ_MP (@lem3611057 _92445) (@lem3612883 _92445)). Qed.
Lemma lem3612886 {_92445 : Type'} : term100 _92445.
Proof. exact (@lem3610941 _92445 (@lem3612884 _92445)). Qed.
Lemma lem3612887 {_92445 : Type'} (h1 : term101 _92445) : False.
Proof. exact (@lem3612886 _92445 (@lem3610925 _92445 h1)). Qed.
Lemma lem3612888 {_92445 : Type'} (h1 : term101 _92445) : (term101 _92445) = False.
Proof. exact (prop_ext (fun h2 : term101 _92445 => @lem3612887 _92445 h1) (fun h2 : False => @lem3610925 _92445 h1)). Qed.
Lemma lem3612889 {_92445 : Type'} (h1 : term101 _92445) : False.
Proof. exact (EQ_MP (@lem3612888 _92445 h1) (@lem3610925 _92445 h1)). Qed.
Lemma lem3612890 {_92445 : Type'} : term100 _92445.
Proof. exact (fun h0 : term101 _92445 => @lem3612889 _92445 h0). Qed.
Lemma lem3612891 {_92445 : Type'} : term97 _92445.
Proof. exact (EQ_MP (@lem3610924 _92445) (@lem3612890 _92445)). Qed.
Lemma lem3612892 {_92445 : Type'} : term90 _92445.
Proof. exact (EQ_MP (@lem3610920 _92445) (@lem3612891 _92445)). Qed.
Lemma lem3612893 {_92445 : Type'} : term49 _92445.
Proof. exact (EQ_MP (@lem3610809 _92445) (@lem3612892 _92445)). Qed.
Lemma lem3612894 {_92445 : Type'} : term58 _92445.
Proof. exact (@lem3610681 _92445 (@lem3612893 _92445)). Qed.
