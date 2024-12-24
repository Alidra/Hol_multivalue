Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EMPTY_UNIONS_term_abbrevs.
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
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3328525 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3328526 {_86951 : Type'} (s : _86951 -> Prop) (t : _86951 -> Prop) : (s = t) = (term0 _86951 s t).
Proof. exact (@lem3328525 _86951 s t). Qed.
Lemma lem3328527 {_86951 : Type'} (s : type686 _86951) : ((@UNIONS _86951 s) = (@EMPTY _86951)) = (term1 _86951 s).
Proof. exact (@lem3328526 _86951 (@UNIONS _86951 s) (@EMPTY _86951)). Qed.
Lemma lem3328536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3328537 {_86951 : Type'} (s : type686 _86951) : (term2 _86951 s) = (term3 _86951 s).
Proof. exact (MK_COMB (@lem3328536) (@lem3328527 _86951 s)). Qed.
Lemma lem3328547 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3328548 {_86951 : Type'} (s : _86951 -> Prop) (t : _86951 -> Prop) : (s = t) = (term0 _86951 s t).
Proof. exact (@lem3328547 _86951 s t). Qed.
Lemma lem3328549 {_86951 : Type'} (t : _86951 -> Prop) : (t = (@EMPTY _86951)) = (term4 _86951 t).
Proof. exact (@lem3328548 _86951 t (@EMPTY _86951)). Qed.
Lemma lem3328558 {_86951 : Type'} (t : _86951 -> Prop) (s : type686 _86951) : (term5 _86951 t s) = (term5 _86951 t s).
Proof. exact (eq_refl (term5 _86951 t s)). Qed.
Lemma lem3328559 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term6 _86951 s t) = (term7 _86951 s t).
Proof. exact (MK_COMB (@lem3328558 _86951 t s) (@lem3328549 _86951 t)). Qed.
Lemma lem3328562 {_86951 : Type'} (s : type686 _86951) : (term8 _86951 s) = (term9 _86951 s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3328559 _86951 s t)). Qed.
Lemma lem3328563 {_86951 : Type'} : (@all (_86951 -> Prop)) = (@all (_86951 -> Prop)).
Proof. exact (eq_refl (@all (_86951 -> Prop))). Qed.
Lemma lem3328564 {_86951 : Type'} (s : type686 _86951) : (term10 _86951 s) = (term11 _86951 s).
Proof. exact (MK_COMB (@lem3328563 _86951) (@lem3328562 _86951 s)). Qed.
Lemma lem3328569 {_86951 : Type'} (s : type686 _86951) : (((@UNIONS _86951 s) = (@EMPTY _86951)) = (term10 _86951 s)) = ((term1 _86951 s) = (term11 _86951 s)).
Proof. exact (MK_COMB (@lem3328537 _86951 s) (@lem3328564 _86951 s)). Qed.
Lemma lem3328574 {_86951 : Type'} : (term12 _86951) = (term13 _86951).
Proof. exact (fun_ext (fun s : type686 _86951 => @lem3328569 _86951 s)). Qed.
Lemma lem3328575 {_86951 : Type'} : (@all ((_86951 -> Prop) -> Prop)) = (@all ((_86951 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_86951 -> Prop) -> Prop))). Qed.
Lemma lem3328576 {_86951 : Type'} : (term14 _86951) = (term15 _86951).
Proof. exact (MK_COMB (@lem3328575 _86951) (@lem3328574 _86951)). Qed.
Lemma lem3328581 {_86951 : Type'} : (term15 _86951) = (term14 _86951).
Proof. exact (SYM (@lem3328576 _86951)). Qed.
Lemma lem3328595 {A : Type'} (s : type686 A) (x : A) : (term16 A x s) = (term17 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3328596 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term16 _86951 x s) = (term17 _86951 s x).
Proof. exact (@lem3328595 _86951 s x). Qed.
Lemma lem3328604 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3328605 {_86951 : Type'} (P : type686 _86951) (x : _86951 -> Prop) : (@IN (_86951 -> Prop) x P) = (P x).
Proof. exact (@lem3328604 (_86951 -> Prop) P x). Qed.
Lemma lem3328606 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (@IN (_86951 -> Prop) t s) = (s t).
Proof. exact (@lem3328605 _86951 s t). Qed.
Lemma lem3328607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3328608 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term18 _86951 t s) = (term19 _86951 s t).
Proof. exact (MK_COMB (@lem3328607) (@lem3328606 _86951 s t)). Qed.
Lemma lem3328610 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3328611 {_86951 : Type'} (P : _86951 -> Prop) (x : _86951) : (@IN _86951 x P) = (P x).
Proof. exact (@lem3328610 _86951 P x). Qed.
Lemma lem3328612 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (@IN _86951 x t) = (t x).
Proof. exact (@lem3328611 _86951 t x). Qed.
Lemma lem3328613 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term20 _86951 s x t) = (term21 _86951 s t x).
Proof. exact (MK_COMB (@lem3328608 _86951 s t) (@lem3328612 _86951 t x)). Qed.
Lemma lem3328616 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term22 _86951 s x) = (term23 _86951 s x).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3328613 _86951 s t x)). Qed.
Lemma lem3328617 {_86951 : Type'} : (@ex (_86951 -> Prop)) = (@ex (_86951 -> Prop)).
Proof. exact (eq_refl (@ex (_86951 -> Prop))). Qed.
Lemma lem3328618 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term17 _86951 s x) = (term24 _86951 s x).
Proof. exact (MK_COMB (@lem3328617 _86951) (@lem3328616 _86951 s x)). Qed.
Lemma lem3328623 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term16 _86951 x s) = (term24 _86951 s x).
Proof. exact (TRANS (@lem3328596 _86951 s x) (@lem3328618 _86951 s x)). Qed.
Lemma lem3328624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3328625 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term25 _86951 x s) = (term26 _86951 s x).
Proof. exact (MK_COMB (@lem3328624) (@lem3328623 _86951 s x)). Qed.
Lemma lem3328627 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3328628 {_86951 : Type'} (x : _86951) : (@IN _86951 x (@EMPTY _86951)) = False.
Proof. exact (@lem3328627 _86951 x). Qed.
Lemma lem3328629 {_86951 : Type'} (s : type686 _86951) (x : _86951) : ((term16 _86951 x s) = (@IN _86951 x (@EMPTY _86951))) = ((term24 _86951 s x) = False).
Proof. exact (MK_COMB (@lem3328625 _86951 s x) (@lem3328628 _86951 x)). Qed.
Lemma lem3328631 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3328632 {_86951 : Type'} (s : type686 _86951) (x : _86951) : ((term24 _86951 s x) = False) = (term27 _86951 s x).
Proof. exact (@lem3328631 (term24 _86951 s x)). Qed.
Lemma lem3328639 {_86951 : Type'} (s : type686 _86951) (x : _86951) : ((term16 _86951 x s) = (@IN _86951 x (@EMPTY _86951))) = (term27 _86951 s x).
Proof. exact (TRANS (@lem3328629 _86951 s x) (@lem3328632 _86951 s x)). Qed.
Lemma lem3328640 {_86951 : Type'} (s : type686 _86951) : (term28 _86951 s) = (term29 _86951 s).
Proof. exact (fun_ext (fun x : _86951 => @lem3328639 _86951 s x)). Qed.
Lemma lem3328641 {_86951 : Type'} : (@all _86951) = (@all _86951).
Proof. exact (eq_refl (@all _86951)). Qed.
Lemma lem3328642 {_86951 : Type'} (s : type686 _86951) : (term1 _86951 s) = (term30 _86951 s).
Proof. exact (MK_COMB (@lem3328641 _86951) (@lem3328640 _86951 s)). Qed.
Lemma lem3328647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3328648 {_86951 : Type'} (s : type686 _86951) : (term3 _86951 s) = (term31 _86951 s).
Proof. exact (MK_COMB (@lem3328647) (@lem3328642 _86951 s)). Qed.
Lemma lem3328656 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3328657 {_86951 : Type'} (P : type686 _86951) (x : _86951 -> Prop) : (@IN (_86951 -> Prop) x P) = (P x).
Proof. exact (@lem3328656 (_86951 -> Prop) P x). Qed.
Lemma lem3328658 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (@IN (_86951 -> Prop) t s) = (s t).
Proof. exact (@lem3328657 _86951 s t). Qed.
Lemma lem3328659 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3328660 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term5 _86951 t s) = (term32 _86951 s t).
Proof. exact (MK_COMB (@lem3328659) (@lem3328658 _86951 s t)). Qed.
Lemma lem3328668 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3328669 {_86951 : Type'} (P : _86951 -> Prop) (x : _86951) : (@IN _86951 x P) = (P x).
Proof. exact (@lem3328668 _86951 P x). Qed.
Lemma lem3328670 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (@IN _86951 x t) = (t x).
Proof. exact (@lem3328669 _86951 t x). Qed.
Lemma lem3328671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3328672 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (term33 _86951 x t) = (term34 _86951 t x).
Proof. exact (MK_COMB (@lem3328671) (@lem3328670 _86951 t x)). Qed.
Lemma lem3328674 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3328675 {_86951 : Type'} (x : _86951) : (@IN _86951 x (@EMPTY _86951)) = False.
Proof. exact (@lem3328674 _86951 x). Qed.
Lemma lem3328676 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : ((@IN _86951 x t) = (@IN _86951 x (@EMPTY _86951))) = ((t x) = False).
Proof. exact (MK_COMB (@lem3328672 _86951 t x) (@lem3328675 _86951 x)). Qed.
Lemma lem3328678 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3328679 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : ((t x) = False) = (term35 _86951 t x).
Proof. exact (@lem3328678 (t x)). Qed.
Lemma lem3328680 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : ((@IN _86951 x t) = (@IN _86951 x (@EMPTY _86951))) = (term35 _86951 t x).
Proof. exact (TRANS (@lem3328676 _86951 t x) (@lem3328679 _86951 t x)). Qed.
Lemma lem3328681 {_86951 : Type'} (t : _86951 -> Prop) : (term36 _86951 t) = (term37 _86951 t).
Proof. exact (fun_ext (fun x : _86951 => @lem3328680 _86951 t x)). Qed.
Lemma lem3328682 {_86951 : Type'} : (@all _86951) = (@all _86951).
Proof. exact (eq_refl (@all _86951)). Qed.
Lemma lem3328683 {_86951 : Type'} (t : _86951 -> Prop) : (term4 _86951 t) = (term38 _86951 t).
Proof. exact (MK_COMB (@lem3328682 _86951) (@lem3328681 _86951 t)). Qed.
Lemma lem3328688 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term7 _86951 s t) = (term39 _86951 s t).
Proof. exact (MK_COMB (@lem3328660 _86951 s t) (@lem3328683 _86951 t)). Qed.
Lemma lem3328691 {_86951 : Type'} (s : type686 _86951) : (term9 _86951 s) = (term40 _86951 s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3328688 _86951 s t)). Qed.
Lemma lem3328692 {_86951 : Type'} : (@all (_86951 -> Prop)) = (@all (_86951 -> Prop)).
Proof. exact (eq_refl (@all (_86951 -> Prop))). Qed.
Lemma lem3328693 {_86951 : Type'} (s : type686 _86951) : (term11 _86951 s) = (term41 _86951 s).
Proof. exact (MK_COMB (@lem3328692 _86951) (@lem3328691 _86951 s)). Qed.
Lemma lem3328698 {_86951 : Type'} (s : type686 _86951) : ((term1 _86951 s) = (term11 _86951 s)) = ((term30 _86951 s) = (term41 _86951 s)).
Proof. exact (MK_COMB (@lem3328648 _86951 s) (@lem3328693 _86951 s)). Qed.
Lemma lem3328701 {_86951 : Type'} : (term13 _86951) = (term42 _86951).
Proof. exact (fun_ext (fun s : type686 _86951 => @lem3328698 _86951 s)). Qed.
Lemma lem3328702 {_86951 : Type'} : (@all ((_86951 -> Prop) -> Prop)) = (@all ((_86951 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_86951 -> Prop) -> Prop))). Qed.
Lemma lem3328703 {_86951 : Type'} : (term15 _86951) = (term43 _86951).
Proof. exact (MK_COMB (@lem3328702 _86951) (@lem3328701 _86951)). Qed.
Lemma lem3328708 {_86951 : Type'} : (term43 _86951) = (term15 _86951).
Proof. exact (SYM (@lem3328703 _86951)). Qed.
Lemma lem3328710 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3328711 {_86951 : Type'} : (term43 _86951) = (term45 _86951).
Proof. exact (@lem3328710 (term43 _86951)). Qed.
Lemma lem3328712 {_86951 : Type'} : (term45 _86951) = (term43 _86951).
Proof. exact (SYM (@lem3328711 _86951)). Qed.
Lemma lem3328713 {_86951 : Type'} (h1 : term46 _86951) : term46 _86951.
Proof. exact (h1). Qed.
Lemma lem3328716 {_86951 : Type'} (h1 : term45 _86951) : term45 _86951.
Proof. exact (h1). Qed.
Lemma lem3328717 {_86951 : Type'} : term47 _86951.
Proof. exact (fun h0 : term45 _86951 => @lem3328716 _86951 h0). Qed.
Lemma lem3328718 {_86951 : Type'} (h1 : term47 _86951) : term47 _86951.
Proof. exact (h1). Qed.
Lemma lem3328719 {_86951 : Type'} (h1 : term45 _86951) : term45 _86951.
Proof. exact (h1). Qed.
Lemma lem3328720 {_86951 : Type'} (h1 : term45 _86951) (h2 : term47 _86951) : term45 _86951.
Proof. exact (@lem3328718 _86951 h2 (@lem3328719 _86951 h1)). Qed.
Lemma lem3328721 {_86951 : Type'} (h1 : term45 _86951) : term48 _86951.
Proof. exact (fun h0 : term47 _86951 => @lem3328720 _86951 h1 h0). Qed.
Lemma lem3328722 {_86951 : Type'} (h1 : term47 _86951) : term47 _86951.
Proof. exact (h1). Qed.
Lemma lem3328723 {_86951 : Type'} (h1 : term45 _86951) (h2 : term47 _86951) : term45 _86951.
Proof. exact (@lem3328721 _86951 h1 (@lem3328722 _86951 h2)). Qed.
Lemma lem3328724 {_86951 : Type'} (h1 : term47 _86951) : term47 _86951.
Proof. exact (fun h0 : term45 _86951 => @lem3328723 _86951 h0 h1). Qed.
Lemma lem3328725 {_86951 : Type'} : term49 _86951.
Proof. exact (fun h0 : term47 _86951 => @lem3328724 _86951 h0). Qed.
Lemma lem3328728 {_86951 : Type'} : term47 _86951.
Proof. exact (@lem3328725 _86951 (@lem3328717 _86951)). Qed.
Lemma lem3328729 {_86951 : Type'} : term47 _86951.
Proof. exact (@lem3328728 _86951). Qed.
Lemma lem3328731 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3328732 {_86951 : Type'} : (term45 _86951) = (term50 _86951).
Proof. exact (@lem3328731 (term46 _86951)). Qed.
Lemma lem3328734 (t : Prop) : (term51 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3328735 {_86951 : Type'} : (term50 _86951) = (term43 _86951).
Proof. exact (@lem3328734 (term43 _86951)). Qed.
Lemma lem3328788 {_86951 : Type'} : (term45 _86951) = (term43 _86951).
Proof. exact (TRANS (@lem3328732 _86951) (@lem3328735 _86951)). Qed.
Lemma lem3328791 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (term35 _86951 t x) = (term35 _86951 t x).
Proof. exact (eq_refl (term35 _86951 t x)). Qed.
Lemma lem3328792 {_86951 : Type'} (t : _86951 -> Prop) : (term37 _86951 t) = (term37 _86951 t).
Proof. exact (fun_ext (fun x : _86951 => @lem3328791 _86951 t x)). Qed.
Lemma lem3328793 {_86951 : Type'} : (@all _86951) = (@all _86951).
Proof. exact (eq_refl (@all _86951)). Qed.
Lemma lem3328794 {_86951 : Type'} (t : _86951 -> Prop) : (term38 _86951 t) = (term38 _86951 t).
Proof. exact (MK_COMB (@lem3328793 _86951) (@lem3328792 _86951 t)). Qed.
Lemma lem3328797 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term32 _86951 s t) = (term32 _86951 s t).
Proof. exact (eq_refl (term32 _86951 s t)). Qed.
Lemma lem3328798 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term39 _86951 s t) = (term39 _86951 s t).
Proof. exact (MK_COMB (@lem3328797 _86951 s t) (@lem3328794 _86951 t)). Qed.
Lemma lem3328799 {_86951 : Type'} (s : type686 _86951) : (term40 _86951 s) = (term40 _86951 s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3328798 _86951 s t)). Qed.
Lemma lem3328800 {_86951 : Type'} : (@all (_86951 -> Prop)) = (@all (_86951 -> Prop)).
Proof. exact (eq_refl (@all (_86951 -> Prop))). Qed.
Lemma lem3328801 {_86951 : Type'} (s : type686 _86951) : (term41 _86951 s) = (term41 _86951 s).
Proof. exact (MK_COMB (@lem3328800 _86951) (@lem3328799 _86951 s)). Qed.
Lemma lem3328806 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term21 _86951 s t x) = (term21 _86951 s t x).
Proof. exact (eq_refl (term21 _86951 s t x)). Qed.
Lemma lem3328807 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term23 _86951 s x) = (term23 _86951 s x).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3328806 _86951 s t x)). Qed.
Lemma lem3328808 {_86951 : Type'} : (@ex (_86951 -> Prop)) = (@ex (_86951 -> Prop)).
Proof. exact (eq_refl (@ex (_86951 -> Prop))). Qed.
Lemma lem3328809 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term24 _86951 s x) = (term24 _86951 s x).
Proof. exact (MK_COMB (@lem3328808 _86951) (@lem3328807 _86951 s x)). Qed.
Lemma lem3328810 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3328811 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term27 _86951 s x) = (term27 _86951 s x).
Proof. exact (MK_COMB (@lem3328810) (@lem3328809 _86951 s x)). Qed.
Lemma lem3328812 {_86951 : Type'} (s : type686 _86951) : (term29 _86951 s) = (term29 _86951 s).
Proof. exact (fun_ext (fun x : _86951 => @lem3328811 _86951 s x)). Qed.
Lemma lem3328813 {_86951 : Type'} : (@all _86951) = (@all _86951).
Proof. exact (eq_refl (@all _86951)). Qed.
Lemma lem3328814 {_86951 : Type'} (s : type686 _86951) : (term30 _86951 s) = (term30 _86951 s).
Proof. exact (MK_COMB (@lem3328813 _86951) (@lem3328812 _86951 s)). Qed.
Lemma lem3328815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3328816 {_86951 : Type'} (s : type686 _86951) : (term31 _86951 s) = (term31 _86951 s).
Proof. exact (MK_COMB (@lem3328815) (@lem3328814 _86951 s)). Qed.
Lemma lem3328817 {_86951 : Type'} (s : type686 _86951) : ((term30 _86951 s) = (term41 _86951 s)) = ((term30 _86951 s) = (term41 _86951 s)).
Proof. exact (MK_COMB (@lem3328816 _86951 s) (@lem3328801 _86951 s)). Qed.
Lemma lem3328818 {_86951 : Type'} : (term42 _86951) = (term42 _86951).
Proof. exact (fun_ext (fun s : type686 _86951 => @lem3328817 _86951 s)). Qed.
Lemma lem3328819 {_86951 : Type'} : (@all ((_86951 -> Prop) -> Prop)) = (@all ((_86951 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_86951 -> Prop) -> Prop))). Qed.
Lemma lem3328820 {_86951 : Type'} : (term43 _86951) = (term43 _86951).
Proof. exact (MK_COMB (@lem3328819 _86951) (@lem3328818 _86951)). Qed.
Lemma lem3328857 {_86951 : Type'} : (term45 _86951) = (term43 _86951).
Proof. exact (TRANS (@lem3328788 _86951) (@lem3328820 _86951)). Qed.
Lemma lem3328858 {_86951 : Type'} : (term43 _86951) = (term45 _86951).
Proof. exact (SYM (@lem3328857 _86951)). Qed.
Lemma lem3328860 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3328861 {_86951 : Type'} (s : type686 _86951) : ((term30 _86951 s) = (term41 _86951 s)) = (term52 _86951 s).
Proof. exact (@lem3328860 ((term30 _86951 s) = (term41 _86951 s))). Qed.
Lemma lem3328862 {_86951 : Type'} (s : type686 _86951) : (term52 _86951 s) = ((term30 _86951 s) = (term41 _86951 s)).
Proof. exact (SYM (@lem3328861 _86951 s)). Qed.
Lemma lem3328863 {_86951 : Type'} (s : type686 _86951) (h1 : term53 _86951 s) : term53 _86951 s.
Proof. exact (h1). Qed.
Lemma lem3328872 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term54 _86951 s t x) = (term55 _86951 s t x).
Proof. exact (@lem17045 (s t) (t x)). Qed.
Lemma lem3328875 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term21 _86951 s t x) = (term21 _86951 s t x).
Proof. exact (eq_refl (term21 _86951 s t x)). Qed.
Lemma lem3328876 {_86951 : Type'} (P : type686 _86951) : (term56 _86951 P) = (term57 _86951 P).
Proof. exact (@lem18394 (_86951 -> Prop) P). Qed.
Lemma lem3328877 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term27 _86951 s x) = (term58 _86951 s x).
Proof. exact (@lem3328876 _86951 (term23 _86951 s x)). Qed.
Lemma lem3328878 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term59 _86951 s x t) = (term21 _86951 s t x).
Proof. exact (eq_refl (term59 _86951 s x t)). Qed.
Lemma lem3328879 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3328880 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term60 _86951 s x t) = (term54 _86951 s t x).
Proof. exact (MK_COMB (@lem3328879) (@lem3328878 _86951 s t x)). Qed.
Lemma lem3328881 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term60 _86951 s x t) = (term55 _86951 s t x).
Proof. exact (TRANS (@lem3328880 _86951 s t x) (@lem3328872 _86951 s t x)). Qed.
Lemma lem3328882 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term61 _86951 s x) = (term62 _86951 s x).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3328881 _86951 s t x)). Qed.
Lemma lem3328883 {_86951 : Type'} : (@all (_86951 -> Prop)) = (@all (_86951 -> Prop)).
Proof. exact (eq_refl (@all (_86951 -> Prop))). Qed.
Lemma lem3328884 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term58 _86951 s x) = (term63 _86951 s x).
Proof. exact (MK_COMB (@lem3328883 _86951) (@lem3328882 _86951 s x)). Qed.
Lemma lem3328885 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term27 _86951 s x) = (term63 _86951 s x).
Proof. exact (TRANS (@lem3328877 _86951 s x) (@lem3328884 _86951 s x)). Qed.
Lemma lem3328886 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term23 _86951 s x) = (term23 _86951 s x).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3328875 _86951 s t x)). Qed.
Lemma lem3328887 {_86951 : Type'} : (@ex (_86951 -> Prop)) = (@ex (_86951 -> Prop)).
Proof. exact (eq_refl (@ex (_86951 -> Prop))). Qed.
Lemma lem3328888 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term24 _86951 s x) = (term24 _86951 s x).
Proof. exact (MK_COMB (@lem3328887 _86951) (@lem3328886 _86951 s x)). Qed.
Lemma lem3328889 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term64 _86951 s x) = (term24 _86951 s x).
Proof. exact (@lem16933 (term24 _86951 s x)). Qed.
Lemma lem3328890 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term64 _86951 s x) = (term24 _86951 s x).
Proof. exact (TRANS (@lem3328889 _86951 s x) (@lem3328888 _86951 s x)). Qed.
Lemma lem3328891 {_86951 : Type'} (P : _86951 -> Prop) : (term65 _86951 P) = (term66 _86951 P).
Proof. exact (@lem18392 _86951 P). Qed.
Lemma lem3328892 {_86951 : Type'} (s : type686 _86951) : (term67 _86951 s) = (term68 _86951 s).
Proof. exact (@lem3328891 _86951 (term29 _86951 s)). Qed.
Lemma lem3328893 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term69 _86951 s x) = (term27 _86951 s x).
Proof. exact (eq_refl (term69 _86951 s x)). Qed.
Lemma lem3328894 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3328895 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term70 _86951 s x) = (term64 _86951 s x).
Proof. exact (MK_COMB (@lem3328894) (@lem3328893 _86951 s x)). Qed.
Lemma lem3328896 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term70 _86951 s x) = (term24 _86951 s x).
Proof. exact (TRANS (@lem3328895 _86951 s x) (@lem3328890 _86951 s x)). Qed.
Lemma lem3328897 {_86951 : Type'} (s : type686 _86951) : (term71 _86951 s) = (term72 _86951 s).
Proof. exact (fun_ext (fun x : _86951 => @lem3328896 _86951 s x)). Qed.
Lemma lem3328898 {_86951 : Type'} : (@ex _86951) = (@ex _86951).
Proof. exact (eq_refl (@ex _86951)). Qed.
Lemma lem3328899 {_86951 : Type'} (s : type686 _86951) : (term68 _86951 s) = (term73 _86951 s).
Proof. exact (MK_COMB (@lem3328898 _86951) (@lem3328897 _86951 s)). Qed.
Lemma lem3328900 {_86951 : Type'} (s : type686 _86951) : (term67 _86951 s) = (term73 _86951 s).
Proof. exact (TRANS (@lem3328892 _86951 s) (@lem3328899 _86951 s)). Qed.
Lemma lem3328901 {_86951 : Type'} (s : type686 _86951) : (term29 _86951 s) = (term74 _86951 s).
Proof. exact (fun_ext (fun x : _86951 => @lem3328885 _86951 s x)). Qed.
Lemma lem3328902 {_86951 : Type'} : (@all _86951) = (@all _86951).
Proof. exact (eq_refl (@all _86951)). Qed.
Lemma lem3328903 {_86951 : Type'} (s : type686 _86951) : (term30 _86951 s) = (term75 _86951 s).
Proof. exact (MK_COMB (@lem3328902 _86951) (@lem3328901 _86951 s)). Qed.
Lemma lem3328906 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (term35 _86951 t x) = (term35 _86951 t x).
Proof. exact (eq_refl (term35 _86951 t x)). Qed.
Lemma lem3328909 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (term76 _86951 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3328910 {_86951 : Type'} (P : _86951 -> Prop) : (term65 _86951 P) = (term66 _86951 P).
Proof. exact (@lem18392 _86951 P). Qed.
Lemma lem3328911 {_86951 : Type'} (t : _86951 -> Prop) : (term77 _86951 t) = (term78 _86951 t).
Proof. exact (@lem3328910 _86951 (term37 _86951 t)). Qed.
Lemma lem3328912 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (term79 _86951 t x) = (term35 _86951 t x).
Proof. exact (eq_refl (term79 _86951 t x)). Qed.
Lemma lem3328913 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3328914 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (term80 _86951 t x) = (term76 _86951 t x).
Proof. exact (MK_COMB (@lem3328913) (@lem3328912 _86951 t x)). Qed.
Lemma lem3328915 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (term80 _86951 t x) = (t x).
Proof. exact (TRANS (@lem3328914 _86951 t x) (@lem3328909 _86951 t x)). Qed.
Lemma lem3328916 {_86951 : Type'} (t : _86951 -> Prop) : (term81 _86951 t) = (term82 _86951 t).
Proof. exact (fun_ext (fun x : _86951 => @lem3328915 _86951 t x)). Qed.
Lemma lem3328917 {_86951 : Type'} : (@ex _86951) = (@ex _86951).
Proof. exact (eq_refl (@ex _86951)). Qed.
Lemma lem3328918 {_86951 : Type'} (t : _86951 -> Prop) : (term78 _86951 t) = (term83 _86951 t).
Proof. exact (MK_COMB (@lem3328917 _86951) (@lem3328916 _86951 t)). Qed.
Lemma lem3328919 {_86951 : Type'} (t : _86951 -> Prop) : (term77 _86951 t) = (term83 _86951 t).
Proof. exact (TRANS (@lem3328911 _86951 t) (@lem3328918 _86951 t)). Qed.
Lemma lem3328920 {_86951 : Type'} (t : _86951 -> Prop) : (term37 _86951 t) = (term37 _86951 t).
Proof. exact (fun_ext (fun x : _86951 => @lem3328906 _86951 t x)). Qed.
Lemma lem3328921 {_86951 : Type'} : (@all _86951) = (@all _86951).
Proof. exact (eq_refl (@all _86951)). Qed.
Lemma lem3328922 {_86951 : Type'} (t : _86951 -> Prop) : (term38 _86951 t) = (term38 _86951 t).
Proof. exact (MK_COMB (@lem3328921 _86951) (@lem3328920 _86951 t)). Qed.
Lemma lem3328924 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term19 _86951 s t) = (term19 _86951 s t).
Proof. exact (eq_refl (term19 _86951 s t)). Qed.
Lemma lem3328925 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term84 _86951 s t) = (term85 _86951 s t).
Proof. exact (MK_COMB (@lem3328924 _86951 s t) (@lem3328919 _86951 t)). Qed.
Lemma lem3328926 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term86 _86951 s t) = (term84 _86951 s t).
Proof. exact (@lem17362 (s t) (term38 _86951 t)). Qed.
Lemma lem3328927 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term86 _86951 s t) = (term85 _86951 s t).
Proof. exact (TRANS (@lem3328926 _86951 s t) (@lem3328925 _86951 s t)). Qed.
Lemma lem3328929 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term87 _86951 s t) = (term87 _86951 s t).
Proof. exact (eq_refl (term87 _86951 s t)). Qed.
Lemma lem3328930 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term88 _86951 s t) = (term88 _86951 s t).
Proof. exact (MK_COMB (@lem3328929 _86951 s t) (@lem3328922 _86951 t)). Qed.
Lemma lem3328931 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term39 _86951 s t) = (term88 _86951 s t).
Proof. exact (@lem17265 (s t) (term38 _86951 t)). Qed.
Lemma lem3328932 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term39 _86951 s t) = (term88 _86951 s t).
Proof. exact (TRANS (@lem3328931 _86951 s t) (@lem3328930 _86951 s t)). Qed.
Lemma lem3328933 {_86951 : Type'} (P : type686 _86951) : (term89 _86951 P) = (term90 _86951 P).
Proof. exact (@lem18392 (_86951 -> Prop) P). Qed.
Lemma lem3328934 {_86951 : Type'} (s : type686 _86951) : (term91 _86951 s) = (term92 _86951 s).
Proof. exact (@lem3328933 _86951 (term40 _86951 s)). Qed.
Lemma lem3328935 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term93 _86951 s t) = (term39 _86951 s t).
Proof. exact (eq_refl (term93 _86951 s t)). Qed.
Lemma lem3328936 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3328937 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term94 _86951 s t) = (term86 _86951 s t).
Proof. exact (MK_COMB (@lem3328936) (@lem3328935 _86951 s t)). Qed.
Lemma lem3328938 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term94 _86951 s t) = (term85 _86951 s t).
Proof. exact (TRANS (@lem3328937 _86951 s t) (@lem3328927 _86951 s t)). Qed.
Lemma lem3328939 {_86951 : Type'} (s : type686 _86951) : (term95 _86951 s) = (term96 _86951 s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3328938 _86951 s t)). Qed.
Lemma lem3328940 {_86951 : Type'} : (@ex (_86951 -> Prop)) = (@ex (_86951 -> Prop)).
Proof. exact (eq_refl (@ex (_86951 -> Prop))). Qed.
Lemma lem3328941 {_86951 : Type'} (s : type686 _86951) : (term92 _86951 s) = (term97 _86951 s).
Proof. exact (MK_COMB (@lem3328940 _86951) (@lem3328939 _86951 s)). Qed.
Lemma lem3328942 {_86951 : Type'} (s : type686 _86951) : (term91 _86951 s) = (term97 _86951 s).
Proof. exact (TRANS (@lem3328934 _86951 s) (@lem3328941 _86951 s)). Qed.
Lemma lem3328943 {_86951 : Type'} (s : type686 _86951) : (term40 _86951 s) = (term98 _86951 s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3328932 _86951 s t)). Qed.
Lemma lem3328944 {_86951 : Type'} : (@all (_86951 -> Prop)) = (@all (_86951 -> Prop)).
Proof. exact (eq_refl (@all (_86951 -> Prop))). Qed.
Lemma lem3328945 {_86951 : Type'} (s : type686 _86951) : (term41 _86951 s) = (term99 _86951 s).
Proof. exact (MK_COMB (@lem3328944 _86951) (@lem3328943 _86951 s)). Qed.
Lemma lem3328946 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3328947 {_86951 : Type'} (s : type686 _86951) : (term100 _86951 s) = (term101 _86951 s).
Proof. exact (MK_COMB (@lem3328946) (@lem3328900 _86951 s)). Qed.
Lemma lem3328948 {_86951 : Type'} (s : type686 _86951) : (term102 _86951 s) = (term103 _86951 s).
Proof. exact (MK_COMB (@lem3328947 _86951 s) (@lem3328945 _86951 s)). Qed.
Lemma lem3328949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3328950 {_86951 : Type'} (s : type686 _86951) : (term104 _86951 s) = (term105 _86951 s).
Proof. exact (MK_COMB (@lem3328949) (@lem3328903 _86951 s)). Qed.
Lemma lem3328951 {_86951 : Type'} (s : type686 _86951) : (term106 _86951 s) = (term107 _86951 s).
Proof. exact (MK_COMB (@lem3328950 _86951 s) (@lem3328942 _86951 s)). Qed.
Lemma lem3328952 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3328953 {_86951 : Type'} (s : type686 _86951) : (term108 _86951 s) = (term109 _86951 s).
Proof. exact (MK_COMB (@lem3328952) (@lem3328951 _86951 s)). Qed.
Lemma lem3328954 {_86951 : Type'} (s : type686 _86951) : (term110 _86951 s) = (term111 _86951 s).
Proof. exact (MK_COMB (@lem3328953 _86951 s) (@lem3328948 _86951 s)). Qed.
Lemma lem3328955 {_86951 : Type'} (s : type686 _86951) : (term53 _86951 s) = (term110 _86951 s).
Proof. exact (@lem17646 (term30 _86951 s) (term41 _86951 s)). Qed.
Lemma lem3328956 {_86951 : Type'} (s : type686 _86951) : (term53 _86951 s) = (term111 _86951 s).
Proof. exact (TRANS (@lem3328955 _86951 s) (@lem3328954 _86951 s)). Qed.
Lemma lem3329127 {A : Type'} (P : Prop) (Q : A -> Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3329128 {_86951 : Type'} (P : Prop) (Q : _86951 -> Prop) : (term112 _86951 P Q) = (term113 _86951 P Q).
Proof. exact (@lem3329127 _86951 P Q). Qed.
Lemma lem3329129 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term85 _86951 s t) = (term114 _86951 s t).
Proof. exact (@lem3329128 _86951 (s t) t). Qed.
Lemma lem3329130 {_86951 : Type'} (s : type686 _86951) : (term96 _86951 s) = (term115 _86951 s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3329129 _86951 s t)). Qed.
Lemma lem3329131 {_86951 : Type'} : (@ex (_86951 -> Prop)) = (@ex (_86951 -> Prop)).
Proof. exact (eq_refl (@ex (_86951 -> Prop))). Qed.
Lemma lem3329132 {_86951 : Type'} (s : type686 _86951) : (term97 _86951 s) = (term116 _86951 s).
Proof. exact (MK_COMB (@lem3329131 _86951) (@lem3329130 _86951 s)). Qed.
Lemma lem3329133 {_86951 : Type'} (s : type686 _86951) : (term105 _86951 s) = (term105 _86951 s).
Proof. exact (eq_refl (term105 _86951 s)). Qed.
Lemma lem3329134 {_86951 : Type'} (s : type686 _86951) : (term107 _86951 s) = (term117 _86951 s).
Proof. exact (MK_COMB (@lem3329133 _86951 s) (@lem3329132 _86951 s)). Qed.
Lemma lem3329136 {A : Type'} (P : Prop) (Q : A -> Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3329137 {_86951 : Type'} (P : Prop) (Q : type686 _86951) : (term118 _86951 P Q) = (term119 _86951 P Q).
Proof. exact (@lem3329136 (_86951 -> Prop) P Q). Qed.
Lemma lem3329138 {_86951 : Type'} (s : type686 _86951) : (term120 _86951 s) = (term121 _86951 s).
Proof. exact (@lem3329137 _86951 (term75 _86951 s) (term115 _86951 s)). Qed.
Lemma lem3329139 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term122 _86951 s t) = (term114 _86951 s t).
Proof. exact (eq_refl (term122 _86951 s t)). Qed.
Lemma lem3329140 {_86951 : Type'} (s : type686 _86951) : (term123 _86951 s) = (term115 _86951 s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3329139 _86951 s t)). Qed.
Lemma lem3329141 {_86951 : Type'} : (@ex (_86951 -> Prop)) = (@ex (_86951 -> Prop)).
Proof. exact (eq_refl (@ex (_86951 -> Prop))). Qed.
Lemma lem3329142 {_86951 : Type'} (s : type686 _86951) : (term124 _86951 s) = (term116 _86951 s).
Proof. exact (MK_COMB (@lem3329141 _86951) (@lem3329140 _86951 s)). Qed.
Lemma lem3329143 {_86951 : Type'} (s : type686 _86951) : (term105 _86951 s) = (term105 _86951 s).
Proof. exact (eq_refl (term105 _86951 s)). Qed.
Lemma lem3329144 {_86951 : Type'} (s : type686 _86951) : (term120 _86951 s) = (term117 _86951 s).
Proof. exact (MK_COMB (@lem3329143 _86951 s) (@lem3329142 _86951 s)). Qed.
Lemma lem3329145 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3329146 {_86951 : Type'} (s : type686 _86951) : (term125 _86951 s) = (term126 _86951 s).
Proof. exact (MK_COMB (@lem3329145) (@lem3329144 _86951 s)). Qed.
Lemma lem3329147 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term122 _86951 s t) = (term114 _86951 s t).
Proof. exact (eq_refl (term122 _86951 s t)). Qed.
Lemma lem3329148 {_86951 : Type'} (s : type686 _86951) : (term105 _86951 s) = (term105 _86951 s).
Proof. exact (eq_refl (term105 _86951 s)). Qed.
Lemma lem3329149 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term127 _86951 s t) = (term128 _86951 s t).
Proof. exact (MK_COMB (@lem3329148 _86951 s) (@lem3329147 _86951 s t)). Qed.
Lemma lem3329150 {_86951 : Type'} (s : type686 _86951) : (term129 _86951 s) = (term130 _86951 s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3329149 _86951 s t)). Qed.
Lemma lem3329151 {_86951 : Type'} : (@ex (_86951 -> Prop)) = (@ex (_86951 -> Prop)).
Proof. exact (eq_refl (@ex (_86951 -> Prop))). Qed.
Lemma lem3329152 {_86951 : Type'} (s : type686 _86951) : (term121 _86951 s) = (term131 _86951 s).
Proof. exact (MK_COMB (@lem3329151 _86951) (@lem3329150 _86951 s)). Qed.
Lemma lem3329153 {_86951 : Type'} (s : type686 _86951) : ((term120 _86951 s) = (term121 _86951 s)) = ((term117 _86951 s) = (term131 _86951 s)).
Proof. exact (MK_COMB (@lem3329146 _86951 s) (@lem3329152 _86951 s)). Qed.
Lemma lem3329154 {_86951 : Type'} (s : type686 _86951) : (term117 _86951 s) = (term131 _86951 s).
Proof. exact (EQ_MP (@lem3329153 _86951 s) (@lem3329138 _86951 s)). Qed.
Lemma lem3329156 {A : Type'} (P : Prop) (Q : A -> Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3329157 {_86951 : Type'} (P : Prop) (Q : _86951 -> Prop) : (term112 _86951 P Q) = (term113 _86951 P Q).
Proof. exact (@lem3329156 _86951 P Q). Qed.
Lemma lem3329158 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term132 _86951 s t) = (term133 _86951 s t).
Proof. exact (@lem3329157 _86951 (term75 _86951 s) (term134 _86951 s t)). Qed.
Lemma lem3329159 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term135 _86951 s t x) = (term21 _86951 s t x).
Proof. exact (eq_refl (term135 _86951 s t x)). Qed.
Lemma lem3329160 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term136 _86951 s t) = (term134 _86951 s t).
Proof. exact (fun_ext (fun x : _86951 => @lem3329159 _86951 s t x)). Qed.
Lemma lem3329161 {_86951 : Type'} : (@ex _86951) = (@ex _86951).
Proof. exact (eq_refl (@ex _86951)). Qed.
Lemma lem3329162 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term137 _86951 s t) = (term114 _86951 s t).
Proof. exact (MK_COMB (@lem3329161 _86951) (@lem3329160 _86951 s t)). Qed.
Lemma lem3329163 {_86951 : Type'} (s : type686 _86951) : (term105 _86951 s) = (term105 _86951 s).
Proof. exact (eq_refl (term105 _86951 s)). Qed.
Lemma lem3329164 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term132 _86951 s t) = (term128 _86951 s t).
Proof. exact (MK_COMB (@lem3329163 _86951 s) (@lem3329162 _86951 s t)). Qed.
Lemma lem3329165 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3329166 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term138 _86951 s t) = (term139 _86951 s t).
Proof. exact (MK_COMB (@lem3329165) (@lem3329164 _86951 s t)). Qed.
Lemma lem3329167 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term135 _86951 s t x) = (term21 _86951 s t x).
Proof. exact (eq_refl (term135 _86951 s t x)). Qed.
Lemma lem3329168 {_86951 : Type'} (s : type686 _86951) : (term105 _86951 s) = (term105 _86951 s).
Proof. exact (eq_refl (term105 _86951 s)). Qed.
Lemma lem3329169 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term140 _86951 s t x) = (term141 _86951 s t x).
Proof. exact (MK_COMB (@lem3329168 _86951 s) (@lem3329167 _86951 s t x)). Qed.
Lemma lem3329170 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term142 _86951 s t) = (term143 _86951 s t).
Proof. exact (fun_ext (fun x : _86951 => @lem3329169 _86951 s t x)). Qed.
Lemma lem3329171 {_86951 : Type'} : (@ex _86951) = (@ex _86951).
Proof. exact (eq_refl (@ex _86951)). Qed.
Lemma lem3329172 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term133 _86951 s t) = (term144 _86951 s t).
Proof. exact (MK_COMB (@lem3329171 _86951) (@lem3329170 _86951 s t)). Qed.
Lemma lem3329173 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : ((term132 _86951 s t) = (term133 _86951 s t)) = ((term128 _86951 s t) = (term144 _86951 s t)).
Proof. exact (MK_COMB (@lem3329166 _86951 s t) (@lem3329172 _86951 s t)). Qed.
Lemma lem3329174 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term128 _86951 s t) = (term144 _86951 s t).
Proof. exact (EQ_MP (@lem3329173 _86951 s t) (@lem3329158 _86951 s t)). Qed.
Lemma lem3329175 {_86951 : Type'} (s : type686 _86951) : (term130 _86951 s) = (term145 _86951 s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3329174 _86951 s t)). Qed.
Lemma lem3329176 {_86951 : Type'} : (@ex (_86951 -> Prop)) = (@ex (_86951 -> Prop)).
Proof. exact (eq_refl (@ex (_86951 -> Prop))). Qed.
Lemma lem3329177 {_86951 : Type'} (s : type686 _86951) : (term131 _86951 s) = (term146 _86951 s).
Proof. exact (MK_COMB (@lem3329176 _86951) (@lem3329175 _86951 s)). Qed.
Lemma lem3329178 {_86951 : Type'} (s : type686 _86951) : (term117 _86951 s) = (term146 _86951 s).
Proof. exact (TRANS (@lem3329154 _86951 s) (@lem3329177 _86951 s)). Qed.
Lemma lem3329179 {_86951 : Type'} (s : type686 _86951) : (term107 _86951 s) = (term146 _86951 s).
Proof. exact (TRANS (@lem3329134 _86951 s) (@lem3329178 _86951 s)). Qed.
Lemma lem3329180 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3329181 {_86951 : Type'} (s : type686 _86951) : (term109 _86951 s) = (term147 _86951 s).
Proof. exact (MK_COMB (@lem3329180) (@lem3329179 _86951 s)). Qed.
Lemma lem3329183 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3329184 {_86951 : Type'} (P : _86951 -> Prop) (Q : Prop) : (term148 _86951 P Q) = (term149 _86951 P Q).
Proof. exact (@lem3329183 _86951 P Q). Qed.
Lemma lem3329185 {_86951 : Type'} (s : type686 _86951) : (term150 _86951 s) = (term151 _86951 s).
Proof. exact (@lem3329184 _86951 (term72 _86951 s) (term99 _86951 s)). Qed.
Lemma lem3329186 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term152 _86951 s x) = (term24 _86951 s x).
Proof. exact (eq_refl (term152 _86951 s x)). Qed.
Lemma lem3329187 {_86951 : Type'} (s : type686 _86951) : (term153 _86951 s) = (term72 _86951 s).
Proof. exact (fun_ext (fun x : _86951 => @lem3329186 _86951 s x)). Qed.
Lemma lem3329188 {_86951 : Type'} : (@ex _86951) = (@ex _86951).
Proof. exact (eq_refl (@ex _86951)). Qed.
Lemma lem3329189 {_86951 : Type'} (s : type686 _86951) : (term154 _86951 s) = (term73 _86951 s).
Proof. exact (MK_COMB (@lem3329188 _86951) (@lem3329187 _86951 s)). Qed.
Lemma lem3329190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3329191 {_86951 : Type'} (s : type686 _86951) : (term155 _86951 s) = (term101 _86951 s).
Proof. exact (MK_COMB (@lem3329190) (@lem3329189 _86951 s)). Qed.
Lemma lem3329192 {_86951 : Type'} (s : type686 _86951) : (term99 _86951 s) = (term99 _86951 s).
Proof. exact (eq_refl (term99 _86951 s)). Qed.
Lemma lem3329193 {_86951 : Type'} (s : type686 _86951) : (term150 _86951 s) = (term103 _86951 s).
Proof. exact (MK_COMB (@lem3329191 _86951 s) (@lem3329192 _86951 s)). Qed.
Lemma lem3329194 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3329195 {_86951 : Type'} (s : type686 _86951) : (term156 _86951 s) = (term157 _86951 s).
Proof. exact (MK_COMB (@lem3329194) (@lem3329193 _86951 s)). Qed.
Lemma lem3329196 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term152 _86951 s x) = (term24 _86951 s x).
Proof. exact (eq_refl (term152 _86951 s x)). Qed.
Lemma lem3329197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3329198 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term158 _86951 s x) = (term159 _86951 s x).
Proof. exact (MK_COMB (@lem3329197) (@lem3329196 _86951 s x)). Qed.
Lemma lem3329199 {_86951 : Type'} (s : type686 _86951) : (term99 _86951 s) = (term99 _86951 s).
Proof. exact (eq_refl (term99 _86951 s)). Qed.
Lemma lem3329200 {_86951 : Type'} (x : _86951) (s : type686 _86951) : (term160 _86951 x s) = (term161 _86951 x s).
Proof. exact (MK_COMB (@lem3329198 _86951 s x) (@lem3329199 _86951 s)). Qed.
Lemma lem3329201 {_86951 : Type'} (s : type686 _86951) : (term162 _86951 s) = (term163 _86951 s).
Proof. exact (fun_ext (fun x : _86951 => @lem3329200 _86951 x s)). Qed.
Lemma lem3329202 {_86951 : Type'} : (@ex _86951) = (@ex _86951).
Proof. exact (eq_refl (@ex _86951)). Qed.
Lemma lem3329203 {_86951 : Type'} (s : type686 _86951) : (term151 _86951 s) = (term164 _86951 s).
Proof. exact (MK_COMB (@lem3329202 _86951) (@lem3329201 _86951 s)). Qed.
Lemma lem3329204 {_86951 : Type'} (s : type686 _86951) : ((term150 _86951 s) = (term151 _86951 s)) = ((term103 _86951 s) = (term164 _86951 s)).
Proof. exact (MK_COMB (@lem3329195 _86951 s) (@lem3329203 _86951 s)). Qed.
Lemma lem3329205 {_86951 : Type'} (s : type686 _86951) : (term103 _86951 s) = (term164 _86951 s).
Proof. exact (EQ_MP (@lem3329204 _86951 s) (@lem3329185 _86951 s)). Qed.
Lemma lem3329207 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3329208 {_86951 : Type'} (P : type686 _86951) (Q : Prop) : (term165 _86951 P Q) = (term166 _86951 P Q).
Proof. exact (@lem3329207 (_86951 -> Prop) P Q). Qed.
Lemma lem3329209 {_86951 : Type'} (x : _86951) (s : type686 _86951) : (term167 _86951 x s) = (term168 _86951 x s).
Proof. exact (@lem3329208 _86951 (term23 _86951 s x) (term99 _86951 s)). Qed.
Lemma lem3329210 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term59 _86951 s x t) = (term21 _86951 s t x).
Proof. exact (eq_refl (term59 _86951 s x t)). Qed.
Lemma lem3329211 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term169 _86951 s x) = (term23 _86951 s x).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3329210 _86951 s t x)). Qed.
Lemma lem3329212 {_86951 : Type'} : (@ex (_86951 -> Prop)) = (@ex (_86951 -> Prop)).
Proof. exact (eq_refl (@ex (_86951 -> Prop))). Qed.
Lemma lem3329213 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term170 _86951 s x) = (term24 _86951 s x).
Proof. exact (MK_COMB (@lem3329212 _86951) (@lem3329211 _86951 s x)). Qed.
Lemma lem3329214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3329215 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term171 _86951 s x) = (term159 _86951 s x).
Proof. exact (MK_COMB (@lem3329214) (@lem3329213 _86951 s x)). Qed.
Lemma lem3329216 {_86951 : Type'} (s : type686 _86951) : (term99 _86951 s) = (term99 _86951 s).
Proof. exact (eq_refl (term99 _86951 s)). Qed.
Lemma lem3329217 {_86951 : Type'} (x : _86951) (s : type686 _86951) : (term167 _86951 x s) = (term161 _86951 x s).
Proof. exact (MK_COMB (@lem3329215 _86951 s x) (@lem3329216 _86951 s)). Qed.
Lemma lem3329218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3329219 {_86951 : Type'} (x : _86951) (s : type686 _86951) : (term172 _86951 x s) = (term173 _86951 x s).
Proof. exact (MK_COMB (@lem3329218) (@lem3329217 _86951 x s)). Qed.
Lemma lem3329220 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term59 _86951 s x t) = (term21 _86951 s t x).
Proof. exact (eq_refl (term59 _86951 s x t)). Qed.
Lemma lem3329221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3329222 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term174 _86951 s x t) = (term175 _86951 s t x).
Proof. exact (MK_COMB (@lem3329221) (@lem3329220 _86951 s t x)). Qed.
Lemma lem3329223 {_86951 : Type'} (s : type686 _86951) : (term99 _86951 s) = (term99 _86951 s).
Proof. exact (eq_refl (term99 _86951 s)). Qed.
Lemma lem3329224 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) (s : type686 _86951) : (term176 _86951 x t s) = (term177 _86951 t x s).
Proof. exact (MK_COMB (@lem3329222 _86951 s t x) (@lem3329223 _86951 s)). Qed.
Lemma lem3329225 {_86951 : Type'} (x : _86951) (s : type686 _86951) : (term178 _86951 x s) = (term179 _86951 x s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3329224 _86951 t x s)). Qed.
Lemma lem3329226 {_86951 : Type'} : (@ex (_86951 -> Prop)) = (@ex (_86951 -> Prop)).
Proof. exact (eq_refl (@ex (_86951 -> Prop))). Qed.
Lemma lem3329227 {_86951 : Type'} (x : _86951) (s : type686 _86951) : (term168 _86951 x s) = (term180 _86951 x s).
Proof. exact (MK_COMB (@lem3329226 _86951) (@lem3329225 _86951 x s)). Qed.
Lemma lem3329228 {_86951 : Type'} (x : _86951) (s : type686 _86951) : ((term167 _86951 x s) = (term168 _86951 x s)) = ((term161 _86951 x s) = (term180 _86951 x s)).
Proof. exact (MK_COMB (@lem3329219 _86951 x s) (@lem3329227 _86951 x s)). Qed.
Lemma lem3329229 {_86951 : Type'} (x : _86951) (s : type686 _86951) : (term161 _86951 x s) = (term180 _86951 x s).
Proof. exact (EQ_MP (@lem3329228 _86951 x s) (@lem3329209 _86951 x s)). Qed.
Lemma lem3329230 {_86951 : Type'} (s : type686 _86951) : (term163 _86951 s) = (term181 _86951 s).
Proof. exact (fun_ext (fun x : _86951 => @lem3329229 _86951 x s)). Qed.
Lemma lem3329231 {_86951 : Type'} : (@ex _86951) = (@ex _86951).
Proof. exact (eq_refl (@ex _86951)). Qed.
Lemma lem3329232 {_86951 : Type'} (s : type686 _86951) : (term164 _86951 s) = (term182 _86951 s).
Proof. exact (MK_COMB (@lem3329231 _86951) (@lem3329230 _86951 s)). Qed.
Lemma lem3329233 {_86951 : Type'} (s : type686 _86951) : (term103 _86951 s) = (term182 _86951 s).
Proof. exact (TRANS (@lem3329205 _86951 s) (@lem3329232 _86951 s)). Qed.
Lemma lem3329234 {_86951 : Type'} (s : type686 _86951) : (term111 _86951 s) = (term183 _86951 s).
Proof. exact (MK_COMB (@lem3329181 _86951 s) (@lem3329233 _86951 s)). Qed.
Lemma lem3329238 {A : Type'} (P : A -> Prop) (Q : Prop) : (term184 A P Q) = (term185 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3329239 {_86951 : Type'} (P : type686 _86951) (Q : Prop) : (term186 _86951 P Q) = (term187 _86951 P Q).
Proof. exact (@lem3329238 (_86951 -> Prop) P Q). Qed.
Lemma lem3329240 {_86951 : Type'} (s : type686 _86951) : (term188 _86951 s) = (term189 _86951 s).
Proof. exact (@lem3329239 _86951 (term145 _86951 s) (term182 _86951 s)). Qed.
Lemma lem3329241 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term190 _86951 s t) = (term144 _86951 s t).
Proof. exact (eq_refl (term190 _86951 s t)). Qed.
Lemma lem3329242 {_86951 : Type'} (s : type686 _86951) : (term191 _86951 s) = (term145 _86951 s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3329241 _86951 s t)). Qed.
Lemma lem3329243 {_86951 : Type'} : (@ex (_86951 -> Prop)) = (@ex (_86951 -> Prop)).
Proof. exact (eq_refl (@ex (_86951 -> Prop))). Qed.
Lemma lem3329244 {_86951 : Type'} (s : type686 _86951) : (term192 _86951 s) = (term146 _86951 s).
Proof. exact (MK_COMB (@lem3329243 _86951) (@lem3329242 _86951 s)). Qed.
Lemma lem3329245 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3329246 {_86951 : Type'} (s : type686 _86951) : (term193 _86951 s) = (term147 _86951 s).
Proof. exact (MK_COMB (@lem3329245) (@lem3329244 _86951 s)). Qed.
Lemma lem3329247 {_86951 : Type'} (s : type686 _86951) : (term182 _86951 s) = (term182 _86951 s).
Proof. exact (eq_refl (term182 _86951 s)). Qed.
Lemma lem3329248 {_86951 : Type'} (s : type686 _86951) : (term188 _86951 s) = (term183 _86951 s).
Proof. exact (MK_COMB (@lem3329246 _86951 s) (@lem3329247 _86951 s)). Qed.
Lemma lem3329249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3329250 {_86951 : Type'} (s : type686 _86951) : (term194 _86951 s) = (term195 _86951 s).
Proof. exact (MK_COMB (@lem3329249) (@lem3329248 _86951 s)). Qed.
Lemma lem3329251 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term190 _86951 s t) = (term144 _86951 s t).
Proof. exact (eq_refl (term190 _86951 s t)). Qed.
Lemma lem3329252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3329253 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term196 _86951 s t) = (term197 _86951 s t).
Proof. exact (MK_COMB (@lem3329252) (@lem3329251 _86951 s t)). Qed.
Lemma lem3329254 {_86951 : Type'} (s : type686 _86951) : (term182 _86951 s) = (term182 _86951 s).
Proof. exact (eq_refl (term182 _86951 s)). Qed.
Lemma lem3329255 {_86951 : Type'} (t : _86951 -> Prop) (s : type686 _86951) : (term198 _86951 t s) = (term199 _86951 t s).
Proof. exact (MK_COMB (@lem3329253 _86951 s t) (@lem3329254 _86951 s)). Qed.
Lemma lem3329256 {_86951 : Type'} (s : type686 _86951) : (term200 _86951 s) = (term201 _86951 s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3329255 _86951 t s)). Qed.
Lemma lem3329257 {_86951 : Type'} : (@ex (_86951 -> Prop)) = (@ex (_86951 -> Prop)).
Proof. exact (eq_refl (@ex (_86951 -> Prop))). Qed.
Lemma lem3329258 {_86951 : Type'} (s : type686 _86951) : (term189 _86951 s) = (term202 _86951 s).
Proof. exact (MK_COMB (@lem3329257 _86951) (@lem3329256 _86951 s)). Qed.
Lemma lem3329259 {_86951 : Type'} (s : type686 _86951) : ((term188 _86951 s) = (term189 _86951 s)) = ((term183 _86951 s) = (term202 _86951 s)).
Proof. exact (MK_COMB (@lem3329250 _86951 s) (@lem3329258 _86951 s)). Qed.
Lemma lem3329260 {_86951 : Type'} (s : type686 _86951) : (term183 _86951 s) = (term202 _86951 s).
Proof. exact (EQ_MP (@lem3329259 _86951 s) (@lem3329240 _86951 s)). Qed.
Lemma lem3329262 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term203 A P Q) = (term204 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3329263 {_86951 : Type'} (P : _86951 -> Prop) (Q : _86951 -> Prop) : (term203 _86951 P Q) = (term204 _86951 P Q).
Proof. exact (@lem3329262 _86951 P Q). Qed.
Lemma lem3329264 {_86951 : Type'} (t : _86951 -> Prop) (s : type686 _86951) : (term205 _86951 t s) = (term206 _86951 t s).
Proof. exact (@lem3329263 _86951 (term143 _86951 s t) (term181 _86951 s)). Qed.
Lemma lem3329265 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term207 _86951 s t x) = (term141 _86951 s t x).
Proof. exact (eq_refl (term207 _86951 s t x)). Qed.
Lemma lem3329266 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term208 _86951 s t) = (term143 _86951 s t).
Proof. exact (fun_ext (fun x : _86951 => @lem3329265 _86951 s t x)). Qed.
Lemma lem3329267 {_86951 : Type'} : (@ex _86951) = (@ex _86951).
Proof. exact (eq_refl (@ex _86951)). Qed.
Lemma lem3329268 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term209 _86951 s t) = (term144 _86951 s t).
Proof. exact (MK_COMB (@lem3329267 _86951) (@lem3329266 _86951 s t)). Qed.
Lemma lem3329269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3329270 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term210 _86951 s t) = (term197 _86951 s t).
Proof. exact (MK_COMB (@lem3329269) (@lem3329268 _86951 s t)). Qed.
Lemma lem3329271 {_86951 : Type'} (x : _86951) (s : type686 _86951) : (term211 _86951 s x) = (term180 _86951 x s).
Proof. exact (eq_refl (term211 _86951 s x)). Qed.
Lemma lem3329272 {_86951 : Type'} (s : type686 _86951) : (term212 _86951 s) = (term181 _86951 s).
Proof. exact (fun_ext (fun x : _86951 => @lem3329271 _86951 x s)). Qed.
Lemma lem3329273 {_86951 : Type'} : (@ex _86951) = (@ex _86951).
Proof. exact (eq_refl (@ex _86951)). Qed.
Lemma lem3329274 {_86951 : Type'} (s : type686 _86951) : (term213 _86951 s) = (term182 _86951 s).
Proof. exact (MK_COMB (@lem3329273 _86951) (@lem3329272 _86951 s)). Qed.
Lemma lem3329275 {_86951 : Type'} (t : _86951 -> Prop) (s : type686 _86951) : (term205 _86951 t s) = (term199 _86951 t s).
Proof. exact (MK_COMB (@lem3329270 _86951 s t) (@lem3329274 _86951 s)). Qed.
Lemma lem3329276 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3329277 {_86951 : Type'} (t : _86951 -> Prop) (s : type686 _86951) : (term214 _86951 t s) = (term215 _86951 t s).
Proof. exact (MK_COMB (@lem3329276) (@lem3329275 _86951 t s)). Qed.
Lemma lem3329278 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term207 _86951 s t x) = (term141 _86951 s t x).
Proof. exact (eq_refl (term207 _86951 s t x)). Qed.
Lemma lem3329279 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3329280 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term216 _86951 s t x) = (term217 _86951 s t x).
Proof. exact (MK_COMB (@lem3329279) (@lem3329278 _86951 s t x)). Qed.
Lemma lem3329281 {_86951 : Type'} (x : _86951) (s : type686 _86951) : (term211 _86951 s x) = (term180 _86951 x s).
Proof. exact (eq_refl (term211 _86951 s x)). Qed.
Lemma lem3329282 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) (s : type686 _86951) : (term218 _86951 t s x) = (term219 _86951 t x s).
Proof. exact (MK_COMB (@lem3329280 _86951 s t x) (@lem3329281 _86951 x s)). Qed.
Lemma lem3329283 {_86951 : Type'} (t : _86951 -> Prop) (s : type686 _86951) : (term220 _86951 t s) = (term221 _86951 t s).
Proof. exact (fun_ext (fun x : _86951 => @lem3329282 _86951 t x s)). Qed.
Lemma lem3329284 {_86951 : Type'} : (@ex _86951) = (@ex _86951).
Proof. exact (eq_refl (@ex _86951)). Qed.
Lemma lem3329285 {_86951 : Type'} (t : _86951 -> Prop) (s : type686 _86951) : (term206 _86951 t s) = (term222 _86951 t s).
Proof. exact (MK_COMB (@lem3329284 _86951) (@lem3329283 _86951 t s)). Qed.
Lemma lem3329286 {_86951 : Type'} (t : _86951 -> Prop) (s : type686 _86951) : ((term205 _86951 t s) = (term206 _86951 t s)) = ((term199 _86951 t s) = (term222 _86951 t s)).
Proof. exact (MK_COMB (@lem3329277 _86951 t s) (@lem3329285 _86951 t s)). Qed.
Lemma lem3329287 {_86951 : Type'} (t : _86951 -> Prop) (s : type686 _86951) : (term199 _86951 t s) = (term222 _86951 t s).
Proof. exact (EQ_MP (@lem3329286 _86951 t s) (@lem3329264 _86951 t s)). Qed.
Lemma lem3329289 {A : Type'} (P : Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3329290 {_86951 : Type'} (P : Prop) (Q : type686 _86951) : (term225 _86951 P Q) = (term226 _86951 P Q).
Proof. exact (@lem3329289 (_86951 -> Prop) P Q). Qed.
Lemma lem3329291 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) (s : type686 _86951) : (term227 _86951 t x s) = (term228 _86951 t x s).
Proof. exact (@lem3329290 _86951 (term141 _86951 s t x) (term179 _86951 x s)). Qed.
Lemma lem3329292 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) (s : type686 _86951) : (term229 _86951 x s t) = (term177 _86951 t x s).
Proof. exact (eq_refl (term229 _86951 x s t)). Qed.
Lemma lem3329293 {_86951 : Type'} (x : _86951) (s : type686 _86951) : (term230 _86951 x s) = (term179 _86951 x s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3329292 _86951 t x s)). Qed.
Lemma lem3329294 {_86951 : Type'} : (@ex (_86951 -> Prop)) = (@ex (_86951 -> Prop)).
Proof. exact (eq_refl (@ex (_86951 -> Prop))). Qed.
Lemma lem3329295 {_86951 : Type'} (x : _86951) (s : type686 _86951) : (term231 _86951 x s) = (term180 _86951 x s).
Proof. exact (MK_COMB (@lem3329294 _86951) (@lem3329293 _86951 x s)). Qed.
Lemma lem3329296 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term217 _86951 s t x) = (term217 _86951 s t x).
Proof. exact (eq_refl (term217 _86951 s t x)). Qed.
Lemma lem3329297 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) (s : type686 _86951) : (term227 _86951 t x s) = (term219 _86951 t x s).
Proof. exact (MK_COMB (@lem3329296 _86951 s t x) (@lem3329295 _86951 x s)). Qed.
Lemma lem3329298 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3329299 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) (s : type686 _86951) : (term232 _86951 t x s) = (term233 _86951 t x s).
Proof. exact (MK_COMB (@lem3329298) (@lem3329297 _86951 t x s)). Qed.
Lemma lem3329300 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) : (term229 _86951 x s t') = (term177 _86951 t' x s).
Proof. exact (eq_refl (term229 _86951 x s t')). Qed.
Lemma lem3329301 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term217 _86951 s t x) = (term217 _86951 s t x).
Proof. exact (eq_refl (term217 _86951 s t x)). Qed.
Lemma lem3329302 {_86951 : Type'} (t : _86951 -> Prop) (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) : (term234 _86951 t x s t') = (term235 _86951 t t' x s).
Proof. exact (MK_COMB (@lem3329301 _86951 s t x) (@lem3329300 _86951 t' x s)). Qed.
Lemma lem3329303 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) (s : type686 _86951) : (term236 _86951 t x s) = (term237 _86951 t x s).
Proof. exact (fun_ext (fun t' : _86951 -> Prop => @lem3329302 _86951 t t' x s)). Qed.
Lemma lem3329304 {_86951 : Type'} : (@ex (_86951 -> Prop)) = (@ex (_86951 -> Prop)).
Proof. exact (eq_refl (@ex (_86951 -> Prop))). Qed.
Lemma lem3329305 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) (s : type686 _86951) : (term228 _86951 t x s) = (term238 _86951 t x s).
Proof. exact (MK_COMB (@lem3329304 _86951) (@lem3329303 _86951 t x s)). Qed.
Lemma lem3329306 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) (s : type686 _86951) : ((term227 _86951 t x s) = (term228 _86951 t x s)) = ((term219 _86951 t x s) = (term238 _86951 t x s)).
Proof. exact (MK_COMB (@lem3329299 _86951 t x s) (@lem3329305 _86951 t x s)). Qed.
Lemma lem3329307 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) (s : type686 _86951) : (term219 _86951 t x s) = (term238 _86951 t x s).
Proof. exact (EQ_MP (@lem3329306 _86951 t x s) (@lem3329291 _86951 t x s)). Qed.
Lemma lem3329308 {_86951 : Type'} (t : _86951 -> Prop) (s : type686 _86951) : (term221 _86951 t s) = (term239 _86951 t s).
Proof. exact (fun_ext (fun x : _86951 => @lem3329307 _86951 t x s)). Qed.
Lemma lem3329309 {_86951 : Type'} : (@ex _86951) = (@ex _86951).
Proof. exact (eq_refl (@ex _86951)). Qed.
Lemma lem3329310 {_86951 : Type'} (t : _86951 -> Prop) (s : type686 _86951) : (term222 _86951 t s) = (term240 _86951 t s).
Proof. exact (MK_COMB (@lem3329309 _86951) (@lem3329308 _86951 t s)). Qed.
Lemma lem3329311 {_86951 : Type'} (t : _86951 -> Prop) (s : type686 _86951) : (term199 _86951 t s) = (term240 _86951 t s).
Proof. exact (TRANS (@lem3329287 _86951 t s) (@lem3329310 _86951 t s)). Qed.
Lemma lem3329312 {_86951 : Type'} (s : type686 _86951) : (term201 _86951 s) = (term241 _86951 s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3329311 _86951 t s)). Qed.
Lemma lem3329313 {_86951 : Type'} : (@ex (_86951 -> Prop)) = (@ex (_86951 -> Prop)).
Proof. exact (eq_refl (@ex (_86951 -> Prop))). Qed.
Lemma lem3329314 {_86951 : Type'} (s : type686 _86951) : (term202 _86951 s) = (term242 _86951 s).
Proof. exact (MK_COMB (@lem3329313 _86951) (@lem3329312 _86951 s)). Qed.
Lemma lem3329315 {_86951 : Type'} (s : type686 _86951) : (term183 _86951 s) = (term242 _86951 s).
Proof. exact (TRANS (@lem3329260 _86951 s) (@lem3329314 _86951 s)). Qed.
Lemma lem3329317 {_86951 : Type'} (s : type686 _86951) : (term111 _86951 s) = (term242 _86951 s).
Proof. exact (TRANS (@lem3329234 _86951 s) (@lem3329315 _86951 s)). Qed.
Lemma lem3329318 {_86951 : Type'} (s : type686 _86951) : (term53 _86951 s) = (term242 _86951 s).
Proof. exact (TRANS (@lem3328956 _86951 s) (@lem3329317 _86951 s)). Qed.
Lemma lem3329319 {_86951 : Type'} (s : type686 _86951) (h1 : term53 _86951 s) : term242 _86951 s.
Proof. exact (EQ_MP (@lem3329318 _86951 s) (@lem3328863 _86951 s h1)). Qed.
Lemma lem3329320 {_86951 : Type'} (t : _86951 -> Prop) (s : type686 _86951) (h1 : term240 _86951 t s) : term240 _86951 t s.
Proof. exact (h1). Qed.
Lemma lem3329321 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term238 _86951 t x s) : term238 _86951 t x s.
Proof. exact (h1). Qed.
Lemma lem3329322 {_86951 : Type'} (t : _86951 -> Prop) (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term235 _86951 t t' x s) : term235 _86951 t t' x s.
Proof. exact (h1). Qed.
Lemma lem3329323 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3329328 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3329329 {_86951 : Type'} (f : _86951 -> Prop) (x : _86951) : (f x) = (@I (_86951 -> Prop) f x).
Proof. exact (@lem3329328 _86951 Prop f x). Qed.
Lemma lem3329331 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (t x) = (@I (_86951 -> Prop) t x).
Proof. exact (@lem3329329 _86951 t x). Qed.
Lemma lem3329332 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (term35 _86951 t x) = (term243 _86951 t x).
Proof. exact (MK_COMB (@lem3329323) (@lem3329331 _86951 t x)). Qed.
Lemma lem3329333 {_86951 : Type'} (t : _86951 -> Prop) : (term37 _86951 t) = (term244 _86951 t).
Proof. exact (fun_ext (fun x : _86951 => @lem3329332 _86951 t x)). Qed.
Lemma lem3329334 {_86951 : Type'} : (@all _86951) = (@all _86951).
Proof. exact (eq_refl (@all _86951)). Qed.
Lemma lem3329335 {_86951 : Type'} (t : _86951 -> Prop) : (term38 _86951 t) = (term245 _86951 t).
Proof. exact (MK_COMB (@lem3329334 _86951) (@lem3329333 _86951 t)). Qed.
Lemma lem3329336 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3329341 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3329342 {_86951 : Type'} (f : type686 _86951) (x : _86951 -> Prop) : (f x) = (@I ((_86951 -> Prop) -> Prop) f x).
Proof. exact (@lem3329341 (_86951 -> Prop) Prop f x). Qed.
Lemma lem3329344 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (s t) = (@I ((_86951 -> Prop) -> Prop) s t).
Proof. exact (@lem3329342 _86951 s t). Qed.
Lemma lem3329345 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term246 _86951 s t) = (term247 _86951 s t).
Proof. exact (MK_COMB (@lem3329336) (@lem3329344 _86951 s t)). Qed.
Lemma lem3329346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3329347 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term87 _86951 s t) = (term248 _86951 s t).
Proof. exact (MK_COMB (@lem3329346) (@lem3329345 _86951 s t)). Qed.
Lemma lem3329348 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term88 _86951 s t) = (term249 _86951 s t).
Proof. exact (MK_COMB (@lem3329347 _86951 s t) (@lem3329335 _86951 t)). Qed.
Lemma lem3329349 {_86951 : Type'} (s : type686 _86951) : (term98 _86951 s) = (term250 _86951 s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3329348 _86951 s t)). Qed.
Lemma lem3329350 {_86951 : Type'} : (@all (_86951 -> Prop)) = (@all (_86951 -> Prop)).
Proof. exact (eq_refl (@all (_86951 -> Prop))). Qed.
Lemma lem3329351 {_86951 : Type'} (s : type686 _86951) : (term99 _86951 s) = (term251 _86951 s).
Proof. exact (MK_COMB (@lem3329350 _86951) (@lem3329349 _86951 s)). Qed.
Lemma lem3329356 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3329357 {_86951 : Type'} (f : _86951 -> Prop) (x : _86951) : (f x) = (@I (_86951 -> Prop) f x).
Proof. exact (@lem3329356 _86951 Prop f x). Qed.
Lemma lem3329359 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) : (t' x) = (@I (_86951 -> Prop) t' x).
Proof. exact (@lem3329357 _86951 t' x). Qed.
Lemma lem3329364 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3329365 {_86951 : Type'} (f : type686 _86951) (x : _86951 -> Prop) : (f x) = (@I ((_86951 -> Prop) -> Prop) f x).
Proof. exact (@lem3329364 (_86951 -> Prop) Prop f x). Qed.
Lemma lem3329367 {_86951 : Type'} (s : type686 _86951) (t' : _86951 -> Prop) : (s t') = (@I ((_86951 -> Prop) -> Prop) s t').
Proof. exact (@lem3329365 _86951 s t'). Qed.
Lemma lem3329368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3329369 {_86951 : Type'} (s : type686 _86951) (t' : _86951 -> Prop) : (term19 _86951 s t') = (term252 _86951 s t').
Proof. exact (MK_COMB (@lem3329368) (@lem3329367 _86951 s t')). Qed.
Lemma lem3329370 {_86951 : Type'} (s : type686 _86951) (t' : _86951 -> Prop) (x : _86951) : (term21 _86951 s t' x) = (term253 _86951 s t' x).
Proof. exact (MK_COMB (@lem3329369 _86951 s t') (@lem3329359 _86951 t' x)). Qed.
Lemma lem3329371 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3329372 {_86951 : Type'} (s : type686 _86951) (t' : _86951 -> Prop) (x : _86951) : (term175 _86951 s t' x) = (term254 _86951 s t' x).
Proof. exact (MK_COMB (@lem3329371) (@lem3329370 _86951 s t' x)). Qed.
Lemma lem3329373 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) : (term177 _86951 t' x s) = (term255 _86951 t' x s).
Proof. exact (MK_COMB (@lem3329372 _86951 s t' x) (@lem3329351 _86951 s)). Qed.
Lemma lem3329378 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3329379 {_86951 : Type'} (f : _86951 -> Prop) (x : _86951) : (f x) = (@I (_86951 -> Prop) f x).
Proof. exact (@lem3329378 _86951 Prop f x). Qed.
Lemma lem3329381 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (t x) = (@I (_86951 -> Prop) t x).
Proof. exact (@lem3329379 _86951 t x). Qed.
Lemma lem3329386 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3329387 {_86951 : Type'} (f : type686 _86951) (x : _86951 -> Prop) : (f x) = (@I ((_86951 -> Prop) -> Prop) f x).
Proof. exact (@lem3329386 (_86951 -> Prop) Prop f x). Qed.
Lemma lem3329389 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (s t) = (@I ((_86951 -> Prop) -> Prop) s t).
Proof. exact (@lem3329387 _86951 s t). Qed.
Lemma lem3329390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3329391 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term19 _86951 s t) = (term252 _86951 s t).
Proof. exact (MK_COMB (@lem3329390) (@lem3329389 _86951 s t)). Qed.
Lemma lem3329392 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term21 _86951 s t x) = (term253 _86951 s t x).
Proof. exact (MK_COMB (@lem3329391 _86951 s t) (@lem3329381 _86951 t x)). Qed.
Lemma lem3329393 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3329398 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3329399 {_86951 : Type'} (f : _86951 -> Prop) (x : _86951) : (f x) = (@I (_86951 -> Prop) f x).
Proof. exact (@lem3329398 _86951 Prop f x). Qed.
Lemma lem3329401 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (t x) = (@I (_86951 -> Prop) t x).
Proof. exact (@lem3329399 _86951 t x). Qed.
Lemma lem3329402 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (term35 _86951 t x) = (term243 _86951 t x).
Proof. exact (MK_COMB (@lem3329393) (@lem3329401 _86951 t x)). Qed.
Lemma lem3329403 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3329408 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3329409 {_86951 : Type'} (f : type686 _86951) (x : _86951 -> Prop) : (f x) = (@I ((_86951 -> Prop) -> Prop) f x).
Proof. exact (@lem3329408 (_86951 -> Prop) Prop f x). Qed.
Lemma lem3329411 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (s t) = (@I ((_86951 -> Prop) -> Prop) s t).
Proof. exact (@lem3329409 _86951 s t). Qed.
Lemma lem3329412 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term246 _86951 s t) = (term247 _86951 s t).
Proof. exact (MK_COMB (@lem3329403) (@lem3329411 _86951 s t)). Qed.
Lemma lem3329413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3329414 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term87 _86951 s t) = (term248 _86951 s t).
Proof. exact (MK_COMB (@lem3329413) (@lem3329412 _86951 s t)). Qed.
Lemma lem3329415 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term55 _86951 s t x) = (term256 _86951 s t x).
Proof. exact (MK_COMB (@lem3329414 _86951 s t) (@lem3329402 _86951 t x)). Qed.
Lemma lem3329416 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term62 _86951 s x) = (term257 _86951 s x).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3329415 _86951 s t x)). Qed.
Lemma lem3329417 {_86951 : Type'} : (@all (_86951 -> Prop)) = (@all (_86951 -> Prop)).
Proof. exact (eq_refl (@all (_86951 -> Prop))). Qed.
Lemma lem3329418 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term63 _86951 s x) = (term258 _86951 s x).
Proof. exact (MK_COMB (@lem3329417 _86951) (@lem3329416 _86951 s x)). Qed.
Lemma lem3329419 {_86951 : Type'} (s : type686 _86951) : (term74 _86951 s) = (term259 _86951 s).
Proof. exact (fun_ext (fun x : _86951 => @lem3329418 _86951 s x)). Qed.
Lemma lem3329420 {_86951 : Type'} : (@all _86951) = (@all _86951).
Proof. exact (eq_refl (@all _86951)). Qed.
Lemma lem3329421 {_86951 : Type'} (s : type686 _86951) : (term75 _86951 s) = (term260 _86951 s).
Proof. exact (MK_COMB (@lem3329420 _86951) (@lem3329419 _86951 s)). Qed.
Lemma lem3329422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3329423 {_86951 : Type'} (s : type686 _86951) : (term105 _86951 s) = (term261 _86951 s).
Proof. exact (MK_COMB (@lem3329422) (@lem3329421 _86951 s)). Qed.
Lemma lem3329424 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term141 _86951 s t x) = (term262 _86951 s t x).
Proof. exact (MK_COMB (@lem3329423 _86951 s) (@lem3329392 _86951 s t x)). Qed.
Lemma lem3329425 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3329426 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term217 _86951 s t x) = (term263 _86951 s t x).
Proof. exact (MK_COMB (@lem3329425) (@lem3329424 _86951 s t x)). Qed.
Lemma lem3329427 {_86951 : Type'} (t : _86951 -> Prop) (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) : (term235 _86951 t t' x s) = (term264 _86951 t t' x s).
Proof. exact (MK_COMB (@lem3329426 _86951 s t x) (@lem3329373 _86951 t' x s)). Qed.
Lemma lem3329428 {_86951 : Type'} (t : _86951 -> Prop) (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term235 _86951 t t' x s) : term264 _86951 t t' x s.
Proof. exact (EQ_MP (@lem3329427 _86951 t t' x s) (@lem3329322 _86951 t t' x s h1)). Qed.
Lemma lem3329429 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : term262 _86951 s t x.
Proof. exact (h1). Qed.
Lemma lem3329430 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : term255 _86951 t' x s.
Proof. exact (h1). Qed.
Lemma lem3329431 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : term253 _86951 s t x.
Proof. exact (proj2 (@lem3329429 _86951 s t x h1)). Qed.
Lemma lem3329432 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : term260 _86951 s.
Proof. exact (proj1 (@lem3329429 _86951 s t x h1)). Qed.
Lemma lem3329435 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : term251 _86951 s.
Proof. exact (proj2 (@lem3329430 _86951 t' x s h1)). Qed.
Lemma lem3329436 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : term253 _86951 s t' x.
Proof. exact (proj1 (@lem3329430 _86951 t' x s h1)). Qed.
Lemma lem3329446 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term256 _86951 s t x) = (term256 _86951 s t x).
Proof. exact (eq_refl (term256 _86951 s t x)). Qed.
Lemma lem3329447 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term257 _86951 s x) = (term257 _86951 s x).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3329446 _86951 s t x)). Qed.
Lemma lem3329448 {_86951 : Type'} : (@all (_86951 -> Prop)) = (@all (_86951 -> Prop)).
Proof. exact (eq_refl (@all (_86951 -> Prop))). Qed.
Lemma lem3329449 {_86951 : Type'} (s : type686 _86951) (x : _86951) : (term258 _86951 s x) = (term258 _86951 s x).
Proof. exact (MK_COMB (@lem3329448 _86951) (@lem3329447 _86951 s x)). Qed.
Lemma lem3329450 {_86951 : Type'} (s : type686 _86951) : (term259 _86951 s) = (term259 _86951 s).
Proof. exact (fun_ext (fun x : _86951 => @lem3329449 _86951 s x)). Qed.
Lemma lem3329451 {_86951 : Type'} : (@all _86951) = (@all _86951).
Proof. exact (eq_refl (@all _86951)). Qed.
Lemma lem3329453 {_86951 : Type'} (s : type686 _86951) : (term260 _86951 s) = (term260 _86951 s).
Proof. exact (MK_COMB (@lem3329451 _86951) (@lem3329450 _86951 s)). Qed.
Lemma lem3329454 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : term260 _86951 s.
Proof. exact (EQ_MP (@lem3329453 _86951 s) (@lem3329432 _86951 s t x h1)). Qed.
Lemma lem3329464 {A : Type'} (P : Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3329465 {_86951 : Type'} (P : Prop) (Q : _86951 -> Prop) : (term265 _86951 P Q) = (term266 _86951 P Q).
Proof. exact (@lem3329464 _86951 P Q). Qed.
Lemma lem3329466 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term267 _86951 s t) = (term268 _86951 s t).
Proof. exact (@lem3329465 _86951 (term247 _86951 s t) (term244 _86951 t)). Qed.
Lemma lem3329467 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (term269 _86951 t x) = (term243 _86951 t x).
Proof. exact (eq_refl (term269 _86951 t x)). Qed.
Lemma lem3329468 {_86951 : Type'} (t : _86951 -> Prop) : (term270 _86951 t) = (term244 _86951 t).
Proof. exact (fun_ext (fun x : _86951 => @lem3329467 _86951 t x)). Qed.
Lemma lem3329469 {_86951 : Type'} : (@all _86951) = (@all _86951).
Proof. exact (eq_refl (@all _86951)). Qed.
Lemma lem3329470 {_86951 : Type'} (t : _86951 -> Prop) : (term271 _86951 t) = (term245 _86951 t).
Proof. exact (MK_COMB (@lem3329469 _86951) (@lem3329468 _86951 t)). Qed.
Lemma lem3329471 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term248 _86951 s t) = (term248 _86951 s t).
Proof. exact (eq_refl (term248 _86951 s t)). Qed.
Lemma lem3329472 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term267 _86951 s t) = (term249 _86951 s t).
Proof. exact (MK_COMB (@lem3329471 _86951 s t) (@lem3329470 _86951 t)). Qed.
Lemma lem3329473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3329474 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term272 _86951 s t) = (term273 _86951 s t).
Proof. exact (MK_COMB (@lem3329473) (@lem3329472 _86951 s t)). Qed.
Lemma lem3329475 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (term269 _86951 t x) = (term243 _86951 t x).
Proof. exact (eq_refl (term269 _86951 t x)). Qed.
Lemma lem3329476 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term248 _86951 s t) = (term248 _86951 s t).
Proof. exact (eq_refl (term248 _86951 s t)). Qed.
Lemma lem3329477 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term274 _86951 s t x) = (term256 _86951 s t x).
Proof. exact (MK_COMB (@lem3329476 _86951 s t) (@lem3329475 _86951 t x)). Qed.
Lemma lem3329478 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term275 _86951 s t) = (term276 _86951 s t).
Proof. exact (fun_ext (fun x : _86951 => @lem3329477 _86951 s t x)). Qed.
Lemma lem3329479 {_86951 : Type'} : (@all _86951) = (@all _86951).
Proof. exact (eq_refl (@all _86951)). Qed.
Lemma lem3329480 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term268 _86951 s t) = (term277 _86951 s t).
Proof. exact (MK_COMB (@lem3329479 _86951) (@lem3329478 _86951 s t)). Qed.
Lemma lem3329481 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : ((term267 _86951 s t) = (term268 _86951 s t)) = ((term249 _86951 s t) = (term277 _86951 s t)).
Proof. exact (MK_COMB (@lem3329474 _86951 s t) (@lem3329480 _86951 s t)). Qed.
Lemma lem3329482 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term249 _86951 s t) = (term277 _86951 s t).
Proof. exact (EQ_MP (@lem3329481 _86951 s t) (@lem3329466 _86951 s t)). Qed.
Lemma lem3329483 {_86951 : Type'} (s : type686 _86951) : (term250 _86951 s) = (term278 _86951 s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3329482 _86951 s t)). Qed.
Lemma lem3329484 {_86951 : Type'} : (@all (_86951 -> Prop)) = (@all (_86951 -> Prop)).
Proof. exact (eq_refl (@all (_86951 -> Prop))). Qed.
Lemma lem3329485 {_86951 : Type'} (s : type686 _86951) : (term251 _86951 s) = (term279 _86951 s).
Proof. exact (MK_COMB (@lem3329484 _86951) (@lem3329483 _86951 s)). Qed.
Lemma lem3329492 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) : (term256 _86951 s t x) = (term256 _86951 s t x).
Proof. exact (eq_refl (term256 _86951 s t x)). Qed.
Lemma lem3329493 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term276 _86951 s t) = (term276 _86951 s t).
Proof. exact (fun_ext (fun x : _86951 => @lem3329492 _86951 s t x)). Qed.
Lemma lem3329494 {_86951 : Type'} : (@all _86951) = (@all _86951).
Proof. exact (eq_refl (@all _86951)). Qed.
Lemma lem3329495 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term277 _86951 s t) = (term277 _86951 s t).
Proof. exact (MK_COMB (@lem3329494 _86951) (@lem3329493 _86951 s t)). Qed.
Lemma lem3329496 {_86951 : Type'} (s : type686 _86951) : (term278 _86951 s) = (term278 _86951 s).
Proof. exact (fun_ext (fun t : _86951 -> Prop => @lem3329495 _86951 s t)). Qed.
Lemma lem3329497 {_86951 : Type'} : (@all (_86951 -> Prop)) = (@all (_86951 -> Prop)).
Proof. exact (eq_refl (@all (_86951 -> Prop))). Qed.
Lemma lem3329498 {_86951 : Type'} (s : type686 _86951) : (term279 _86951 s) = (term279 _86951 s).
Proof. exact (MK_COMB (@lem3329497 _86951) (@lem3329496 _86951 s)). Qed.
Lemma lem3329499 {_86951 : Type'} (s : type686 _86951) : (term251 _86951 s) = (term279 _86951 s).
Proof. exact (TRANS (@lem3329485 _86951 s) (@lem3329498 _86951 s)). Qed.
Lemma lem3329500 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : term279 _86951 s.
Proof. exact (EQ_MP (@lem3329499 _86951 s) (@lem3329435 _86951 t' x s h1)). Qed.
Lemma lem3329509 {_86951 : Type'} (_34537 : _86951) (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : term280 _86951 s _34537.
Proof. exact (@lem3329454 _86951 s t x h1 _34537). Qed.
Lemma lem3329510 {_86951 : Type'} (s : type686 _86951) (_34537 : _86951) : (term280 _86951 s _34537) = (term258 _86951 s _34537).
Proof. exact (eq_refl (term280 _86951 s _34537)). Qed.
Lemma lem3329511 {_86951 : Type'} (_34537 : _86951) (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : term258 _86951 s _34537.
Proof. exact (EQ_MP (@lem3329510 _86951 s _34537) (@lem3329509 _86951 _34537 s t x h1)). Qed.
Lemma lem3329512 {_86951 : Type'} (_34537 : _86951) (_34538 : _86951 -> Prop) (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : term281 _86951 s _34537 _34538.
Proof. exact (@lem3329511 _86951 _34537 s t x h1 _34538). Qed.
Lemma lem3329513 {_86951 : Type'} (s : type686 _86951) (_34538 : _86951 -> Prop) (_34537 : _86951) : (term281 _86951 s _34537 _34538) = (term256 _86951 s _34538 _34537).
Proof. exact (eq_refl (term281 _86951 s _34537 _34538)). Qed.
Lemma lem3329515 {_86951 : Type'} (_34539 : _86951 -> Prop) (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : term282 _86951 s _34539.
Proof. exact (@lem3329500 _86951 t' x s h1 _34539). Qed.
Lemma lem3329516 {_86951 : Type'} (s : type686 _86951) (_34539 : _86951 -> Prop) : (term282 _86951 s _34539) = (term277 _86951 s _34539).
Proof. exact (eq_refl (term282 _86951 s _34539)). Qed.
Lemma lem3329517 {_86951 : Type'} (_34539 : _86951 -> Prop) (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : term277 _86951 s _34539.
Proof. exact (EQ_MP (@lem3329516 _86951 s _34539) (@lem3329515 _86951 _34539 t' x s h1)). Qed.
Lemma lem3329518 {_86951 : Type'} (_34539 : _86951 -> Prop) (_34540 : _86951) (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : term283 _86951 s _34539 _34540.
Proof. exact (@lem3329517 _86951 _34539 t' x s h1 _34540). Qed.
Lemma lem3329519 {_86951 : Type'} (s : type686 _86951) (_34539 : _86951 -> Prop) (_34540 : _86951) : (term283 _86951 s _34539 _34540) = (term256 _86951 s _34539 _34540).
Proof. exact (eq_refl (term283 _86951 s _34539 _34540)). Qed.
Lemma lem3329526 {_86951 : Type'} (_34538 : _86951 -> Prop) (_34537 : _86951) (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : term256 _86951 s _34538 _34537.
Proof. exact (EQ_MP (@lem3329513 _86951 s _34538 _34537) (@lem3329512 _86951 _34537 _34538 s t x h1)). Qed.
Lemma lem3329536 {_86951 : Type'} (_34539 : _86951 -> Prop) (_34540 : _86951) (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : term256 _86951 s _34539 _34540.
Proof. exact (EQ_MP (@lem3329519 _86951 s _34539 _34540) (@lem3329518 _86951 _34539 _34540 t' x s h1)). Qed.
Lemma lem3329542 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : @I ((_86951 -> Prop) -> Prop) s t.
Proof. exact (proj1 (@lem3329431 _86951 s t x h1)). Qed.
Lemma lem3329543 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : term284 _86951 s t.
Proof. exact (fun h0 : term247 _86951 s t => @lem3329542 _86951 s t x h1). Qed.
Lemma lem3329545 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3329546 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) : (term284 _86951 s t) = (@I ((_86951 -> Prop) -> Prop) s t).
Proof. exact (@lem3329545 (@I ((_86951 -> Prop) -> Prop) s t)). Qed.
Lemma lem3329547 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : @I ((_86951 -> Prop) -> Prop) s t.
Proof. exact (EQ_MP (@lem3329546 _86951 s t) (@lem3329543 _86951 s t x h1)). Qed.
Lemma lem3329549 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : @I (_86951 -> Prop) t x.
Proof. exact (proj2 (@lem3329431 _86951 s t x h1)). Qed.
Lemma lem3329550 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : term286 _86951 t x.
Proof. exact (fun h0 : term243 _86951 t x => @lem3329549 _86951 s t x h1). Qed.
Lemma lem3329552 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3329553 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) : (term286 _86951 t x) = (@I (_86951 -> Prop) t x).
Proof. exact (@lem3329552 (@I (_86951 -> Prop) t x)). Qed.
Lemma lem3329554 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : @I (_86951 -> Prop) t x.
Proof. exact (EQ_MP (@lem3329553 _86951 t x) (@lem3329550 _86951 s t x h1)). Qed.
Lemma lem3329556 (a : Prop) (b : Prop) : (term287 a b) = (term288 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3329557 {_86951 : Type'} (s : type686 _86951) (_34538 : _86951 -> Prop) (_34537 : _86951) : (term256 _86951 s _34538 _34537) = (term289 _86951 s _34538 _34537).
Proof. exact (@lem3329556 (@I ((_86951 -> Prop) -> Prop) s _34538) (@I (_86951 -> Prop) _34538 _34537)). Qed.
Lemma lem3329559 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3329560 {_86951 : Type'} (s : type686 _86951) (_34538 : _86951 -> Prop) (_34537 : _86951) : (term289 _86951 s _34538 _34537) = (term290 _86951 s _34538 _34537).
Proof. exact (@lem3329559 (term253 _86951 s _34538 _34537)). Qed.
Lemma lem3329561 {_86951 : Type'} (s : type686 _86951) (_34538 : _86951 -> Prop) (_34537 : _86951) : (term256 _86951 s _34538 _34537) = (term290 _86951 s _34538 _34537).
Proof. exact (TRANS (@lem3329557 _86951 s _34538 _34537) (@lem3329560 _86951 s _34538 _34537)). Qed.
Lemma lem3329563 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : term253 _86951 s t x.
Proof. exact (conj (@lem3329547 _86951 s t x h1) (@lem3329554 _86951 s t x h1)). Qed.
Lemma lem3329565 {_86951 : Type'} (_34538 : _86951 -> Prop) (_34537 : _86951) (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : term290 _86951 s _34538 _34537.
Proof. exact (EQ_MP (@lem3329561 _86951 s _34538 _34537) (@lem3329526 _86951 _34538 _34537 s t x h1)). Qed.
Lemma lem3329566 {_86951 : Type'} (_34538 : _86951 -> Prop) (_34537 : _86951) (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : term290 _86951 s _34538 _34537.
Proof. exact (@lem3329565 _86951 _34538 _34537 s t x h1). Qed.
Lemma lem3329567 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : term290 _86951 s t x.
Proof. exact (@lem3329566 _86951 t x s t x h1). Qed.
Lemma lem3329570 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : False.
Proof. exact (@lem3329567 _86951 s t x h1 (@lem3329563 _86951 s t x h1)). Qed.
Lemma lem3329571 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : term291.
Proof. exact (fun h0 : ~ False => @lem3329570 _86951 s t x h1). Qed.
Lemma lem3329573 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3329574 : term291 = False.
Proof. exact (@lem3329573 False). Qed.
Lemma lem3329575 {_86951 : Type'} (s : type686 _86951) (t : _86951 -> Prop) (x : _86951) (h1 : term262 _86951 s t x) : False.
Proof. exact (EQ_MP (@lem3329574) (@lem3329571 _86951 s t x h1)). Qed.
Lemma lem3329577 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : @I ((_86951 -> Prop) -> Prop) s t'.
Proof. exact (proj1 (@lem3329436 _86951 t' x s h1)). Qed.
Lemma lem3329578 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : term284 _86951 s t'.
Proof. exact (fun h0 : term247 _86951 s t' => @lem3329577 _86951 t' x s h1). Qed.
Lemma lem3329580 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3329581 {_86951 : Type'} (s : type686 _86951) (t' : _86951 -> Prop) : (term284 _86951 s t') = (@I ((_86951 -> Prop) -> Prop) s t').
Proof. exact (@lem3329580 (@I ((_86951 -> Prop) -> Prop) s t')). Qed.
Lemma lem3329582 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : @I ((_86951 -> Prop) -> Prop) s t'.
Proof. exact (EQ_MP (@lem3329581 _86951 s t') (@lem3329578 _86951 t' x s h1)). Qed.
Lemma lem3329584 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : @I (_86951 -> Prop) t' x.
Proof. exact (proj2 (@lem3329436 _86951 t' x s h1)). Qed.
Lemma lem3329585 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : term286 _86951 t' x.
Proof. exact (fun h0 : term243 _86951 t' x => @lem3329584 _86951 t' x s h1). Qed.
Lemma lem3329587 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3329588 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) : (term286 _86951 t' x) = (@I (_86951 -> Prop) t' x).
Proof. exact (@lem3329587 (@I (_86951 -> Prop) t' x)). Qed.
Lemma lem3329589 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : @I (_86951 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3329588 _86951 t' x) (@lem3329585 _86951 t' x s h1)). Qed.
Lemma lem3329591 (a : Prop) (b : Prop) : (term287 a b) = (term288 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3329592 {_86951 : Type'} (s : type686 _86951) (_34539 : _86951 -> Prop) (_34540 : _86951) : (term256 _86951 s _34539 _34540) = (term289 _86951 s _34539 _34540).
Proof. exact (@lem3329591 (@I ((_86951 -> Prop) -> Prop) s _34539) (@I (_86951 -> Prop) _34539 _34540)). Qed.
Lemma lem3329594 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3329595 {_86951 : Type'} (s : type686 _86951) (_34539 : _86951 -> Prop) (_34540 : _86951) : (term289 _86951 s _34539 _34540) = (term290 _86951 s _34539 _34540).
Proof. exact (@lem3329594 (term253 _86951 s _34539 _34540)). Qed.
Lemma lem3329596 {_86951 : Type'} (s : type686 _86951) (_34539 : _86951 -> Prop) (_34540 : _86951) : (term256 _86951 s _34539 _34540) = (term290 _86951 s _34539 _34540).
Proof. exact (TRANS (@lem3329592 _86951 s _34539 _34540) (@lem3329595 _86951 s _34539 _34540)). Qed.
Lemma lem3329598 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : term253 _86951 s t' x.
Proof. exact (conj (@lem3329582 _86951 t' x s h1) (@lem3329589 _86951 t' x s h1)). Qed.
Lemma lem3329600 {_86951 : Type'} (_34539 : _86951 -> Prop) (_34540 : _86951) (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : term290 _86951 s _34539 _34540.
Proof. exact (EQ_MP (@lem3329596 _86951 s _34539 _34540) (@lem3329536 _86951 _34539 _34540 t' x s h1)). Qed.
Lemma lem3329601 {_86951 : Type'} (_34539 : _86951 -> Prop) (_34540 : _86951) (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : term290 _86951 s _34539 _34540.
Proof. exact (@lem3329600 _86951 _34539 _34540 t' x s h1). Qed.
Lemma lem3329602 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : term290 _86951 s t' x.
Proof. exact (@lem3329601 _86951 t' x t' x s h1). Qed.
Lemma lem3329605 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : False.
Proof. exact (@lem3329602 _86951 t' x s h1 (@lem3329598 _86951 t' x s h1)). Qed.
Lemma lem3329606 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : term291.
Proof. exact (fun h0 : ~ False => @lem3329605 _86951 t' x s h1). Qed.
Lemma lem3329608 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3329609 : term291 = False.
Proof. exact (@lem3329608 False). Qed.
Lemma lem3329610 {_86951 : Type'} (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term255 _86951 t' x s) : False.
Proof. exact (EQ_MP (@lem3329609) (@lem3329606 _86951 t' x s h1)). Qed.
Lemma lem3329611 {_86951 : Type'} (t : _86951 -> Prop) (t' : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term235 _86951 t t' x s) : False.
Proof. exact (or_elim (@lem3329428 _86951 t t' x s h1) (fun h0 : term262 _86951 s t x => @lem3329575 _86951 s t x h0) (fun h0 : term255 _86951 t' x s => @lem3329610 _86951 t' x s h0)). Qed.
Lemma lem3329612 {_86951 : Type'} (t : _86951 -> Prop) (x : _86951) (s : type686 _86951) (h1 : term238 _86951 t x s) : False.
Proof. exact (ex_elim (@lem3329321 _86951 t x s h1) (fun t' : _86951 -> Prop => fun h0 : term237 _86951 t x s t' => @lem3329611 _86951 t t' x s h0)). Qed.
Lemma lem3329613 {_86951 : Type'} (t : _86951 -> Prop) (s : type686 _86951) (h1 : term240 _86951 t s) : False.
Proof. exact (ex_elim (@lem3329320 _86951 t s h1) (fun x : _86951 => fun h0 : term239 _86951 t s x => @lem3329612 _86951 t x s h0)). Qed.
Lemma lem3329614 {_86951 : Type'} (s : type686 _86951) (h1 : term53 _86951 s) : False.
Proof. exact (ex_elim (@lem3329319 _86951 s h1) (fun t : _86951 -> Prop => fun h0 : term241 _86951 s t => @lem3329613 _86951 t s h0)). Qed.
Lemma lem3329615 {_86951 : Type'} (s : type686 _86951) (h1 : term53 _86951 s) : (term53 _86951 s) = False.
Proof. exact (prop_ext (fun h2 : term53 _86951 s => @lem3329614 _86951 s h1) (fun h2 : False => @lem3328863 _86951 s h1)). Qed.
Lemma lem3329616 {_86951 : Type'} (s : type686 _86951) (h1 : term53 _86951 s) : False.
Proof. exact (EQ_MP (@lem3329615 _86951 s h1) (@lem3328863 _86951 s h1)). Qed.
Lemma lem3329617 {_86951 : Type'} (s : type686 _86951) : term52 _86951 s.
Proof. exact (fun h0 : term53 _86951 s => @lem3329616 _86951 s h0). Qed.
Lemma lem3329618 {_86951 : Type'} (s : type686 _86951) : (term30 _86951 s) = (term41 _86951 s).
Proof. exact (EQ_MP (@lem3328862 _86951 s) (@lem3329617 _86951 s)). Qed.
Lemma lem3329623 {_86951 : Type'} : term43 _86951.
Proof. exact (fun s : type686 _86951 => @lem3329618 _86951 s). Qed.
Lemma lem3329624 {_86951 : Type'} : term45 _86951.
Proof. exact (EQ_MP (@lem3328858 _86951) (@lem3329623 _86951)). Qed.
Lemma lem3329626 {_86951 : Type'} : term45 _86951.
Proof. exact (@lem3328729 _86951 (@lem3329624 _86951)). Qed.
Lemma lem3329627 {_86951 : Type'} (h1 : term46 _86951) : False.
Proof. exact (@lem3329626 _86951 (@lem3328713 _86951 h1)). Qed.
Lemma lem3329628 {_86951 : Type'} (h1 : term46 _86951) : (term46 _86951) = False.
Proof. exact (prop_ext (fun h2 : term46 _86951 => @lem3329627 _86951 h1) (fun h2 : False => @lem3328713 _86951 h1)). Qed.
Lemma lem3329629 {_86951 : Type'} (h1 : term46 _86951) : False.
Proof. exact (EQ_MP (@lem3329628 _86951 h1) (@lem3328713 _86951 h1)). Qed.
Lemma lem3329630 {_86951 : Type'} : term45 _86951.
Proof. exact (fun h0 : term46 _86951 => @lem3329629 _86951 h0). Qed.
Lemma lem3329631 {_86951 : Type'} : term43 _86951.
Proof. exact (EQ_MP (@lem3328712 _86951) (@lem3329630 _86951)). Qed.
Lemma lem3329632 {_86951 : Type'} : term15 _86951.
Proof. exact (EQ_MP (@lem3328708 _86951) (@lem3329631 _86951)). Qed.
Lemma lem3329633 {_86951 : Type'} : term14 _86951.
Proof. exact (EQ_MP (@lem3328581 _86951) (@lem3329632 _86951)). Qed.
