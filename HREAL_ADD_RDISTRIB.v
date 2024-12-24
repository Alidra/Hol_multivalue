Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HREAL_ADD_RDISTRIB_term_abbrevs.
Require Import thm1320617_spec.
Require Import thm1321091_spec.
Lemma lem1321695 (x : hreal) : term0 x.
Proof. exact (@lem1320617 x). Qed.
Lemma lem1321696 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1321697 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1321696 x) (@lem1321695 x)). Qed.
Lemma lem1321698 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1321697 x y). Qed.
Lemma lem1321699 (y : hreal) (x : hreal) : (term2 x y) = ((hreal_mul x y) = (hreal_mul y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1321716 (y : hreal) (x : hreal) : (hreal_mul x y) = (hreal_mul y x).
Proof. exact (EQ_MP (@lem1321699 y x) (@lem1321698 x y)). Qed.
Lemma lem1321717 (p : hreal) (m : hreal) (n : hreal) : (term3 m n p) = (term4 p m n).
Proof. exact (@lem1321716 p (hreal_add m n)). Qed.
Lemma lem1321718 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1321719 (p : hreal) (m : hreal) (n : hreal) : (term5 m n p) = (term6 p m n).
Proof. exact (MK_COMB (@lem1321718) (@lem1321717 p m n)). Qed.
Lemma lem1321721 (y : hreal) (x : hreal) : (hreal_mul x y) = (hreal_mul y x).
Proof. exact (EQ_MP (@lem1321699 y x) (@lem1321698 x y)). Qed.
Lemma lem1321722 (p : hreal) (m : hreal) : (hreal_mul m p) = (hreal_mul p m).
Proof. exact (@lem1321721 p m). Qed.
Lemma lem1321723 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1321724 (p : hreal) (m : hreal) : (term7 m p) = (term7 p m).
Proof. exact (MK_COMB (@lem1321723) (@lem1321722 p m)). Qed.
Lemma lem1321726 (y : hreal) (x : hreal) : (hreal_mul x y) = (hreal_mul y x).
Proof. exact (EQ_MP (@lem1321699 y x) (@lem1321698 x y)). Qed.
Lemma lem1321727 (p : hreal) (n : hreal) : (hreal_mul n p) = (hreal_mul p n).
Proof. exact (@lem1321726 p n). Qed.
Lemma lem1321728 (m : hreal) (p : hreal) (n : hreal) : (term8 m n p) = (term9 m p n).
Proof. exact (MK_COMB (@lem1321724 p m) (@lem1321727 p n)). Qed.
Lemma lem1321729 (m : hreal) (p : hreal) (n : hreal) : ((term3 m n p) = (term8 m n p)) = ((term4 p m n) = (term9 m p n)).
Proof. exact (MK_COMB (@lem1321719 p m n) (@lem1321728 m p n)). Qed.
Lemma lem1321730 (m : hreal) (n : hreal) : (term10 m n) = (term11 m n).
Proof. exact (fun_ext (fun p : hreal => @lem1321729 m p n)). Qed.
Lemma lem1321731 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321732 (m : hreal) (n : hreal) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem1321731) (@lem1321730 m n)). Qed.
Lemma lem1321733 (m : hreal) : (term14 m) = (term15 m).
Proof. exact (fun_ext (fun n : hreal => @lem1321732 m n)). Qed.
Lemma lem1321734 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321735 (m : hreal) : (term16 m) = (term17 m).
Proof. exact (MK_COMB (@lem1321734) (@lem1321733 m)). Qed.
Lemma lem1321736 : term18 = term19.
Proof. exact (fun_ext (fun m : hreal => @lem1321735 m)). Qed.
Lemma lem1321737 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321738 : term20 = term21.
Proof. exact (MK_COMB (@lem1321737) (@lem1321736)). Qed.
Lemma lem1321739 : term21 = term20.
Proof. exact (SYM (@lem1321738)). Qed.
Lemma lem1321740 (x : hreal) : term22 x.
Proof. exact (@lem1321091 x). Qed.
Lemma lem1321741 (x : hreal) : (term22 x) = (term23 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1321742 (x : hreal) : term23 x.
Proof. exact (EQ_MP (@lem1321741 x) (@lem1321740 x)). Qed.
Lemma lem1321743 (x : hreal) (y : hreal) : term24 x y.
Proof. exact (@lem1321742 x y). Qed.
Lemma lem1321744 (y : hreal) (x : hreal) : (term24 x y) = (term25 y x).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1321745 (y : hreal) (x : hreal) : term25 y x.
Proof. exact (EQ_MP (@lem1321744 y x) (@lem1321743 x y)). Qed.
Lemma lem1321746 (y : hreal) (x : hreal) (z : hreal) : term26 y x z.
Proof. exact (@lem1321745 y x z). Qed.
Lemma lem1321747 (y : hreal) (x : hreal) (z : hreal) : (term26 y x z) = ((term4 x y z) = (term9 y x z)).
Proof. exact (eq_refl (term26 y x z)). Qed.
Lemma lem1321750 (y : hreal) (x : hreal) (z : hreal) : (term4 x y z) = (term9 y x z).
Proof. exact (EQ_MP (@lem1321747 y x z) (@lem1321746 y x z)). Qed.
Lemma lem1321751 (m : hreal) (p : hreal) (n : hreal) : (term4 p m n) = (term9 m p n).
Proof. exact (@lem1321750 m p n). Qed.
Lemma lem1321756 (m : hreal) (n : hreal) : term13 m n.
Proof. exact (fun p : hreal => @lem1321751 m p n). Qed.
Lemma lem1321761 (m : hreal) : term17 m.
Proof. exact (fun n : hreal => @lem1321756 m n). Qed.
Lemma lem1321766 : term21.
Proof. exact (fun m : hreal => @lem1321761 m). Qed.
Lemma lem1321767 : term20.
Proof. exact (EQ_MP (@lem1321739) (@lem1321766)). Qed.
