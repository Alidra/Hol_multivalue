Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_SUBSET_term_abbrevs.
Require Import FINITE_DIFF_spec.
Require Import FINITE_INTER_spec.
Require Import INT_POS_spec.
Require Import NSUM_EQ_0_spec.
Require Import NSUM_UNION_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032060_spec.
Require Import thm1032098_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm129_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm137_spec.
Require Import thm1386578_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm2318495_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
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
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7002642 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7002643 {_128878 : Type'} (s : _128878 -> Prop) (t : _128878 -> Prop) : (s = t) = (term0 _128878 s t).
Proof. exact (@lem7002642 _128878 s t). Qed.
Lemma lem7002644 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : ((term1 _128878 v u) = v) = (term2 _128878 u v).
Proof. exact (@lem7002643 _128878 (term1 _128878 v u) v). Qed.
Lemma lem7002653 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : (term2 _128878 u v) = ((term1 _128878 v u) = v).
Proof. exact (SYM (@lem7002644 _128878 u v)). Qed.
Lemma lem7002661 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term3 A x s t) = (term4 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem7002662 {_128878 : Type'} (s : _128878 -> Prop) (x : _128878) (t : _128878 -> Prop) : (term3 _128878 x s t) = (term4 _128878 s x t).
Proof. exact (@lem7002661 _128878 s x t). Qed.
Lemma lem7002663 {_128878 : Type'} (x : _128878) (v : _128878 -> Prop) (u : _128878 -> Prop) : (term5 _128878 x v u) = (term6 _128878 x v u).
Proof. exact (@lem7002662 _128878 (@INTER _128878 u v) x (@DIFF _128878 v u)). Qed.
Lemma lem7002667 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem7002668 {_128878 : Type'} (s : _128878 -> Prop) (x : _128878) (t : _128878 -> Prop) : (term7 _128878 x s t) = (term8 _128878 s x t).
Proof. exact (@lem7002667 _128878 s x t). Qed.
Lemma lem7002669 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (v : _128878 -> Prop) : (term7 _128878 x u v) = (term8 _128878 u x v).
Proof. exact (@lem7002668 _128878 u x v). Qed.
Lemma lem7002673 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7002674 {_128878 : Type'} (P : _128878 -> Prop) (x : _128878) : (@IN _128878 x P) = (P x).
Proof. exact (@lem7002673 _128878 P x). Qed.
Lemma lem7002675 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) : (@IN _128878 x u) = (u x).
Proof. exact (@lem7002674 _128878 u x). Qed.
Lemma lem7002676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7002677 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) : (term9 _128878 x u) = (term10 _128878 u x).
Proof. exact (MK_COMB (@lem7002676) (@lem7002675 _128878 u x)). Qed.
Lemma lem7002679 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7002680 {_128878 : Type'} (P : _128878 -> Prop) (x : _128878) : (@IN _128878 x P) = (P x).
Proof. exact (@lem7002679 _128878 P x). Qed.
Lemma lem7002681 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (@IN _128878 x v) = (v x).
Proof. exact (@lem7002680 _128878 v x). Qed.
Lemma lem7002682 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : (term8 _128878 u x v) = (term11 _128878 u v x).
Proof. exact (MK_COMB (@lem7002677 _128878 u x) (@lem7002681 _128878 v x)). Qed.
Lemma lem7002685 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : (term7 _128878 x u v) = (term11 _128878 u v x).
Proof. exact (TRANS (@lem7002669 _128878 u x v) (@lem7002682 _128878 u v x)). Qed.
Lemma lem7002686 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7002687 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : (term12 _128878 x u v) = (term13 _128878 u v x).
Proof. exact (MK_COMB (@lem7002686) (@lem7002685 _128878 u v x)). Qed.
Lemma lem7002689 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem7002690 {_128878 : Type'} (s : _128878 -> Prop) (x : _128878) (t : _128878 -> Prop) : (term14 _128878 x s t) = (term15 _128878 s x t).
Proof. exact (@lem7002689 _128878 s x t). Qed.
Lemma lem7002691 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) (u : _128878 -> Prop) : (term14 _128878 x v u) = (term15 _128878 v x u).
Proof. exact (@lem7002690 _128878 v x u). Qed.
Lemma lem7002695 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7002696 {_128878 : Type'} (P : _128878 -> Prop) (x : _128878) : (@IN _128878 x P) = (P x).
Proof. exact (@lem7002695 _128878 P x). Qed.
Lemma lem7002697 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (@IN _128878 x v) = (v x).
Proof. exact (@lem7002696 _128878 v x). Qed.
Lemma lem7002698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7002699 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (term9 _128878 x v) = (term10 _128878 v x).
Proof. exact (MK_COMB (@lem7002698) (@lem7002697 _128878 v x)). Qed.
Lemma lem7002701 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7002702 {_128878 : Type'} (P : _128878 -> Prop) (x : _128878) : (@IN _128878 x P) = (P x).
Proof. exact (@lem7002701 _128878 P x). Qed.
Lemma lem7002703 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) : (@IN _128878 x u) = (u x).
Proof. exact (@lem7002702 _128878 u x). Qed.
Lemma lem7002704 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7002705 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) : (term16 _128878 x u) = (term17 _128878 u x).
Proof. exact (MK_COMB (@lem7002704) (@lem7002703 _128878 u x)). Qed.
Lemma lem7002706 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) : (term15 _128878 v x u) = (term18 _128878 v u x).
Proof. exact (MK_COMB (@lem7002699 _128878 v x) (@lem7002705 _128878 u x)). Qed.
Lemma lem7002709 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) : (term14 _128878 x v u) = (term18 _128878 v u x).
Proof. exact (TRANS (@lem7002691 _128878 v x u) (@lem7002706 _128878 v u x)). Qed.
Lemma lem7002710 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) : (term6 _128878 x v u) = (term19 _128878 v u x).
Proof. exact (MK_COMB (@lem7002687 _128878 u v x) (@lem7002709 _128878 v u x)). Qed.
Lemma lem7002713 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) : (term5 _128878 x v u) = (term19 _128878 v u x).
Proof. exact (TRANS (@lem7002663 _128878 x v u) (@lem7002710 _128878 v u x)). Qed.
Lemma lem7002714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7002715 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) : (term20 _128878 x v u) = (term21 _128878 v u x).
Proof. exact (MK_COMB (@lem7002714) (@lem7002713 _128878 v u x)). Qed.
Lemma lem7002717 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7002718 {_128878 : Type'} (P : _128878 -> Prop) (x : _128878) : (@IN _128878 x P) = (P x).
Proof. exact (@lem7002717 _128878 P x). Qed.
Lemma lem7002719 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (@IN _128878 x v) = (v x).
Proof. exact (@lem7002718 _128878 v x). Qed.
Lemma lem7002720 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : ((term5 _128878 x v u) = (@IN _128878 x v)) = ((term19 _128878 v u x) = (v x)).
Proof. exact (MK_COMB (@lem7002715 _128878 v u x) (@lem7002719 _128878 v x)). Qed.
Lemma lem7002723 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : (term22 _128878 u v) = (term23 _128878 u v).
Proof. exact (fun_ext (fun x : _128878 => @lem7002720 _128878 u v x)). Qed.
Lemma lem7002724 {_128878 : Type'} : (@all _128878) = (@all _128878).
Proof. exact (eq_refl (@all _128878)). Qed.
Lemma lem7002725 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : (term2 _128878 u v) = (term24 _128878 u v).
Proof. exact (MK_COMB (@lem7002724 _128878) (@lem7002723 _128878 u v)). Qed.
Lemma lem7002730 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : (term24 _128878 u v) = (term2 _128878 u v).
Proof. exact (SYM (@lem7002725 _128878 u v)). Qed.
Lemma lem7002732 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7002733 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : (term24 _128878 u v) = (term26 _128878 u v).
Proof. exact (@lem7002732 (term24 _128878 u v)). Qed.
Lemma lem7002734 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : (term26 _128878 u v) = (term24 _128878 u v).
Proof. exact (SYM (@lem7002733 _128878 u v)). Qed.
Lemma lem7002735 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (h1 : term27 _128878 u v) : term27 _128878 u v.
Proof. exact (h1). Qed.
Lemma lem7002738 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (h1 : term26 _128878 u v) : term26 _128878 u v.
Proof. exact (h1). Qed.
Lemma lem7002739 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : term28 _128878 u v.
Proof. exact (fun h0 : term26 _128878 u v => @lem7002738 _128878 u v h0). Qed.
Lemma lem7002740 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (h1 : term28 _128878 u v) : term28 _128878 u v.
Proof. exact (h1). Qed.
Lemma lem7002741 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (h1 : term26 _128878 u v) : term26 _128878 u v.
Proof. exact (h1). Qed.
Lemma lem7002742 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (h1 : term26 _128878 u v) (h2 : term28 _128878 u v) : term26 _128878 u v.
Proof. exact (@lem7002740 _128878 u v h2 (@lem7002741 _128878 u v h1)). Qed.
Lemma lem7002743 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (h1 : term26 _128878 u v) : term29 _128878 u v.
Proof. exact (fun h0 : term28 _128878 u v => @lem7002742 _128878 u v h1 h0). Qed.
Lemma lem7002744 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (h1 : term28 _128878 u v) : term28 _128878 u v.
Proof. exact (h1). Qed.
Lemma lem7002745 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (h1 : term26 _128878 u v) (h2 : term28 _128878 u v) : term26 _128878 u v.
Proof. exact (@lem7002743 _128878 u v h1 (@lem7002744 _128878 u v h2)). Qed.
Lemma lem7002746 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (h1 : term28 _128878 u v) : term28 _128878 u v.
Proof. exact (fun h0 : term26 _128878 u v => @lem7002745 _128878 u v h0 h1). Qed.
Lemma lem7002747 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : term30 _128878 u v.
Proof. exact (fun h0 : term28 _128878 u v => @lem7002746 _128878 u v h0). Qed.
Lemma lem7002750 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : term28 _128878 u v.
Proof. exact (@lem7002747 _128878 u v (@lem7002739 _128878 u v)). Qed.
Lemma lem7002751 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : term28 _128878 u v.
Proof. exact (@lem7002750 _128878 u v). Qed.
Lemma lem7002761 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7002762 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : (term26 _128878 u v) = (term31 _128878 u v).
Proof. exact (@lem7002761 (term27 _128878 u v)). Qed.
Lemma lem7002764 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7002765 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : (term31 _128878 u v) = (term24 _128878 u v).
Proof. exact (@lem7002764 (term24 _128878 u v)). Qed.
Lemma lem7002770 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : (term26 _128878 u v) = (term24 _128878 u v).
Proof. exact (TRANS (@lem7002762 _128878 u v) (@lem7002765 _128878 u v)). Qed.
Lemma lem7002777 {_128878 : Type'} (v : _128878 -> Prop) : (term33 _128878 v) = (term34 _128878 v).
Proof. exact (fun_ext (fun u : _128878 -> Prop => @lem7002770 _128878 u v)). Qed.
Lemma lem7002778 {_128878 : Type'} : (@all (_128878 -> Prop)) = (@all (_128878 -> Prop)).
Proof. exact (eq_refl (@all (_128878 -> Prop))). Qed.
Lemma lem7002779 {_128878 : Type'} (v : _128878 -> Prop) : (term35 _128878 v) = (term36 _128878 v).
Proof. exact (MK_COMB (@lem7002778 _128878) (@lem7002777 _128878 v)). Qed.
Lemma lem7002784 {_128878 : Type'} : (term37 _128878) = (term38 _128878).
Proof. exact (fun_ext (fun v : _128878 -> Prop => @lem7002779 _128878 v)). Qed.
Lemma lem7002785 {_128878 : Type'} : (@all (_128878 -> Prop)) = (@all (_128878 -> Prop)).
Proof. exact (eq_refl (@all (_128878 -> Prop))). Qed.
Lemma lem7002794 {_128878 : Type'} : (term39 _128878) = (term40 _128878).
Proof. exact (MK_COMB (@lem7002785 _128878) (@lem7002784 _128878)). Qed.
Lemma lem7002813 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : ((term19 _128878 v u x) = (v x)) = ((term19 _128878 v u x) = (v x)).
Proof. exact (eq_refl ((term19 _128878 v u x) = (v x))). Qed.
Lemma lem7002814 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : (term23 _128878 u v) = (term23 _128878 u v).
Proof. exact (fun_ext (fun x : _128878 => @lem7002813 _128878 u v x)). Qed.
Lemma lem7002815 {_128878 : Type'} : (@all _128878) = (@all _128878).
Proof. exact (eq_refl (@all _128878)). Qed.
Lemma lem7002816 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : (term24 _128878 u v) = (term24 _128878 u v).
Proof. exact (MK_COMB (@lem7002815 _128878) (@lem7002814 _128878 u v)). Qed.
Lemma lem7002817 {_128878 : Type'} (v : _128878 -> Prop) : (term34 _128878 v) = (term34 _128878 v).
Proof. exact (fun_ext (fun u : _128878 -> Prop => @lem7002816 _128878 u v)). Qed.
Lemma lem7002818 {_128878 : Type'} : (@all (_128878 -> Prop)) = (@all (_128878 -> Prop)).
Proof. exact (eq_refl (@all (_128878 -> Prop))). Qed.
Lemma lem7002819 {_128878 : Type'} (v : _128878 -> Prop) : (term36 _128878 v) = (term36 _128878 v).
Proof. exact (MK_COMB (@lem7002818 _128878) (@lem7002817 _128878 v)). Qed.
Lemma lem7002820 {_128878 : Type'} : (term38 _128878) = (term38 _128878).
Proof. exact (fun_ext (fun v : _128878 -> Prop => @lem7002819 _128878 v)). Qed.
Lemma lem7002821 {_128878 : Type'} : (@all (_128878 -> Prop)) = (@all (_128878 -> Prop)).
Proof. exact (eq_refl (@all (_128878 -> Prop))). Qed.
Lemma lem7002822 {_128878 : Type'} : (term40 _128878) = (term40 _128878).
Proof. exact (MK_COMB (@lem7002821 _128878) (@lem7002820 _128878)). Qed.
Lemma lem7002849 {_128878 : Type'} : (term39 _128878) = (term40 _128878).
Proof. exact (TRANS (@lem7002794 _128878) (@lem7002822 _128878)). Qed.
Lemma lem7002850 {_128878 : Type'} : (term40 _128878) = (term39 _128878).
Proof. exact (SYM (@lem7002849 _128878)). Qed.
Lemma lem7002852 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7002853 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : ((term19 _128878 v u x) = (v x)) = (term41 _128878 u v x).
Proof. exact (@lem7002852 ((term19 _128878 v u x) = (v x))). Qed.
Lemma lem7002854 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : (term41 _128878 u v x) = ((term19 _128878 v u x) = (v x)).
Proof. exact (SYM (@lem7002853 _128878 u v x)). Qed.
Lemma lem7002855 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term42 _128878 u v x) : term42 _128878 u v x.
Proof. exact (h1). Qed.
Lemma lem7002864 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : (term43 _128878 u v x) = (term44 _128878 u v x).
Proof. exact (@lem17045 (u x) (v x)). Qed.
Lemma lem7002873 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) : (term45 _128878 u x) = (u x).
Proof. exact (@lem16933 (u x)). Qed.
Lemma lem7002875 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (term46 _128878 v x) = (term46 _128878 v x).
Proof. exact (eq_refl (term46 _128878 v x)). Qed.
Lemma lem7002876 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) : (term47 _128878 v u x) = (term48 _128878 v u x).
Proof. exact (MK_COMB (@lem7002875 _128878 v x) (@lem7002873 _128878 u x)). Qed.
Lemma lem7002877 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) : (term49 _128878 v u x) = (term47 _128878 v u x).
Proof. exact (@lem17045 (v x) (term17 _128878 u x)). Qed.
Lemma lem7002878 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) : (term49 _128878 v u x) = (term48 _128878 v u x).
Proof. exact (TRANS (@lem7002877 _128878 v u x) (@lem7002876 _128878 v u x)). Qed.
Lemma lem7002882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7002883 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : (term50 _128878 u v x) = (term51 _128878 u v x).
Proof. exact (MK_COMB (@lem7002882) (@lem7002864 _128878 u v x)). Qed.
Lemma lem7002884 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) : (term52 _128878 v u x) = (term53 _128878 v u x).
Proof. exact (MK_COMB (@lem7002883 _128878 u v x) (@lem7002878 _128878 v u x)). Qed.
Lemma lem7002885 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) : (term54 _128878 v u x) = (term52 _128878 v u x).
Proof. exact (@lem17160 (term11 _128878 u v x) (term18 _128878 v u x)). Qed.
Lemma lem7002886 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) : (term54 _128878 v u x) = (term53 _128878 v u x).
Proof. exact (TRANS (@lem7002885 _128878 v u x) (@lem7002884 _128878 v u x)). Qed.
Lemma lem7002891 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (v x) = (v x).
Proof. exact (eq_refl (v x)). Qed.
Lemma lem7002892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7002893 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) : (term55 _128878 v u x) = (term56 _128878 v u x).
Proof. exact (MK_COMB (@lem7002892) (@lem7002886 _128878 v u x)). Qed.
Lemma lem7002894 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : (term57 _128878 u v x) = (term58 _128878 u v x).
Proof. exact (MK_COMB (@lem7002893 _128878 v u x) (@lem7002891 _128878 v x)). Qed.
Lemma lem7002899 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : (term59 _128878 u v x) = (term59 _128878 u v x).
Proof. exact (eq_refl (term59 _128878 u v x)). Qed.
Lemma lem7002900 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : (term60 _128878 u v x) = (term61 _128878 u v x).
Proof. exact (MK_COMB (@lem7002899 _128878 u v x) (@lem7002894 _128878 u v x)). Qed.
Lemma lem7002901 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : (term42 _128878 u v x) = (term60 _128878 u v x).
Proof. exact (@lem17646 (term19 _128878 v u x) (v x)). Qed.
Lemma lem7002906 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : (term42 _128878 u v x) = (term61 _128878 u v x).
Proof. exact (TRANS (@lem7002901 _128878 u v x) (@lem7002900 _128878 u v x)). Qed.
Lemma lem7002975 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term42 _128878 u v x) : term61 _128878 u v x.
Proof. exact (EQ_MP (@lem7002906 _128878 u v x) (@lem7002855 _128878 u v x h1)). Qed.
Lemma lem7002976 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term62 _128878 u v x) : term62 _128878 u v x.
Proof. exact (h1). Qed.
Lemma lem7002977 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term58 _128878 u v x) : term58 _128878 u v x.
Proof. exact (h1). Qed.
Lemma lem7002979 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term62 _128878 u v x) : term19 _128878 v u x.
Proof. exact (proj1 (@lem7002976 _128878 u v x h1)). Qed.
Lemma lem7002980 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term11 _128878 u v x) : term11 _128878 u v x.
Proof. exact (h1). Qed.
Lemma lem7002981 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) (h1 : term18 _128878 v u x) : term18 _128878 v u x.
Proof. exact (h1). Qed.
Lemma lem7002987 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term58 _128878 u v x) : term53 _128878 v u x.
Proof. exact (proj1 (@lem7002977 _128878 u v x h1)). Qed.
Lemma lem7002988 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term58 _128878 u v x) : term48 _128878 v u x.
Proof. exact (proj2 (@lem7002987 _128878 u v x h1)). Qed.
Lemma lem7002989 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term58 _128878 u v x) : term44 _128878 u v x.
Proof. exact (proj1 (@lem7002987 _128878 u v x h1)). Qed.
Lemma lem7003027 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) : term17 _128878 v x.
Proof. exact (h1). Qed.
Lemma lem7003039 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) : term17 _128878 v x.
Proof. exact (h1). Qed.
Lemma lem7003043 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) : term17 _128878 v x.
Proof. exact (h1). Qed.
Lemma lem7003051 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7003055 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) : term17 _128878 u x.
Proof. exact (h1). Qed.
Lemma lem7003067 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) : term17 _128878 v x.
Proof. exact (h1). Qed.
Lemma lem7003069 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term62 _128878 u v x) : term17 _128878 v x.
Proof. exact (proj2 (@lem7002976 _128878 u v x h1)). Qed.
Lemma lem7003075 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term62 _128878 u v x) : term17 _128878 v x.
Proof. exact (proj2 (@lem7002976 _128878 u v x h1)). Qed.
Lemma lem7003083 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) : term17 _128878 v x.
Proof. exact (h1). Qed.
Lemma lem7003089 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) : term17 _128878 v x.
Proof. exact (h1). Qed.
Lemma lem7003091 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) : term17 _128878 v x.
Proof. exact (h1). Qed.
Lemma lem7003095 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7003097 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) : term17 _128878 u x.
Proof. exact (h1). Qed.
Lemma lem7003103 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) : term17 _128878 v x.
Proof. exact (h1). Qed.
Lemma lem7003105 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term11 _128878 u v x) : v x.
Proof. exact (proj2 (@lem7002980 _128878 u v x h1)). Qed.
Lemma lem7003106 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term11 _128878 u v x) : term63 _128878 v x.
Proof. exact (fun h0 : term17 _128878 v x => @lem7003105 _128878 u v x h1). Qed.
Lemma lem7003108 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003109 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (term63 _128878 v x) = (v x).
Proof. exact (@lem7003108 (v x)). Qed.
Lemma lem7003110 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term11 _128878 u v x) : v x.
Proof. exact (EQ_MP (@lem7003109 _128878 v x) (@lem7003106 _128878 u v x h1)). Qed.
Lemma lem7003113 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7003115 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (term17 _128878 v x) = (term65 _128878 v x).
Proof. exact (@lem7003113 (v x)). Qed.
Lemma lem7003118 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term62 _128878 u v x) : term65 _128878 v x.
Proof. exact (EQ_MP (@lem7003115 _128878 v x) (@lem7003069 _128878 u v x h1)). Qed.
Lemma lem7003121 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term11 _128878 u v x) (h2 : term62 _128878 u v x) : False.
Proof. exact (@lem7003118 _128878 u v x h2 (@lem7003110 _128878 u v x h1)). Qed.
Lemma lem7003122 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term11 _128878 u v x) (h2 : term62 _128878 u v x) : term66.
Proof. exact (fun h0 : ~ False => @lem7003121 _128878 u v x h1 h2). Qed.
Lemma lem7003124 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003125 : term66 = False.
Proof. exact (@lem7003124 False). Qed.
Lemma lem7003126 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term11 _128878 u v x) (h2 : term62 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003125) (@lem7003122 _128878 u v x h1 h2)). Qed.
Lemma lem7003128 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) (h1 : term18 _128878 v u x) : v x.
Proof. exact (proj1 (@lem7002981 _128878 v u x h1)). Qed.
Lemma lem7003129 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) (h1 : term18 _128878 v u x) : term63 _128878 v x.
Proof. exact (fun h0 : term17 _128878 v x => @lem7003128 _128878 v u x h1). Qed.
Lemma lem7003131 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003132 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (term63 _128878 v x) = (v x).
Proof. exact (@lem7003131 (v x)). Qed.
Lemma lem7003133 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) (x : _128878) (h1 : term18 _128878 v u x) : v x.
Proof. exact (EQ_MP (@lem7003132 _128878 v x) (@lem7003129 _128878 v u x h1)). Qed.
Lemma lem7003136 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7003138 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (term17 _128878 v x) = (term65 _128878 v x).
Proof. exact (@lem7003136 (v x)). Qed.
Lemma lem7003141 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term62 _128878 u v x) : term65 _128878 v x.
Proof. exact (EQ_MP (@lem7003138 _128878 v x) (@lem7003075 _128878 u v x h1)). Qed.
Lemma lem7003144 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term18 _128878 v u x) (h2 : term62 _128878 u v x) : False.
Proof. exact (@lem7003141 _128878 u v x h2 (@lem7003133 _128878 v u x h1)). Qed.
Lemma lem7003145 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term18 _128878 v u x) (h2 : term62 _128878 u v x) : term66.
Proof. exact (fun h0 : ~ False => @lem7003144 _128878 u v x h1 h2). Qed.
Lemma lem7003147 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003148 : term66 = False.
Proof. exact (@lem7003147 False). Qed.
Lemma lem7003149 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term18 _128878 v u x) (h2 : term62 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003148) (@lem7003145 _128878 u v x h1 h2)). Qed.
Lemma lem7003151 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term58 _128878 u v x) : v x.
Proof. exact (proj2 (@lem7002977 _128878 u v x h1)). Qed.
Lemma lem7003152 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term58 _128878 u v x) : term63 _128878 v x.
Proof. exact (fun h0 : term17 _128878 v x => @lem7003151 _128878 u v x h1). Qed.
Lemma lem7003154 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003155 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (term63 _128878 v x) = (v x).
Proof. exact (@lem7003154 (v x)). Qed.
Lemma lem7003156 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term58 _128878 u v x) : v x.
Proof. exact (EQ_MP (@lem7003155 _128878 v x) (@lem7003152 _128878 u v x h1)). Qed.
Lemma lem7003159 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7003161 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (term17 _128878 v x) = (term65 _128878 v x).
Proof. exact (@lem7003159 (v x)). Qed.
Lemma lem7003164 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) : term65 _128878 v x.
Proof. exact (EQ_MP (@lem7003161 _128878 v x) (@lem7003083 _128878 v x h1)). Qed.
Lemma lem7003167 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (@lem7003164 _128878 v x h1 (@lem7003156 _128878 u v x h2)). Qed.
Lemma lem7003168 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : term66.
Proof. exact (fun h0 : ~ False => @lem7003167 _128878 u v x h1 h2). Qed.
Lemma lem7003170 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003171 : term66 = False.
Proof. exact (@lem7003170 False). Qed.
Lemma lem7003172 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003171) (@lem7003168 _128878 u v x h1 h2)). Qed.
Lemma lem7003174 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term58 _128878 u v x) : v x.
Proof. exact (proj2 (@lem7002977 _128878 u v x h1)). Qed.
Lemma lem7003175 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term58 _128878 u v x) : term63 _128878 v x.
Proof. exact (fun h0 : term17 _128878 v x => @lem7003174 _128878 u v x h1). Qed.
Lemma lem7003177 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003178 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (term63 _128878 v x) = (v x).
Proof. exact (@lem7003177 (v x)). Qed.
Lemma lem7003179 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term58 _128878 u v x) : v x.
Proof. exact (EQ_MP (@lem7003178 _128878 v x) (@lem7003175 _128878 u v x h1)). Qed.
Lemma lem7003182 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7003184 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (term17 _128878 v x) = (term65 _128878 v x).
Proof. exact (@lem7003182 (v x)). Qed.
Lemma lem7003187 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) : term65 _128878 v x.
Proof. exact (EQ_MP (@lem7003184 _128878 v x) (@lem7003089 _128878 v x h1)). Qed.
Lemma lem7003190 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (@lem7003187 _128878 v x h1 (@lem7003179 _128878 u v x h2)). Qed.
Lemma lem7003191 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : term66.
Proof. exact (fun h0 : ~ False => @lem7003190 _128878 u v x h1 h2). Qed.
Lemma lem7003193 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003194 : term66 = False.
Proof. exact (@lem7003193 False). Qed.
Lemma lem7003195 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003194) (@lem7003191 _128878 u v x h1 h2)). Qed.
Lemma lem7003197 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7003198 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : u x) : term63 _128878 u x.
Proof. exact (fun h0 : term17 _128878 u x => @lem7003197 _128878 u x h1). Qed.
Lemma lem7003200 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003201 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) : (term63 _128878 u x) = (u x).
Proof. exact (@lem7003200 (u x)). Qed.
Lemma lem7003202 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : u x) : u x.
Proof. exact (EQ_MP (@lem7003201 _128878 u x) (@lem7003198 _128878 u x h1)). Qed.
Lemma lem7003205 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7003207 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) : (term17 _128878 u x) = (term65 _128878 u x).
Proof. exact (@lem7003205 (u x)). Qed.
Lemma lem7003210 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) : term65 _128878 u x.
Proof. exact (EQ_MP (@lem7003207 _128878 u x) (@lem7003097 _128878 u x h1)). Qed.
Lemma lem7003213 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) (h2 : u x) : False.
Proof. exact (@lem7003210 _128878 u x h1 (@lem7003202 _128878 u x h2)). Qed.
Lemma lem7003214 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) (h2 : u x) : term66.
Proof. exact (fun h0 : ~ False => @lem7003213 _128878 u x h1 h2). Qed.
Lemma lem7003216 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003217 : term66 = False.
Proof. exact (@lem7003216 False). Qed.
Lemma lem7003218 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem7003217) (@lem7003214 _128878 u x h1 h2)). Qed.
Lemma lem7003220 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term58 _128878 u v x) : v x.
Proof. exact (proj2 (@lem7002977 _128878 u v x h1)). Qed.
Lemma lem7003221 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term58 _128878 u v x) : term63 _128878 v x.
Proof. exact (fun h0 : term17 _128878 v x => @lem7003220 _128878 u v x h1). Qed.
Lemma lem7003223 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003224 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (term63 _128878 v x) = (v x).
Proof. exact (@lem7003223 (v x)). Qed.
Lemma lem7003225 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term58 _128878 u v x) : v x.
Proof. exact (EQ_MP (@lem7003224 _128878 v x) (@lem7003221 _128878 u v x h1)). Qed.
Lemma lem7003228 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7003230 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) : (term17 _128878 v x) = (term65 _128878 v x).
Proof. exact (@lem7003228 (v x)). Qed.
Lemma lem7003233 {_128878 : Type'} (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) : term65 _128878 v x.
Proof. exact (EQ_MP (@lem7003230 _128878 v x) (@lem7003103 _128878 v x h1)). Qed.
Lemma lem7003236 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (@lem7003233 _128878 v x h1 (@lem7003225 _128878 u v x h2)). Qed.
Lemma lem7003237 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : term66.
Proof. exact (fun h0 : ~ False => @lem7003236 _128878 u v x h1 h2). Qed.
Lemma lem7003239 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003240 : term66 = False.
Proof. exact (@lem7003239 False). Qed.
Lemma lem7003241 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003240) (@lem7003237 _128878 u v x h1 h2)). Qed.
Lemma lem7003242 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : (term17 _128878 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128878 v x => @lem7003241 _128878 u v x h1 h2) (fun h3 : False => @lem7003103 _128878 v x h1)). Qed.
Lemma lem7003243 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003242 _128878 u v x h1 h2) (@lem7003103 _128878 v x h1)). Qed.
Lemma lem7003244 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) (h2 : u x) : (term17 _128878 u x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128878 u x => @lem7003218 _128878 u x h1 h2) (fun h3 : False => @lem7003097 _128878 u x h1)). Qed.
Lemma lem7003245 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem7003244 _128878 u x h1 h2) (@lem7003097 _128878 u x h1)). Qed.
Lemma lem7003246 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) (h2 : u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7003245 _128878 u x h1 h2) (fun h3 : False => @lem7003095 _128878 u x h2)). Qed.
Lemma lem7003247 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem7003246 _128878 u x h1 h2) (@lem7003095 _128878 u x h2)). Qed.
Lemma lem7003248 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : (term17 _128878 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128878 v x => @lem7003195 _128878 u v x h1 h2) (fun h3 : False => @lem7003091 _128878 v x h1)). Qed.
Lemma lem7003249 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003248 _128878 u v x h1 h2) (@lem7003091 _128878 v x h1)). Qed.
Lemma lem7003250 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : (term17 _128878 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128878 v x => @lem7003249 _128878 u v x h1 h2) (fun h3 : False => @lem7003089 _128878 v x h1)). Qed.
Lemma lem7003251 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003250 _128878 u v x h1 h2) (@lem7003089 _128878 v x h1)). Qed.
Lemma lem7003252 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : (term17 _128878 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128878 v x => @lem7003172 _128878 u v x h1 h2) (fun h3 : False => @lem7003083 _128878 v x h1)). Qed.
Lemma lem7003253 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003252 _128878 u v x h1 h2) (@lem7003083 _128878 v x h1)). Qed.
Lemma lem7003254 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : (term17 _128878 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128878 v x => @lem7003243 _128878 u v x h1 h2) (fun h3 : False => @lem7003067 _128878 v x h1)). Qed.
Lemma lem7003255 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003254 _128878 u v x h1 h2) (@lem7003067 _128878 v x h1)). Qed.
Lemma lem7003256 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) (h2 : u x) : (term17 _128878 u x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128878 u x => @lem7003247 _128878 u x h1 h2) (fun h3 : False => @lem7003055 _128878 u x h1)). Qed.
Lemma lem7003257 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem7003256 _128878 u x h1 h2) (@lem7003055 _128878 u x h1)). Qed.
Lemma lem7003258 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) (h2 : u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7003257 _128878 u x h1 h2) (fun h3 : False => @lem7003051 _128878 u x h2)). Qed.
Lemma lem7003259 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem7003258 _128878 u x h1 h2) (@lem7003051 _128878 u x h2)). Qed.
Lemma lem7003260 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : (term17 _128878 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128878 v x => @lem7003251 _128878 u v x h1 h2) (fun h3 : False => @lem7003043 _128878 v x h1)). Qed.
Lemma lem7003261 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003260 _128878 u v x h1 h2) (@lem7003043 _128878 v x h1)). Qed.
Lemma lem7003262 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : (term17 _128878 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128878 v x => @lem7003261 _128878 u v x h1 h2) (fun h3 : False => @lem7003039 _128878 v x h1)). Qed.
Lemma lem7003263 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003262 _128878 u v x h1 h2) (@lem7003039 _128878 v x h1)). Qed.
Lemma lem7003264 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : (term17 _128878 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128878 v x => @lem7003253 _128878 u v x h1 h2) (fun h3 : False => @lem7003027 _128878 v x h1)). Qed.
Lemma lem7003265 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003264 _128878 u v x h1 h2) (@lem7003027 _128878 v x h1)). Qed.
Lemma lem7003266 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : (term17 _128878 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128878 v x => @lem7003255 _128878 u v x h1 h2) (fun h3 : False => @lem7003067 _128878 v x h1)). Qed.
Lemma lem7003267 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003266 _128878 u v x h1 h2) (@lem7003067 _128878 v x h1)). Qed.
Lemma lem7003268 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) (h2 : u x) : (term17 _128878 u x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128878 u x => @lem7003259 _128878 u x h1 h2) (fun h3 : False => @lem7003055 _128878 u x h1)). Qed.
Lemma lem7003269 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem7003268 _128878 u x h1 h2) (@lem7003055 _128878 u x h1)). Qed.
Lemma lem7003270 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) (h2 : u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7003269 _128878 u x h1 h2) (fun h3 : False => @lem7003051 _128878 u x h2)). Qed.
Lemma lem7003271 {_128878 : Type'} (u : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem7003270 _128878 u x h1 h2) (@lem7003051 _128878 u x h2)). Qed.
Lemma lem7003272 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : (term17 _128878 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128878 v x => @lem7003263 _128878 u v x h1 h2) (fun h3 : False => @lem7003043 _128878 v x h1)). Qed.
Lemma lem7003273 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003272 _128878 u v x h1 h2) (@lem7003043 _128878 v x h1)). Qed.
Lemma lem7003274 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : (term17 _128878 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128878 v x => @lem7003273 _128878 u v x h1 h2) (fun h3 : False => @lem7003039 _128878 v x h1)). Qed.
Lemma lem7003275 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003274 _128878 u v x h1 h2) (@lem7003039 _128878 v x h1)). Qed.
Lemma lem7003276 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : (term17 _128878 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128878 v x => @lem7003265 _128878 u v x h1 h2) (fun h3 : False => @lem7003027 _128878 v x h1)). Qed.
Lemma lem7003277 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003276 _128878 u v x h1 h2) (@lem7003027 _128878 v x h1)). Qed.
Lemma lem7003278 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : u x) (h2 : term58 _128878 u v x) : False.
Proof. exact (or_elim (@lem7002989 _128878 u v x h2) (fun h0 : term17 _128878 u x => @lem7003271 _128878 u x h0 h1) (fun h0 : term17 _128878 v x => @lem7003267 _128878 u v x h0 h2)). Qed.
Lemma lem7003279 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term17 _128878 v x) (h2 : term58 _128878 u v x) : False.
Proof. exact (or_elim (@lem7002989 _128878 u v x h2) (fun h0 : term17 _128878 u x => @lem7003277 _128878 u v x h1 h2) (fun h0 : term17 _128878 v x => @lem7003275 _128878 u v x h1 h2)). Qed.
Lemma lem7003280 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term58 _128878 u v x) : False.
Proof. exact (or_elim (@lem7002988 _128878 u v x h1) (fun h0 : term17 _128878 v x => @lem7003279 _128878 u v x h0 h1) (fun h0 : u x => @lem7003278 _128878 u v x h0 h1)). Qed.
Lemma lem7003281 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term62 _128878 u v x) : False.
Proof. exact (or_elim (@lem7002979 _128878 u v x h1) (fun h0 : term11 _128878 u v x => @lem7003126 _128878 u v x h0 h1) (fun h0 : term18 _128878 v u x => @lem7003149 _128878 u v x h0 h1)). Qed.
Lemma lem7003282 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term42 _128878 u v x) : False.
Proof. exact (or_elim (@lem7002975 _128878 u v x h1) (fun h0 : term62 _128878 u v x => @lem7003281 _128878 u v x h0) (fun h0 : term58 _128878 u v x => @lem7003280 _128878 u v x h0)). Qed.
Lemma lem7003283 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term42 _128878 u v x) : (term42 _128878 u v x) = False.
Proof. exact (prop_ext (fun h2 : term42 _128878 u v x => @lem7003282 _128878 u v x h1) (fun h2 : False => @lem7002855 _128878 u v x h1)). Qed.
Lemma lem7003284 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) (h1 : term42 _128878 u v x) : False.
Proof. exact (EQ_MP (@lem7003283 _128878 u v x h1) (@lem7002855 _128878 u v x h1)). Qed.
Lemma lem7003285 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : term41 _128878 u v x.
Proof. exact (fun h0 : term42 _128878 u v x => @lem7003284 _128878 u v x h0). Qed.
Lemma lem7003286 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (x : _128878) : (term19 _128878 v u x) = (v x).
Proof. exact (EQ_MP (@lem7002854 _128878 u v x) (@lem7003285 _128878 u v x)). Qed.
Lemma lem7003291 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : term24 _128878 u v.
Proof. exact (fun x : _128878 => @lem7003286 _128878 u v x). Qed.
Lemma lem7003296 {_128878 : Type'} (v : _128878 -> Prop) : term36 _128878 v.
Proof. exact (fun u : _128878 -> Prop => @lem7003291 _128878 u v). Qed.
Lemma lem7003301 {_128878 : Type'} : term40 _128878.
Proof. exact (fun v : _128878 -> Prop => @lem7003296 _128878 v). Qed.
Lemma lem7003302 {_128878 : Type'} : term39 _128878.
Proof. exact (EQ_MP (@lem7002850 _128878) (@lem7003301 _128878)). Qed.
Lemma lem7003303 {_128878 : Type'} (v : _128878 -> Prop) : term67 _128878 v.
Proof. exact (@lem7003302 _128878 v). Qed.
Lemma lem7003304 {_128878 : Type'} (v : _128878 -> Prop) : (term67 _128878 v) = (term35 _128878 v).
Proof. exact (eq_refl (term67 _128878 v)). Qed.
Lemma lem7003305 {_128878 : Type'} (v : _128878 -> Prop) : term35 _128878 v.
Proof. exact (EQ_MP (@lem7003304 _128878 v) (@lem7003303 _128878 v)). Qed.
Lemma lem7003306 {_128878 : Type'} (v : _128878 -> Prop) (u : _128878 -> Prop) : term68 _128878 v u.
Proof. exact (@lem7003305 _128878 v u). Qed.
Lemma lem7003307 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : (term68 _128878 v u) = (term26 _128878 u v).
Proof. exact (eq_refl (term68 _128878 v u)). Qed.
Lemma lem7003308 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : term26 _128878 u v.
Proof. exact (EQ_MP (@lem7003307 _128878 u v) (@lem7003306 _128878 v u)). Qed.
Lemma lem7003310 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : term26 _128878 u v.
Proof. exact (@lem7002751 _128878 u v (@lem7003308 _128878 u v)). Qed.
Lemma lem7003311 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (h1 : term27 _128878 u v) : False.
Proof. exact (@lem7003310 _128878 u v (@lem7002735 _128878 u v h1)). Qed.
Lemma lem7003312 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (h1 : term27 _128878 u v) : (term27 _128878 u v) = False.
Proof. exact (prop_ext (fun h2 : term27 _128878 u v => @lem7003311 _128878 u v h1) (fun h2 : False => @lem7002735 _128878 u v h1)). Qed.
Lemma lem7003313 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) (h1 : term27 _128878 u v) : False.
Proof. exact (EQ_MP (@lem7003312 _128878 u v h1) (@lem7002735 _128878 u v h1)). Qed.
Lemma lem7003314 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : term26 _128878 u v.
Proof. exact (fun h0 : term27 _128878 u v => @lem7003313 _128878 u v h0). Qed.
Lemma lem7003315 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : term24 _128878 u v.
Proof. exact (EQ_MP (@lem7002734 _128878 u v) (@lem7003314 _128878 u v)). Qed.
Lemma lem7003316 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : term2 _128878 u v.
Proof. exact (EQ_MP (@lem7002730 _128878 u v) (@lem7003315 _128878 u v)). Qed.
Lemma lem7003331 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7003332 {_128891 : Type'} (s : _128891 -> Prop) (t : _128891 -> Prop) : (s = t) = (term0 _128891 s t).
Proof. exact (@lem7003331 _128891 s t). Qed.
Lemma lem7003333 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : ((term69 _128891 u v) = u) = (term70 _128891 v u).
Proof. exact (@lem7003332 _128891 (term69 _128891 u v) u). Qed.
Lemma lem7003342 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : (term70 _128891 v u) = ((term69 _128891 u v) = u).
Proof. exact (SYM (@lem7003333 _128891 v u)). Qed.
Lemma lem7003350 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term3 A x s t) = (term4 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem7003351 {_128891 : Type'} (s : _128891 -> Prop) (x : _128891) (t : _128891 -> Prop) : (term3 _128891 x s t) = (term4 _128891 s x t).
Proof. exact (@lem7003350 _128891 s x t). Qed.
Lemma lem7003352 {_128891 : Type'} (x : _128891) (u : _128891 -> Prop) (v : _128891 -> Prop) : (term71 _128891 x u v) = (term72 _128891 x u v).
Proof. exact (@lem7003351 _128891 (@INTER _128891 u v) x (@DIFF _128891 u v)). Qed.
Lemma lem7003356 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem7003357 {_128891 : Type'} (s : _128891 -> Prop) (x : _128891) (t : _128891 -> Prop) : (term7 _128891 x s t) = (term8 _128891 s x t).
Proof. exact (@lem7003356 _128891 s x t). Qed.
Lemma lem7003358 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) (v : _128891 -> Prop) : (term7 _128891 x u v) = (term8 _128891 u x v).
Proof. exact (@lem7003357 _128891 u x v). Qed.
Lemma lem7003362 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7003363 {_128891 : Type'} (P : _128891 -> Prop) (x : _128891) : (@IN _128891 x P) = (P x).
Proof. exact (@lem7003362 _128891 P x). Qed.
Lemma lem7003364 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (@IN _128891 x u) = (u x).
Proof. exact (@lem7003363 _128891 u x). Qed.
Lemma lem7003365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7003366 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (term9 _128891 x u) = (term10 _128891 u x).
Proof. exact (MK_COMB (@lem7003365) (@lem7003364 _128891 u x)). Qed.
Lemma lem7003368 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7003369 {_128891 : Type'} (P : _128891 -> Prop) (x : _128891) : (@IN _128891 x P) = (P x).
Proof. exact (@lem7003368 _128891 P x). Qed.
Lemma lem7003370 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) : (@IN _128891 x v) = (v x).
Proof. exact (@lem7003369 _128891 v x). Qed.
Lemma lem7003371 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term8 _128891 u x v) = (term11 _128891 u v x).
Proof. exact (MK_COMB (@lem7003366 _128891 u x) (@lem7003370 _128891 v x)). Qed.
Lemma lem7003374 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term7 _128891 x u v) = (term11 _128891 u v x).
Proof. exact (TRANS (@lem7003358 _128891 u x v) (@lem7003371 _128891 u v x)). Qed.
Lemma lem7003375 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7003376 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term12 _128891 x u v) = (term13 _128891 u v x).
Proof. exact (MK_COMB (@lem7003375) (@lem7003374 _128891 u v x)). Qed.
Lemma lem7003378 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem7003379 {_128891 : Type'} (s : _128891 -> Prop) (x : _128891) (t : _128891 -> Prop) : (term14 _128891 x s t) = (term15 _128891 s x t).
Proof. exact (@lem7003378 _128891 s x t). Qed.
Lemma lem7003380 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) (v : _128891 -> Prop) : (term14 _128891 x u v) = (term15 _128891 u x v).
Proof. exact (@lem7003379 _128891 u x v). Qed.
Lemma lem7003384 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7003385 {_128891 : Type'} (P : _128891 -> Prop) (x : _128891) : (@IN _128891 x P) = (P x).
Proof. exact (@lem7003384 _128891 P x). Qed.
Lemma lem7003386 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (@IN _128891 x u) = (u x).
Proof. exact (@lem7003385 _128891 u x). Qed.
Lemma lem7003387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7003388 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (term9 _128891 x u) = (term10 _128891 u x).
Proof. exact (MK_COMB (@lem7003387) (@lem7003386 _128891 u x)). Qed.
Lemma lem7003390 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7003391 {_128891 : Type'} (P : _128891 -> Prop) (x : _128891) : (@IN _128891 x P) = (P x).
Proof. exact (@lem7003390 _128891 P x). Qed.
Lemma lem7003392 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) : (@IN _128891 x v) = (v x).
Proof. exact (@lem7003391 _128891 v x). Qed.
Lemma lem7003393 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7003394 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) : (term16 _128891 x v) = (term17 _128891 v x).
Proof. exact (MK_COMB (@lem7003393) (@lem7003392 _128891 v x)). Qed.
Lemma lem7003395 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term15 _128891 u x v) = (term18 _128891 u v x).
Proof. exact (MK_COMB (@lem7003388 _128891 u x) (@lem7003394 _128891 v x)). Qed.
Lemma lem7003398 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term14 _128891 x u v) = (term18 _128891 u v x).
Proof. exact (TRANS (@lem7003380 _128891 u x v) (@lem7003395 _128891 u v x)). Qed.
Lemma lem7003399 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term72 _128891 x u v) = (term73 _128891 u v x).
Proof. exact (MK_COMB (@lem7003376 _128891 u v x) (@lem7003398 _128891 u v x)). Qed.
Lemma lem7003402 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term71 _128891 x u v) = (term73 _128891 u v x).
Proof. exact (TRANS (@lem7003352 _128891 x u v) (@lem7003399 _128891 u v x)). Qed.
Lemma lem7003403 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7003404 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term74 _128891 x u v) = (term75 _128891 u v x).
Proof. exact (MK_COMB (@lem7003403) (@lem7003402 _128891 u v x)). Qed.
Lemma lem7003406 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7003407 {_128891 : Type'} (P : _128891 -> Prop) (x : _128891) : (@IN _128891 x P) = (P x).
Proof. exact (@lem7003406 _128891 P x). Qed.
Lemma lem7003408 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (@IN _128891 x u) = (u x).
Proof. exact (@lem7003407 _128891 u x). Qed.
Lemma lem7003409 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) : ((term71 _128891 x u v) = (@IN _128891 x u)) = ((term73 _128891 u v x) = (u x)).
Proof. exact (MK_COMB (@lem7003404 _128891 u v x) (@lem7003408 _128891 u x)). Qed.
Lemma lem7003412 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : (term76 _128891 v u) = (term77 _128891 v u).
Proof. exact (fun_ext (fun x : _128891 => @lem7003409 _128891 v u x)). Qed.
Lemma lem7003413 {_128891 : Type'} : (@all _128891) = (@all _128891).
Proof. exact (eq_refl (@all _128891)). Qed.
Lemma lem7003414 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : (term70 _128891 v u) = (term78 _128891 v u).
Proof. exact (MK_COMB (@lem7003413 _128891) (@lem7003412 _128891 v u)). Qed.
Lemma lem7003419 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : (term78 _128891 v u) = (term70 _128891 v u).
Proof. exact (SYM (@lem7003414 _128891 v u)). Qed.
Lemma lem7003421 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7003422 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : (term78 _128891 v u) = (term79 _128891 v u).
Proof. exact (@lem7003421 (term78 _128891 v u)). Qed.
Lemma lem7003423 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : (term79 _128891 v u) = (term78 _128891 v u).
Proof. exact (SYM (@lem7003422 _128891 v u)). Qed.
Lemma lem7003424 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (h1 : term80 _128891 v u) : term80 _128891 v u.
Proof. exact (h1). Qed.
Lemma lem7003427 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (h1 : term79 _128891 v u) : term79 _128891 v u.
Proof. exact (h1). Qed.
Lemma lem7003428 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : term81 _128891 v u.
Proof. exact (fun h0 : term79 _128891 v u => @lem7003427 _128891 v u h0). Qed.
Lemma lem7003429 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (h1 : term81 _128891 v u) : term81 _128891 v u.
Proof. exact (h1). Qed.
Lemma lem7003430 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (h1 : term79 _128891 v u) : term79 _128891 v u.
Proof. exact (h1). Qed.
Lemma lem7003431 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (h1 : term79 _128891 v u) (h2 : term81 _128891 v u) : term79 _128891 v u.
Proof. exact (@lem7003429 _128891 v u h2 (@lem7003430 _128891 v u h1)). Qed.
Lemma lem7003432 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (h1 : term79 _128891 v u) : term82 _128891 v u.
Proof. exact (fun h0 : term81 _128891 v u => @lem7003431 _128891 v u h1 h0). Qed.
Lemma lem7003433 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (h1 : term81 _128891 v u) : term81 _128891 v u.
Proof. exact (h1). Qed.
Lemma lem7003434 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (h1 : term79 _128891 v u) (h2 : term81 _128891 v u) : term79 _128891 v u.
Proof. exact (@lem7003432 _128891 v u h1 (@lem7003433 _128891 v u h2)). Qed.
Lemma lem7003435 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (h1 : term81 _128891 v u) : term81 _128891 v u.
Proof. exact (fun h0 : term79 _128891 v u => @lem7003434 _128891 v u h0 h1). Qed.
Lemma lem7003436 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : term83 _128891 v u.
Proof. exact (fun h0 : term81 _128891 v u => @lem7003435 _128891 v u h0). Qed.
Lemma lem7003439 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : term81 _128891 v u.
Proof. exact (@lem7003436 _128891 v u (@lem7003428 _128891 v u)). Qed.
Lemma lem7003440 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : term81 _128891 v u.
Proof. exact (@lem7003439 _128891 v u). Qed.
Lemma lem7003450 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7003451 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : (term79 _128891 v u) = (term84 _128891 v u).
Proof. exact (@lem7003450 (term80 _128891 v u)). Qed.
Lemma lem7003453 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7003454 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : (term84 _128891 v u) = (term78 _128891 v u).
Proof. exact (@lem7003453 (term78 _128891 v u)). Qed.
Lemma lem7003459 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : (term79 _128891 v u) = (term78 _128891 v u).
Proof. exact (TRANS (@lem7003451 _128891 v u) (@lem7003454 _128891 v u)). Qed.
Lemma lem7003466 {_128891 : Type'} (u : _128891 -> Prop) : (term85 _128891 u) = (term86 _128891 u).
Proof. exact (fun_ext (fun v : _128891 -> Prop => @lem7003459 _128891 v u)). Qed.
Lemma lem7003467 {_128891 : Type'} : (@all (_128891 -> Prop)) = (@all (_128891 -> Prop)).
Proof. exact (eq_refl (@all (_128891 -> Prop))). Qed.
Lemma lem7003468 {_128891 : Type'} (u : _128891 -> Prop) : (term87 _128891 u) = (term88 _128891 u).
Proof. exact (MK_COMB (@lem7003467 _128891) (@lem7003466 _128891 u)). Qed.
Lemma lem7003473 {_128891 : Type'} : (term89 _128891) = (term90 _128891).
Proof. exact (fun_ext (fun u : _128891 -> Prop => @lem7003468 _128891 u)). Qed.
Lemma lem7003474 {_128891 : Type'} : (@all (_128891 -> Prop)) = (@all (_128891 -> Prop)).
Proof. exact (eq_refl (@all (_128891 -> Prop))). Qed.
Lemma lem7003483 {_128891 : Type'} : (term91 _128891) = (term92 _128891).
Proof. exact (MK_COMB (@lem7003474 _128891) (@lem7003473 _128891)). Qed.
Lemma lem7003502 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) : ((term73 _128891 u v x) = (u x)) = ((term73 _128891 u v x) = (u x)).
Proof. exact (eq_refl ((term73 _128891 u v x) = (u x))). Qed.
Lemma lem7003503 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : (term77 _128891 v u) = (term77 _128891 v u).
Proof. exact (fun_ext (fun x : _128891 => @lem7003502 _128891 v u x)). Qed.
Lemma lem7003504 {_128891 : Type'} : (@all _128891) = (@all _128891).
Proof. exact (eq_refl (@all _128891)). Qed.
Lemma lem7003505 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : (term78 _128891 v u) = (term78 _128891 v u).
Proof. exact (MK_COMB (@lem7003504 _128891) (@lem7003503 _128891 v u)). Qed.
Lemma lem7003506 {_128891 : Type'} (u : _128891 -> Prop) : (term86 _128891 u) = (term86 _128891 u).
Proof. exact (fun_ext (fun v : _128891 -> Prop => @lem7003505 _128891 v u)). Qed.
Lemma lem7003507 {_128891 : Type'} : (@all (_128891 -> Prop)) = (@all (_128891 -> Prop)).
Proof. exact (eq_refl (@all (_128891 -> Prop))). Qed.
Lemma lem7003508 {_128891 : Type'} (u : _128891 -> Prop) : (term88 _128891 u) = (term88 _128891 u).
Proof. exact (MK_COMB (@lem7003507 _128891) (@lem7003506 _128891 u)). Qed.
Lemma lem7003509 {_128891 : Type'} : (term90 _128891) = (term90 _128891).
Proof. exact (fun_ext (fun u : _128891 -> Prop => @lem7003508 _128891 u)). Qed.
Lemma lem7003510 {_128891 : Type'} : (@all (_128891 -> Prop)) = (@all (_128891 -> Prop)).
Proof. exact (eq_refl (@all (_128891 -> Prop))). Qed.
Lemma lem7003511 {_128891 : Type'} : (term92 _128891) = (term92 _128891).
Proof. exact (MK_COMB (@lem7003510 _128891) (@lem7003509 _128891)). Qed.
Lemma lem7003538 {_128891 : Type'} : (term91 _128891) = (term92 _128891).
Proof. exact (TRANS (@lem7003483 _128891) (@lem7003511 _128891)). Qed.
Lemma lem7003539 {_128891 : Type'} : (term92 _128891) = (term91 _128891).
Proof. exact (SYM (@lem7003538 _128891)). Qed.
Lemma lem7003541 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7003542 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) : ((term73 _128891 u v x) = (u x)) = (term93 _128891 v u x).
Proof. exact (@lem7003541 ((term73 _128891 u v x) = (u x))). Qed.
Lemma lem7003543 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) : (term93 _128891 v u x) = ((term73 _128891 u v x) = (u x)).
Proof. exact (SYM (@lem7003542 _128891 v u x)). Qed.
Lemma lem7003544 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term94 _128891 v u x) : term94 _128891 v u x.
Proof. exact (h1). Qed.
Lemma lem7003553 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term43 _128891 u v x) = (term44 _128891 u v x).
Proof. exact (@lem17045 (u x) (v x)). Qed.
Lemma lem7003562 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) : (term45 _128891 v x) = (v x).
Proof. exact (@lem16933 (v x)). Qed.
Lemma lem7003564 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (term46 _128891 u x) = (term46 _128891 u x).
Proof. exact (eq_refl (term46 _128891 u x)). Qed.
Lemma lem7003565 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term47 _128891 u v x) = (term48 _128891 u v x).
Proof. exact (MK_COMB (@lem7003564 _128891 u x) (@lem7003562 _128891 v x)). Qed.
Lemma lem7003566 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term49 _128891 u v x) = (term47 _128891 u v x).
Proof. exact (@lem17045 (u x) (term17 _128891 v x)). Qed.
Lemma lem7003567 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term49 _128891 u v x) = (term48 _128891 u v x).
Proof. exact (TRANS (@lem7003566 _128891 u v x) (@lem7003565 _128891 u v x)). Qed.
Lemma lem7003571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7003572 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term50 _128891 u v x) = (term51 _128891 u v x).
Proof. exact (MK_COMB (@lem7003571) (@lem7003553 _128891 u v x)). Qed.
Lemma lem7003573 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term95 _128891 u v x) = (term96 _128891 u v x).
Proof. exact (MK_COMB (@lem7003572 _128891 u v x) (@lem7003567 _128891 u v x)). Qed.
Lemma lem7003574 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term97 _128891 u v x) = (term95 _128891 u v x).
Proof. exact (@lem17160 (term11 _128891 u v x) (term18 _128891 u v x)). Qed.
Lemma lem7003575 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term97 _128891 u v x) = (term96 _128891 u v x).
Proof. exact (TRANS (@lem7003574 _128891 u v x) (@lem7003573 _128891 u v x)). Qed.
Lemma lem7003580 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (u x) = (u x).
Proof. exact (eq_refl (u x)). Qed.
Lemma lem7003581 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7003582 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) : (term98 _128891 u v x) = (term99 _128891 u v x).
Proof. exact (MK_COMB (@lem7003581) (@lem7003575 _128891 u v x)). Qed.
Lemma lem7003583 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) : (term100 _128891 v u x) = (term101 _128891 v u x).
Proof. exact (MK_COMB (@lem7003582 _128891 u v x) (@lem7003580 _128891 u x)). Qed.
Lemma lem7003588 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) : (term102 _128891 v u x) = (term102 _128891 v u x).
Proof. exact (eq_refl (term102 _128891 v u x)). Qed.
Lemma lem7003589 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) : (term103 _128891 v u x) = (term104 _128891 v u x).
Proof. exact (MK_COMB (@lem7003588 _128891 v u x) (@lem7003583 _128891 v u x)). Qed.
Lemma lem7003590 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) : (term94 _128891 v u x) = (term103 _128891 v u x).
Proof. exact (@lem17646 (term73 _128891 u v x) (u x)). Qed.
Lemma lem7003595 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) : (term94 _128891 v u x) = (term104 _128891 v u x).
Proof. exact (TRANS (@lem7003590 _128891 v u x) (@lem7003589 _128891 v u x)). Qed.
Lemma lem7003664 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term94 _128891 v u x) : term104 _128891 v u x.
Proof. exact (EQ_MP (@lem7003595 _128891 v u x) (@lem7003544 _128891 v u x h1)). Qed.
Lemma lem7003665 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term105 _128891 v u x) : term105 _128891 v u x.
Proof. exact (h1). Qed.
Lemma lem7003666 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term101 _128891 v u x) : term101 _128891 v u x.
Proof. exact (h1). Qed.
Lemma lem7003668 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term105 _128891 v u x) : term73 _128891 u v x.
Proof. exact (proj1 (@lem7003665 _128891 v u x h1)). Qed.
Lemma lem7003669 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) (h1 : term11 _128891 u v x) : term11 _128891 u v x.
Proof. exact (h1). Qed.
Lemma lem7003670 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) (h1 : term18 _128891 u v x) : term18 _128891 u v x.
Proof. exact (h1). Qed.
Lemma lem7003676 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term101 _128891 v u x) : term96 _128891 u v x.
Proof. exact (proj1 (@lem7003666 _128891 v u x h1)). Qed.
Lemma lem7003677 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term101 _128891 v u x) : term48 _128891 u v x.
Proof. exact (proj2 (@lem7003676 _128891 v u x h1)). Qed.
Lemma lem7003678 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term101 _128891 v u x) : term44 _128891 u v x.
Proof. exact (proj1 (@lem7003676 _128891 v u x h1)). Qed.
Lemma lem7003716 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) : term17 _128891 u x.
Proof. exact (h1). Qed.
Lemma lem7003720 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) : term17 _128891 u x.
Proof. exact (h1). Qed.
Lemma lem7003728 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) : term17 _128891 u x.
Proof. exact (h1). Qed.
Lemma lem7003744 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) : term17 _128891 u x.
Proof. exact (h1). Qed.
Lemma lem7003752 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : v x) : v x.
Proof. exact (h1). Qed.
Lemma lem7003756 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) : term17 _128891 v x.
Proof. exact (h1). Qed.
Lemma lem7003758 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term105 _128891 v u x) : term17 _128891 u x.
Proof. exact (proj2 (@lem7003665 _128891 v u x h1)). Qed.
Lemma lem7003764 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term105 _128891 v u x) : term17 _128891 u x.
Proof. exact (proj2 (@lem7003665 _128891 v u x h1)). Qed.
Lemma lem7003772 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) : term17 _128891 u x.
Proof. exact (h1). Qed.
Lemma lem7003774 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) : term17 _128891 u x.
Proof. exact (h1). Qed.
Lemma lem7003778 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) : term17 _128891 u x.
Proof. exact (h1). Qed.
Lemma lem7003786 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) : term17 _128891 u x.
Proof. exact (h1). Qed.
Lemma lem7003790 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : v x) : v x.
Proof. exact (h1). Qed.
Lemma lem7003792 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) : term17 _128891 v x.
Proof. exact (h1). Qed.
Lemma lem7003794 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) (h1 : term11 _128891 u v x) : u x.
Proof. exact (proj1 (@lem7003669 _128891 u v x h1)). Qed.
Lemma lem7003795 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) (h1 : term11 _128891 u v x) : term63 _128891 u x.
Proof. exact (fun h0 : term17 _128891 u x => @lem7003794 _128891 u v x h1). Qed.
Lemma lem7003797 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003798 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (term63 _128891 u x) = (u x).
Proof. exact (@lem7003797 (u x)). Qed.
Lemma lem7003799 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) (h1 : term11 _128891 u v x) : u x.
Proof. exact (EQ_MP (@lem7003798 _128891 u x) (@lem7003795 _128891 u v x h1)). Qed.
Lemma lem7003802 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7003804 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (term17 _128891 u x) = (term65 _128891 u x).
Proof. exact (@lem7003802 (u x)). Qed.
Lemma lem7003807 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term105 _128891 v u x) : term65 _128891 u x.
Proof. exact (EQ_MP (@lem7003804 _128891 u x) (@lem7003758 _128891 v u x h1)). Qed.
Lemma lem7003810 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term11 _128891 u v x) (h2 : term105 _128891 v u x) : False.
Proof. exact (@lem7003807 _128891 v u x h2 (@lem7003799 _128891 u v x h1)). Qed.
Lemma lem7003811 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term11 _128891 u v x) (h2 : term105 _128891 v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem7003810 _128891 v u x h1 h2). Qed.
Lemma lem7003813 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003814 : term66 = False.
Proof. exact (@lem7003813 False). Qed.
Lemma lem7003815 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term11 _128891 u v x) (h2 : term105 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003814) (@lem7003811 _128891 v u x h1 h2)). Qed.
Lemma lem7003817 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) (h1 : term18 _128891 u v x) : u x.
Proof. exact (proj1 (@lem7003670 _128891 u v x h1)). Qed.
Lemma lem7003818 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) (h1 : term18 _128891 u v x) : term63 _128891 u x.
Proof. exact (fun h0 : term17 _128891 u x => @lem7003817 _128891 u v x h1). Qed.
Lemma lem7003820 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003821 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (term63 _128891 u x) = (u x).
Proof. exact (@lem7003820 (u x)). Qed.
Lemma lem7003822 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) (x : _128891) (h1 : term18 _128891 u v x) : u x.
Proof. exact (EQ_MP (@lem7003821 _128891 u x) (@lem7003818 _128891 u v x h1)). Qed.
Lemma lem7003825 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7003827 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (term17 _128891 u x) = (term65 _128891 u x).
Proof. exact (@lem7003825 (u x)). Qed.
Lemma lem7003830 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term105 _128891 v u x) : term65 _128891 u x.
Proof. exact (EQ_MP (@lem7003827 _128891 u x) (@lem7003764 _128891 v u x h1)). Qed.
Lemma lem7003833 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term18 _128891 u v x) (h2 : term105 _128891 v u x) : False.
Proof. exact (@lem7003830 _128891 v u x h2 (@lem7003822 _128891 u v x h1)). Qed.
Lemma lem7003834 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term18 _128891 u v x) (h2 : term105 _128891 v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem7003833 _128891 v u x h1 h2). Qed.
Lemma lem7003836 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003837 : term66 = False.
Proof. exact (@lem7003836 False). Qed.
Lemma lem7003838 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term18 _128891 u v x) (h2 : term105 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003837) (@lem7003834 _128891 v u x h1 h2)). Qed.
Lemma lem7003840 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term101 _128891 v u x) : u x.
Proof. exact (proj2 (@lem7003666 _128891 v u x h1)). Qed.
Lemma lem7003841 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term101 _128891 v u x) : term63 _128891 u x.
Proof. exact (fun h0 : term17 _128891 u x => @lem7003840 _128891 v u x h1). Qed.
Lemma lem7003843 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003844 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (term63 _128891 u x) = (u x).
Proof. exact (@lem7003843 (u x)). Qed.
Lemma lem7003845 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term101 _128891 v u x) : u x.
Proof. exact (EQ_MP (@lem7003844 _128891 u x) (@lem7003841 _128891 v u x h1)). Qed.
Lemma lem7003848 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7003850 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (term17 _128891 u x) = (term65 _128891 u x).
Proof. exact (@lem7003848 (u x)). Qed.
Lemma lem7003853 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) : term65 _128891 u x.
Proof. exact (EQ_MP (@lem7003850 _128891 u x) (@lem7003772 _128891 u x h1)). Qed.
Lemma lem7003856 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (@lem7003853 _128891 u x h1 (@lem7003845 _128891 v u x h2)). Qed.
Lemma lem7003857 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem7003856 _128891 v u x h1 h2). Qed.
Lemma lem7003859 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003860 : term66 = False.
Proof. exact (@lem7003859 False). Qed.
Lemma lem7003861 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003860) (@lem7003857 _128891 v u x h1 h2)). Qed.
Lemma lem7003863 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term101 _128891 v u x) : u x.
Proof. exact (proj2 (@lem7003666 _128891 v u x h1)). Qed.
Lemma lem7003864 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term101 _128891 v u x) : term63 _128891 u x.
Proof. exact (fun h0 : term17 _128891 u x => @lem7003863 _128891 v u x h1). Qed.
Lemma lem7003866 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003867 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (term63 _128891 u x) = (u x).
Proof. exact (@lem7003866 (u x)). Qed.
Lemma lem7003868 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term101 _128891 v u x) : u x.
Proof. exact (EQ_MP (@lem7003867 _128891 u x) (@lem7003864 _128891 v u x h1)). Qed.
Lemma lem7003871 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7003873 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (term17 _128891 u x) = (term65 _128891 u x).
Proof. exact (@lem7003871 (u x)). Qed.
Lemma lem7003876 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) : term65 _128891 u x.
Proof. exact (EQ_MP (@lem7003873 _128891 u x) (@lem7003778 _128891 u x h1)). Qed.
Lemma lem7003879 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (@lem7003876 _128891 u x h1 (@lem7003868 _128891 v u x h2)). Qed.
Lemma lem7003880 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem7003879 _128891 v u x h1 h2). Qed.
Lemma lem7003882 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003883 : term66 = False.
Proof. exact (@lem7003882 False). Qed.
Lemma lem7003884 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003883) (@lem7003880 _128891 v u x h1 h2)). Qed.
Lemma lem7003886 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term101 _128891 v u x) : u x.
Proof. exact (proj2 (@lem7003666 _128891 v u x h1)). Qed.
Lemma lem7003887 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term101 _128891 v u x) : term63 _128891 u x.
Proof. exact (fun h0 : term17 _128891 u x => @lem7003886 _128891 v u x h1). Qed.
Lemma lem7003889 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003890 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (term63 _128891 u x) = (u x).
Proof. exact (@lem7003889 (u x)). Qed.
Lemma lem7003891 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term101 _128891 v u x) : u x.
Proof. exact (EQ_MP (@lem7003890 _128891 u x) (@lem7003887 _128891 v u x h1)). Qed.
Lemma lem7003894 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7003896 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) : (term17 _128891 u x) = (term65 _128891 u x).
Proof. exact (@lem7003894 (u x)). Qed.
Lemma lem7003899 {_128891 : Type'} (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) : term65 _128891 u x.
Proof. exact (EQ_MP (@lem7003896 _128891 u x) (@lem7003786 _128891 u x h1)). Qed.
Lemma lem7003902 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (@lem7003899 _128891 u x h1 (@lem7003891 _128891 v u x h2)). Qed.
Lemma lem7003903 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem7003902 _128891 v u x h1 h2). Qed.
Lemma lem7003905 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003906 : term66 = False.
Proof. exact (@lem7003905 False). Qed.
Lemma lem7003907 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003906) (@lem7003903 _128891 v u x h1 h2)). Qed.
Lemma lem7003909 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : v x) : v x.
Proof. exact (h1). Qed.
Lemma lem7003910 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : v x) : term63 _128891 v x.
Proof. exact (fun h0 : term17 _128891 v x => @lem7003909 _128891 v x h1). Qed.
Lemma lem7003912 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003913 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) : (term63 _128891 v x) = (v x).
Proof. exact (@lem7003912 (v x)). Qed.
Lemma lem7003914 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : v x) : v x.
Proof. exact (EQ_MP (@lem7003913 _128891 v x) (@lem7003910 _128891 v x h1)). Qed.
Lemma lem7003917 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7003919 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) : (term17 _128891 v x) = (term65 _128891 v x).
Proof. exact (@lem7003917 (v x)). Qed.
Lemma lem7003922 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) : term65 _128891 v x.
Proof. exact (EQ_MP (@lem7003919 _128891 v x) (@lem7003792 _128891 v x h1)). Qed.
Lemma lem7003925 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) (h2 : v x) : False.
Proof. exact (@lem7003922 _128891 v x h1 (@lem7003914 _128891 v x h2)). Qed.
Lemma lem7003926 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) (h2 : v x) : term66.
Proof. exact (fun h0 : ~ False => @lem7003925 _128891 v x h1 h2). Qed.
Lemma lem7003928 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7003929 : term66 = False.
Proof. exact (@lem7003928 False). Qed.
Lemma lem7003930 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7003929) (@lem7003926 _128891 v x h1 h2)). Qed.
Lemma lem7003931 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) (h2 : v x) : (term17 _128891 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128891 v x => @lem7003930 _128891 v x h1 h2) (fun h3 : False => @lem7003792 _128891 v x h1)). Qed.
Lemma lem7003932 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7003931 _128891 v x h1 h2) (@lem7003792 _128891 v x h1)). Qed.
Lemma lem7003933 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) (h2 : v x) : (v x) = False.
Proof. exact (prop_ext (fun h3 : v x => @lem7003932 _128891 v x h1 h2) (fun h3 : False => @lem7003790 _128891 v x h2)). Qed.
Lemma lem7003934 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7003933 _128891 v x h1 h2) (@lem7003790 _128891 v x h2)). Qed.
Lemma lem7003935 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : (term17 _128891 u x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128891 u x => @lem7003907 _128891 v u x h1 h2) (fun h3 : False => @lem7003786 _128891 u x h1)). Qed.
Lemma lem7003936 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003935 _128891 v u x h1 h2) (@lem7003786 _128891 u x h1)). Qed.
Lemma lem7003937 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : (term17 _128891 u x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128891 u x => @lem7003884 _128891 v u x h1 h2) (fun h3 : False => @lem7003778 _128891 u x h1)). Qed.
Lemma lem7003938 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003937 _128891 v u x h1 h2) (@lem7003778 _128891 u x h1)). Qed.
Lemma lem7003939 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : (term17 _128891 u x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128891 u x => @lem7003861 _128891 v u x h1 h2) (fun h3 : False => @lem7003774 _128891 u x h1)). Qed.
Lemma lem7003940 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003939 _128891 v u x h1 h2) (@lem7003774 _128891 u x h1)). Qed.
Lemma lem7003941 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : (term17 _128891 u x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128891 u x => @lem7003940 _128891 v u x h1 h2) (fun h3 : False => @lem7003772 _128891 u x h1)). Qed.
Lemma lem7003942 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003941 _128891 v u x h1 h2) (@lem7003772 _128891 u x h1)). Qed.
Lemma lem7003943 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) (h2 : v x) : (term17 _128891 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128891 v x => @lem7003934 _128891 v x h1 h2) (fun h3 : False => @lem7003756 _128891 v x h1)). Qed.
Lemma lem7003944 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7003943 _128891 v x h1 h2) (@lem7003756 _128891 v x h1)). Qed.
Lemma lem7003945 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) (h2 : v x) : (v x) = False.
Proof. exact (prop_ext (fun h3 : v x => @lem7003944 _128891 v x h1 h2) (fun h3 : False => @lem7003752 _128891 v x h2)). Qed.
Lemma lem7003946 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7003945 _128891 v x h1 h2) (@lem7003752 _128891 v x h2)). Qed.
Lemma lem7003947 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : (term17 _128891 u x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128891 u x => @lem7003936 _128891 v u x h1 h2) (fun h3 : False => @lem7003744 _128891 u x h1)). Qed.
Lemma lem7003948 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003947 _128891 v u x h1 h2) (@lem7003744 _128891 u x h1)). Qed.
Lemma lem7003949 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : (term17 _128891 u x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128891 u x => @lem7003938 _128891 v u x h1 h2) (fun h3 : False => @lem7003728 _128891 u x h1)). Qed.
Lemma lem7003950 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003949 _128891 v u x h1 h2) (@lem7003728 _128891 u x h1)). Qed.
Lemma lem7003951 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : (term17 _128891 u x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128891 u x => @lem7003942 _128891 v u x h1 h2) (fun h3 : False => @lem7003720 _128891 u x h1)). Qed.
Lemma lem7003952 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003951 _128891 v u x h1 h2) (@lem7003720 _128891 u x h1)). Qed.
Lemma lem7003953 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : (term17 _128891 u x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128891 u x => @lem7003952 _128891 v u x h1 h2) (fun h3 : False => @lem7003716 _128891 u x h1)). Qed.
Lemma lem7003954 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003953 _128891 v u x h1 h2) (@lem7003716 _128891 u x h1)). Qed.
Lemma lem7003955 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) (h2 : v x) : (term17 _128891 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128891 v x => @lem7003946 _128891 v x h1 h2) (fun h3 : False => @lem7003756 _128891 v x h1)). Qed.
Lemma lem7003956 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7003955 _128891 v x h1 h2) (@lem7003756 _128891 v x h1)). Qed.
Lemma lem7003957 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) (h2 : v x) : (v x) = False.
Proof. exact (prop_ext (fun h3 : v x => @lem7003956 _128891 v x h1 h2) (fun h3 : False => @lem7003752 _128891 v x h2)). Qed.
Lemma lem7003958 {_128891 : Type'} (v : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7003957 _128891 v x h1 h2) (@lem7003752 _128891 v x h2)). Qed.
Lemma lem7003959 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : (term17 _128891 u x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128891 u x => @lem7003948 _128891 v u x h1 h2) (fun h3 : False => @lem7003744 _128891 u x h1)). Qed.
Lemma lem7003960 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003959 _128891 v u x h1 h2) (@lem7003744 _128891 u x h1)). Qed.
Lemma lem7003961 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : (term17 _128891 u x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128891 u x => @lem7003950 _128891 v u x h1 h2) (fun h3 : False => @lem7003728 _128891 u x h1)). Qed.
Lemma lem7003962 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003961 _128891 v u x h1 h2) (@lem7003728 _128891 u x h1)). Qed.
Lemma lem7003963 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : (term17 _128891 u x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128891 u x => @lem7003954 _128891 v u x h1 h2) (fun h3 : False => @lem7003720 _128891 u x h1)). Qed.
Lemma lem7003964 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003963 _128891 v u x h1 h2) (@lem7003720 _128891 u x h1)). Qed.
Lemma lem7003965 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : (term17 _128891 u x) = False.
Proof. exact (prop_ext (fun h3 : term17 _128891 u x => @lem7003964 _128891 v u x h1 h2) (fun h3 : False => @lem7003716 _128891 u x h1)). Qed.
Lemma lem7003966 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003965 _128891 v u x h1 h2) (@lem7003716 _128891 u x h1)). Qed.
Lemma lem7003967 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : v x) (h2 : term101 _128891 v u x) : False.
Proof. exact (or_elim (@lem7003678 _128891 v u x h2) (fun h0 : term17 _128891 u x => @lem7003960 _128891 v u x h0 h2) (fun h0 : term17 _128891 v x => @lem7003958 _128891 v x h0 h1)). Qed.
Lemma lem7003968 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term17 _128891 u x) (h2 : term101 _128891 v u x) : False.
Proof. exact (or_elim (@lem7003678 _128891 v u x h2) (fun h0 : term17 _128891 u x => @lem7003966 _128891 v u x h1 h2) (fun h0 : term17 _128891 v x => @lem7003962 _128891 v u x h1 h2)). Qed.
Lemma lem7003969 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term101 _128891 v u x) : False.
Proof. exact (or_elim (@lem7003677 _128891 v u x h1) (fun h0 : term17 _128891 u x => @lem7003968 _128891 v u x h0 h1) (fun h0 : v x => @lem7003967 _128891 v u x h0 h1)). Qed.
Lemma lem7003970 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term105 _128891 v u x) : False.
Proof. exact (or_elim (@lem7003668 _128891 v u x h1) (fun h0 : term11 _128891 u v x => @lem7003815 _128891 v u x h0 h1) (fun h0 : term18 _128891 u v x => @lem7003838 _128891 v u x h0 h1)). Qed.
Lemma lem7003971 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term94 _128891 v u x) : False.
Proof. exact (or_elim (@lem7003664 _128891 v u x h1) (fun h0 : term105 _128891 v u x => @lem7003970 _128891 v u x h0) (fun h0 : term101 _128891 v u x => @lem7003969 _128891 v u x h0)). Qed.
Lemma lem7003972 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term94 _128891 v u x) : (term94 _128891 v u x) = False.
Proof. exact (prop_ext (fun h2 : term94 _128891 v u x => @lem7003971 _128891 v u x h1) (fun h2 : False => @lem7003544 _128891 v u x h1)). Qed.
Lemma lem7003973 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) (h1 : term94 _128891 v u x) : False.
Proof. exact (EQ_MP (@lem7003972 _128891 v u x h1) (@lem7003544 _128891 v u x h1)). Qed.
Lemma lem7003974 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) : term93 _128891 v u x.
Proof. exact (fun h0 : term94 _128891 v u x => @lem7003973 _128891 v u x h0). Qed.
Lemma lem7003975 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (x : _128891) : (term73 _128891 u v x) = (u x).
Proof. exact (EQ_MP (@lem7003543 _128891 v u x) (@lem7003974 _128891 v u x)). Qed.
Lemma lem7003980 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : term78 _128891 v u.
Proof. exact (fun x : _128891 => @lem7003975 _128891 v u x). Qed.
Lemma lem7003985 {_128891 : Type'} (u : _128891 -> Prop) : term88 _128891 u.
Proof. exact (fun v : _128891 -> Prop => @lem7003980 _128891 v u). Qed.
Lemma lem7003990 {_128891 : Type'} : term92 _128891.
Proof. exact (fun u : _128891 -> Prop => @lem7003985 _128891 u). Qed.
Lemma lem7003991 {_128891 : Type'} : term91 _128891.
Proof. exact (EQ_MP (@lem7003539 _128891) (@lem7003990 _128891)). Qed.
Lemma lem7003992 {_128891 : Type'} (u : _128891 -> Prop) : term106 _128891 u.
Proof. exact (@lem7003991 _128891 u). Qed.
Lemma lem7003993 {_128891 : Type'} (u : _128891 -> Prop) : (term106 _128891 u) = (term87 _128891 u).
Proof. exact (eq_refl (term106 _128891 u)). Qed.
Lemma lem7003994 {_128891 : Type'} (u : _128891 -> Prop) : term87 _128891 u.
Proof. exact (EQ_MP (@lem7003993 _128891 u) (@lem7003992 _128891 u)). Qed.
Lemma lem7003995 {_128891 : Type'} (u : _128891 -> Prop) (v : _128891 -> Prop) : term107 _128891 u v.
Proof. exact (@lem7003994 _128891 u v). Qed.
Lemma lem7003996 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : (term107 _128891 u v) = (term79 _128891 v u).
Proof. exact (eq_refl (term107 _128891 u v)). Qed.
Lemma lem7003997 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : term79 _128891 v u.
Proof. exact (EQ_MP (@lem7003996 _128891 v u) (@lem7003995 _128891 u v)). Qed.
Lemma lem7003999 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : term79 _128891 v u.
Proof. exact (@lem7003440 _128891 v u (@lem7003997 _128891 v u)). Qed.
Lemma lem7004000 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (h1 : term80 _128891 v u) : False.
Proof. exact (@lem7003999 _128891 v u (@lem7003424 _128891 v u h1)). Qed.
Lemma lem7004001 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (h1 : term80 _128891 v u) : (term80 _128891 v u) = False.
Proof. exact (prop_ext (fun h2 : term80 _128891 v u => @lem7004000 _128891 v u h1) (fun h2 : False => @lem7003424 _128891 v u h1)). Qed.
Lemma lem7004002 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) (h1 : term80 _128891 v u) : False.
Proof. exact (EQ_MP (@lem7004001 _128891 v u h1) (@lem7003424 _128891 v u h1)). Qed.
Lemma lem7004003 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : term79 _128891 v u.
Proof. exact (fun h0 : term80 _128891 v u => @lem7004002 _128891 v u h0). Qed.
Lemma lem7004004 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : term78 _128891 v u.
Proof. exact (EQ_MP (@lem7003423 _128891 v u) (@lem7004003 _128891 v u)). Qed.
Lemma lem7004005 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : term70 _128891 v u.
Proof. exact (EQ_MP (@lem7003419 _128891 v u) (@lem7004004 _128891 v u)). Qed.
Lemma lem7004007 {A : Type'} : term108 A.
Proof. exact (@lem6925097 A). Qed.
Lemma lem7004008 {A : Type'} (f : A -> nat) : term109 A f.
Proof. exact (@lem7004007 A f). Qed.
Lemma lem7004009 {A : Type'} (f : A -> nat) : (term109 A f) = (term110 A f).
Proof. exact (eq_refl (term109 A f)). Qed.
Lemma lem7004010 {A : Type'} (f : A -> nat) : term110 A f.
Proof. exact (EQ_MP (@lem7004009 A f) (@lem7004008 A f)). Qed.
Lemma lem7004011 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : term111 A f u v.
Proof. exact (@lem7004010 A f (@INTER A u v)). Qed.
Lemma lem7004012 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term111 A f u v) = (term112 A u v f).
Proof. exact (eq_refl (term111 A f u v)). Qed.
Lemma lem7004013 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term112 A u v f.
Proof. exact (EQ_MP (@lem7004012 A u v f) (@lem7004011 A f u v)). Qed.
Lemma lem7004014 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term113 A u v f) : term113 A u v f.
Proof. exact (h1). Qed.
Lemma lem7004015 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term114 A u v f) : term114 A u v f.
Proof. exact (h1). Qed.
Lemma lem7004016 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : @FINITE A u.
Proof. exact (h1). Qed.
Lemma lem7004017 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : term115 A u v f.
Proof. exact (h1). Qed.
Lemma lem7004018 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : @FINITE A v.
Proof. exact (h1). Qed.
Lemma lem7004019 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term112 A u v f) : term112 A u v f.
Proof. exact (h1). Qed.
Lemma lem7004020 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term112 A u v f) : term116 A f u v.
Proof. exact (@lem7004019 A u v f h1 (@DIFF A u v)). Qed.
Lemma lem7004021 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term116 A f u v) = (term117 A u v f).
Proof. exact (eq_refl (term116 A f u v)). Qed.
Lemma lem7004022 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term112 A u v f) : term117 A u v f.
Proof. exact (EQ_MP (@lem7004021 A u v f) (@lem7004020 A u v f h1)). Qed.
Lemma lem7004023 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term112 A u v f) : term118 A f v u.
Proof. exact (@lem7004019 A u v f h1 (@DIFF A v u)). Qed.
Lemma lem7004024 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term118 A f v u) = (term119 A v u f).
Proof. exact (eq_refl (term118 A f v u)). Qed.
Lemma lem7004025 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term112 A u v f) : term119 A v u f.
Proof. exact (EQ_MP (@lem7004024 A v u f) (@lem7004023 A u v f h1)). Qed.
Lemma lem7004039 {_128891 : Type'} (v : _128891 -> Prop) (u : _128891 -> Prop) : (term69 _128891 u v) = u.
Proof. exact (EQ_MP (@lem7003342 _128891 v u) (@lem7004005 _128891 v u)). Qed.
Lemma lem7004040 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term69 A u v) = u.
Proof. exact (@lem7004039 A v u). Qed.
Lemma lem7004041 {A : Type'} : (@nsum A) = (@nsum A).
Proof. exact (eq_refl (@nsum A)). Qed.
Lemma lem7004042 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term120 A u v) = (@nsum A u).
Proof. exact (MK_COMB (@lem7004041 A) (@lem7004040 A v u)). Qed.
Lemma lem7004043 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7004044 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term121 A u v f) = (@nsum A u f).
Proof. exact (MK_COMB (@lem7004042 A v u) (@lem7004043 A f)). Qed.
Lemma lem7004045 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7004046 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term122 A u v f) = (term123 A u f).
Proof. exact (MK_COMB (@lem7004045) (@lem7004044 A v u f)). Qed.
Lemma lem7004047 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term124 A u v f) = (term124 A u v f).
Proof. exact (eq_refl (term124 A u v f)). Qed.
Lemma lem7004048 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : ((term121 A u v f) = (term124 A u v f)) = ((@nsum A u f) = (term124 A u v f)).
Proof. exact (MK_COMB (@lem7004046 A v u f) (@lem7004047 A u v f)). Qed.
Lemma lem7004051 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term125 A u v) = (term125 A u v).
Proof. exact (eq_refl (term125 A u v)). Qed.
Lemma lem7004052 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term117 A u v f) = (term126 A u v f).
Proof. exact (MK_COMB (@lem7004051 A u v) (@lem7004048 A u v f)). Qed.
Lemma lem7004055 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7004056 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term127 A u v f) = (term128 A u v f).
Proof. exact (MK_COMB (@lem7004055) (@lem7004052 A u v f)). Qed.
Lemma lem7004068 {_128878 : Type'} (u : _128878 -> Prop) (v : _128878 -> Prop) : (term1 _128878 v u) = v.
Proof. exact (EQ_MP (@lem7002653 _128878 u v) (@lem7003316 _128878 u v)). Qed.
Lemma lem7004069 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term1 A v u) = v.
Proof. exact (@lem7004068 A u v). Qed.
Lemma lem7004070 {A : Type'} : (@nsum A) = (@nsum A).
Proof. exact (eq_refl (@nsum A)). Qed.
Lemma lem7004071 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term129 A v u) = (@nsum A v).
Proof. exact (MK_COMB (@lem7004070 A) (@lem7004069 A u v)). Qed.
Lemma lem7004072 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7004073 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term130 A v u f) = (@nsum A v f).
Proof. exact (MK_COMB (@lem7004071 A u v) (@lem7004072 A f)). Qed.
Lemma lem7004074 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7004075 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term131 A v u f) = (term123 A v f).
Proof. exact (MK_COMB (@lem7004074) (@lem7004073 A u v f)). Qed.
Lemma lem7004076 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term132 A v u f) = (term132 A v u f).
Proof. exact (eq_refl (term132 A v u f)). Qed.
Lemma lem7004077 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term130 A v u f) = (term132 A v u f)) = ((@nsum A v f) = (term132 A v u f)).
Proof. exact (MK_COMB (@lem7004075 A u v f) (@lem7004076 A v u f)). Qed.
Lemma lem7004080 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term133 A v u) = (term133 A v u).
Proof. exact (eq_refl (term133 A v u)). Qed.
Lemma lem7004081 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term119 A v u f) = (term134 A v u f).
Proof. exact (MK_COMB (@lem7004080 A v u) (@lem7004077 A v u f)). Qed.
Lemma lem7004084 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7004085 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term135 A v u f) = (term136 A v u f).
Proof. exact (MK_COMB (@lem7004084) (@lem7004081 A v u f)). Qed.
Lemma lem7004086 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term137 A u v f) = (term137 A u v f).
Proof. exact (eq_refl (term137 A u v f)). Qed.
Lemma lem7004087 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term138 A u v f) = (term139 A u v f).
Proof. exact (MK_COMB (@lem7004085 A v u f) (@lem7004086 A u v f)). Qed.
Lemma lem7004090 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term140 A u v f) = (term141 A u v f).
Proof. exact (MK_COMB (@lem7004056 A u v f) (@lem7004087 A u v f)). Qed.
Lemma lem7004093 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term141 A u v f) = (term140 A u v f).
Proof. exact (SYM (@lem7004090 A u v f)). Qed.
Lemma lem7004094 {A : Type'} (s : A -> Prop) : term142 A s.
Proof. exact (@lem3607909 A s). Qed.
Lemma lem7004095 {A : Type'} (s : A -> Prop) : (term142 A s) = (term143 A s).
Proof. exact (eq_refl (term142 A s)). Qed.
Lemma lem7004096 {A : Type'} (s : A -> Prop) : term143 A s.
Proof. exact (EQ_MP (@lem7004095 A s) (@lem7004094 A s)). Qed.
Lemma lem7004097 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term144 A s t.
Proof. exact (@lem7004096 A s t). Qed.
Lemma lem7004098 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term144 A s t) = (term145 A s t).
Proof. exact (eq_refl (term144 A s t)). Qed.
Lemma lem7004099 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term145 A s t.
Proof. exact (EQ_MP (@lem7004098 A s t) (@lem7004097 A s t)). Qed.
Lemma lem7004100 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term146 A s t) : term146 A s t.
Proof. exact (h1). Qed.
Lemma lem7004101 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term146 A s t) : term147 A s t.
Proof. exact (@lem7004099 A s t (@lem7004100 A s t h1)). Qed.
Lemma lem7004102 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term147 A s t) = ((term147 A s t) = True).
Proof. exact (@lem7 (term147 A s t)). Qed.
Lemma lem7004103 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term146 A s t) : (term147 A s t) = True.
Proof. exact (EQ_MP (@lem7004102 A s t) (@lem7004101 A s t h1)). Qed.
Lemma lem7004109 {_97970 : Type'} (s : _97970 -> Prop) : term148 _97970 s.
Proof. exact (@lem3734933 _97970 s). Qed.
Lemma lem7004110 {_97970 : Type'} (s : _97970 -> Prop) : (term148 _97970 s) = (term149 _97970 s).
Proof. exact (eq_refl (term148 _97970 s)). Qed.
Lemma lem7004111 {_97970 : Type'} (s : _97970 -> Prop) : term149 _97970 s.
Proof. exact (EQ_MP (@lem7004110 _97970 s) (@lem7004109 _97970 s)). Qed.
Lemma lem7004112 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term150 _97970 s t.
Proof. exact (@lem7004111 _97970 s t). Qed.
Lemma lem7004113 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term150 _97970 s t) = (term151 _97970 s t).
Proof. exact (eq_refl (term150 _97970 s t)). Qed.
Lemma lem7004114 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term151 _97970 s t.
Proof. exact (EQ_MP (@lem7004113 _97970 s t) (@lem7004112 _97970 s t)). Qed.
Lemma lem7004115 {_97970 : Type'} (s : _97970 -> Prop) (h1 : @FINITE _97970 s) : @FINITE _97970 s.
Proof. exact (h1). Qed.
Lemma lem7004116 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) (h1 : @FINITE _97970 s) : term152 _97970 s t.
Proof. exact (@lem7004114 _97970 s t (@lem7004115 _97970 s h1)). Qed.
Lemma lem7004117 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term152 _97970 s t) = ((term152 _97970 s t) = True).
Proof. exact (@lem7 (term152 _97970 s t)). Qed.
Lemma lem7004118 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) (h1 : @FINITE _97970 s) : (term152 _97970 s t) = True.
Proof. exact (EQ_MP (@lem7004117 _97970 s t) (@lem7004116 _97970 t s h1)). Qed.
Lemma lem7004124 {A : Type'} (u : A -> Prop) : (@FINITE A u) = ((@FINITE A u) = True).
Proof. exact (@lem7 (@FINITE A u)). Qed.
Lemma lem7004126 {A : Type'} (v : A -> Prop) : (@FINITE A v) = ((@FINITE A v) = True).
Proof. exact (@lem7 (@FINITE A v)). Qed.
Lemma lem7004141 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term153 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7004142 (p : Prop) (q : Prop) (p' : Prop) : term154 p q p'.
Proof. exact (fun q' : Prop => @lem7004141 p q p' q'). Qed.
Lemma lem7004143 (p : Prop) (q : Prop) : term155 p q.
Proof. exact (fun p' : Prop => @lem7004142 p q p'). Qed.
Lemma lem7004144 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term156 A u v f.
Proof. exact (@lem7004143 (term126 A u v f) (term139 A u v f)). Qed.
Lemma lem7004145 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) : term157 A u v f p'.
Proof. exact (@lem7004144 A u v f p'). Qed.
Lemma lem7004146 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) : (term157 A u v f p') = (term158 A u v f p').
Proof. exact (eq_refl (term157 A u v f p')). Qed.
Lemma lem7004147 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) : term158 A u v f p'.
Proof. exact (EQ_MP (@lem7004146 A u v f p') (@lem7004145 A u v f p')). Qed.
Lemma lem7004148 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term159 A u v f p' q'.
Proof. exact (@lem7004147 A u v f p' q'). Qed.
Lemma lem7004149 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : (term159 A u v f p' q') = (term160 A u v f p' q').
Proof. exact (eq_refl (term159 A u v f p' q')). Qed.
Lemma lem7004150 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term160 A u v f p' q'.
Proof. exact (EQ_MP (@lem7004149 A u v f p' q') (@lem7004148 A u v f p' q')). Qed.
Lemma lem7004154 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term153 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7004155 (p : Prop) (q : Prop) (p' : Prop) : term154 p q p'.
Proof. exact (fun q' : Prop => @lem7004154 p q p' q'). Qed.
Lemma lem7004156 (p : Prop) (q : Prop) : term155 p q.
Proof. exact (fun p' : Prop => @lem7004155 p q p'). Qed.
Lemma lem7004157 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term161 A u v f.
Proof. exact (@lem7004156 (term162 A u v) ((@nsum A u f) = (term124 A u v f))). Qed.
Lemma lem7004158 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) : term163 A u v f p'.
Proof. exact (@lem7004157 A u v f p'). Qed.
Lemma lem7004159 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) : (term163 A u v f p') = (term164 A u v f p').
Proof. exact (eq_refl (term163 A u v f p')). Qed.
Lemma lem7004160 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) : term164 A u v f p'.
Proof. exact (EQ_MP (@lem7004159 A u v f p') (@lem7004158 A u v f p')). Qed.
Lemma lem7004161 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term165 A u v f p' q'.
Proof. exact (@lem7004160 A u v f p' q'). Qed.
Lemma lem7004162 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : (term165 A u v f p' q') = (term166 A u v f p' q').
Proof. exact (eq_refl (term165 A u v f p' q')). Qed.
Lemma lem7004163 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term166 A u v f p' q'.
Proof. exact (EQ_MP (@lem7004162 A u v f p' q') (@lem7004161 A u v f p' q')). Qed.
Lemma lem7004167 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term167 A s t.
Proof. exact (fun h0 : term146 A s t => @lem7004103 A s t h0). Qed.
Lemma lem7004168 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term167 A s t.
Proof. exact (@lem7004167 A s t). Qed.
Lemma lem7004169 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term167 A u v.
Proof. exact (@lem7004168 A u v). Qed.
Lemma lem7004173 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : (@FINITE A u) = True.
Proof. exact (EQ_MP (@lem7004124 A u) (@lem7004016 A u h1)). Qed.
Lemma lem7004174 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7004175 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : (term168 A u) = (or True).
Proof. exact (MK_COMB (@lem7004174) (@lem7004173 A u h1)). Qed.
Lemma lem7004177 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : (@FINITE A v) = True.
Proof. exact (EQ_MP (@lem7004126 A v) (@lem7004018 A v h1)). Qed.
Lemma lem7004178 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term146 A u v) = (True \/ True).
Proof. exact (MK_COMB (@lem7004175 A u h1) (@lem7004177 A v h2)). Qed.
Lemma lem7004180 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem7004181 : (True \/ True) = True.
Proof. exact (@lem7004180 True). Qed.
Lemma lem7004182 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term146 A u v) = True.
Proof. exact (TRANS (@lem7004178 A u v h1 h2) (@lem7004181)). Qed.
Lemma lem7004183 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : True = (term146 A u v).
Proof. exact (SYM (@lem7004182 A u v h1 h2)). Qed.
Lemma lem7004184 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term146 A u v.
Proof. exact (EQ_MP (@lem7004183 A u v h1 h2) (@lem0)). Qed.
Lemma lem7004185 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term147 A u v) = True.
Proof. exact (@lem7004169 A u v (@lem7004184 A u v h1 h2)). Qed.
Lemma lem7004186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7004187 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term169 A u v) = (and True).
Proof. exact (MK_COMB (@lem7004186) (@lem7004185 A u v h1 h2)). Qed.
Lemma lem7004191 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term170 _97970 s t.
Proof. exact (fun h0 : @FINITE _97970 s => @lem7004118 _97970 t s h0). Qed.
Lemma lem7004192 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term170 A s t.
Proof. exact (@lem7004191 A s t). Qed.
Lemma lem7004193 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term170 A u v.
Proof. exact (@lem7004192 A u v). Qed.
Lemma lem7004195 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : (@FINITE A u) = True.
Proof. exact (EQ_MP (@lem7004124 A u) (@lem7004016 A u h1)). Qed.
Lemma lem7004196 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : True = (@FINITE A u).
Proof. exact (SYM (@lem7004195 A u h1)). Qed.
Lemma lem7004197 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : @FINITE A u.
Proof. exact (EQ_MP (@lem7004196 A u h1) (@lem0)). Qed.
Lemma lem7004198 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : @FINITE A u) : (term152 A u v) = True.
Proof. exact (@lem7004193 A u v (@lem7004197 A u h1)). Qed.
Lemma lem7004199 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7004200 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : @FINITE A u) : (term171 A u v) = (and True).
Proof. exact (MK_COMB (@lem7004199) (@lem7004198 A v u h1)). Qed.
Lemma lem7004201 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term172 A u v) = (term172 A u v).
Proof. exact (eq_refl (term172 A u v)). Qed.
Lemma lem7004202 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : @FINITE A u) : (term173 A u v) = (term174 A u v).
Proof. exact (MK_COMB (@lem7004200 A v u h1) (@lem7004201 A u v)). Qed.
Lemma lem7004204 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7004205 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term174 A u v) = (term172 A u v).
Proof. exact (@lem7004204 (term172 A u v)). Qed.
Lemma lem7004206 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : @FINITE A u) : (term173 A u v) = (term172 A u v).
Proof. exact (TRANS (@lem7004202 A v u h1) (@lem7004205 A u v)). Qed.
Lemma lem7004207 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term162 A u v) = (term174 A u v).
Proof. exact (MK_COMB (@lem7004187 A u v h1 h2) (@lem7004206 A v u h1)). Qed.
Lemma lem7004209 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7004210 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term174 A u v) = (term172 A u v).
Proof. exact (@lem7004209 (term172 A u v)). Qed.
Lemma lem7004211 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term162 A u v) = (term172 A u v).
Proof. exact (TRANS (@lem7004207 A u v h1 h2) (@lem7004210 A u v)). Qed.
Lemma lem7004212 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (q' : Prop) : term175 A f u v q'.
Proof. exact (@lem7004163 A u v f (term172 A u v) q'). Qed.
Lemma lem7004213 {A : Type'} (f : A -> nat) (q' : Prop) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term176 A f u v q'.
Proof. exact (@lem7004212 A f u v q' (@lem7004211 A u v h1 h2)). Qed.
Lemma lem7004219 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : ((@nsum A u f) = (term124 A u v f)) = ((@nsum A u f) = (term124 A u v f)).
Proof. exact (eq_refl ((@nsum A u f) = (term124 A u v f))). Qed.
Lemma lem7004220 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term177 A u v f.
Proof. exact (fun h0 : term172 A u v => @lem7004219 A u v f). Qed.
Lemma lem7004221 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term178 A u v f.
Proof. exact (@lem7004213 A f ((@nsum A u f) = (term124 A u v f)) u v h1 h2). Qed.
Lemma lem7004222 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term126 A u v f) = (term179 A u v f).
Proof. exact (@lem7004221 A f u v h1 h2 (@lem7004220 A u v f)). Qed.
Lemma lem7004250 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (q' : Prop) : term180 A u v f q'.
Proof. exact (@lem7004150 A u v f (term179 A u v f) q'). Qed.
Lemma lem7004251 {A : Type'} (f : A -> nat) (q' : Prop) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term181 A u v f q'.
Proof. exact (@lem7004250 A u v f q' (@lem7004222 A f u v h1 h2)). Qed.
Lemma lem7004263 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term153 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7004264 (p : Prop) (q : Prop) (p' : Prop) : term154 p q p'.
Proof. exact (fun q' : Prop => @lem7004263 p q p' q'). Qed.
Lemma lem7004265 (p : Prop) (q : Prop) : term155 p q.
Proof. exact (fun p' : Prop => @lem7004264 p q p'). Qed.
Lemma lem7004266 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term182 A u v f.
Proof. exact (@lem7004265 (term134 A v u f) (term137 A u v f)). Qed.
Lemma lem7004267 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) : term183 A u v f p'.
Proof. exact (@lem7004266 A u v f p'). Qed.
Lemma lem7004268 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) : (term183 A u v f p') = (term184 A u v f p').
Proof. exact (eq_refl (term183 A u v f p')). Qed.
Lemma lem7004269 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) : term184 A u v f p'.
Proof. exact (EQ_MP (@lem7004268 A u v f p') (@lem7004267 A u v f p')). Qed.
Lemma lem7004270 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term185 A u v f p' q'.
Proof. exact (@lem7004269 A u v f p' q'). Qed.
Lemma lem7004271 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : (term185 A u v f p' q') = (term186 A u v f p' q').
Proof. exact (eq_refl (term185 A u v f p' q')). Qed.
Lemma lem7004272 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term186 A u v f p' q'.
Proof. exact (EQ_MP (@lem7004271 A u v f p' q') (@lem7004270 A u v f p' q')). Qed.
Lemma lem7004276 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term153 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7004277 (p : Prop) (q : Prop) (p' : Prop) : term154 p q p'.
Proof. exact (fun q' : Prop => @lem7004276 p q p' q'). Qed.
Lemma lem7004278 (p : Prop) (q : Prop) : term155 p q.
Proof. exact (fun p' : Prop => @lem7004277 p q p'). Qed.
Lemma lem7004279 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term187 A v u f.
Proof. exact (@lem7004278 (term188 A v u) ((@nsum A v f) = (term132 A v u f))). Qed.
Lemma lem7004280 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (p' : Prop) : term189 A v u f p'.
Proof. exact (@lem7004279 A v u f p'). Qed.
Lemma lem7004281 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (p' : Prop) : (term189 A v u f p') = (term190 A v u f p').
Proof. exact (eq_refl (term189 A v u f p')). Qed.
Lemma lem7004282 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (p' : Prop) : term190 A v u f p'.
Proof. exact (EQ_MP (@lem7004281 A v u f p') (@lem7004280 A v u f p')). Qed.
Lemma lem7004283 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term191 A v u f p' q'.
Proof. exact (@lem7004282 A v u f p' q'). Qed.
Lemma lem7004284 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : (term191 A v u f p' q') = (term192 A v u f p' q').
Proof. exact (eq_refl (term191 A v u f p' q')). Qed.
Lemma lem7004285 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term192 A v u f p' q'.
Proof. exact (EQ_MP (@lem7004284 A v u f p' q') (@lem7004283 A v u f p' q')). Qed.
Lemma lem7004289 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term167 A s t.
Proof. exact (fun h0 : term146 A s t => @lem7004103 A s t h0). Qed.
Lemma lem7004290 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term167 A s t.
Proof. exact (@lem7004289 A s t). Qed.
Lemma lem7004291 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term167 A u v.
Proof. exact (@lem7004290 A u v). Qed.
Lemma lem7004295 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : (@FINITE A u) = True.
Proof. exact (EQ_MP (@lem7004124 A u) (@lem7004016 A u h1)). Qed.
Lemma lem7004296 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7004297 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : (term168 A u) = (or True).
Proof. exact (MK_COMB (@lem7004296) (@lem7004295 A u h1)). Qed.
Lemma lem7004299 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : (@FINITE A v) = True.
Proof. exact (EQ_MP (@lem7004126 A v) (@lem7004018 A v h1)). Qed.
Lemma lem7004300 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term146 A u v) = (True \/ True).
Proof. exact (MK_COMB (@lem7004297 A u h1) (@lem7004299 A v h2)). Qed.
Lemma lem7004302 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem7004303 : (True \/ True) = True.
Proof. exact (@lem7004302 True). Qed.
Lemma lem7004304 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term146 A u v) = True.
Proof. exact (TRANS (@lem7004300 A u v h1 h2) (@lem7004303)). Qed.
Lemma lem7004305 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : True = (term146 A u v).
Proof. exact (SYM (@lem7004304 A u v h1 h2)). Qed.
Lemma lem7004306 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term146 A u v.
Proof. exact (EQ_MP (@lem7004305 A u v h1 h2) (@lem0)). Qed.
Lemma lem7004307 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term147 A u v) = True.
Proof. exact (@lem7004291 A u v (@lem7004306 A u v h1 h2)). Qed.
Lemma lem7004308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7004309 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term169 A u v) = (and True).
Proof. exact (MK_COMB (@lem7004308) (@lem7004307 A u v h1 h2)). Qed.
Lemma lem7004313 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term170 _97970 s t.
Proof. exact (fun h0 : @FINITE _97970 s => @lem7004118 _97970 t s h0). Qed.
Lemma lem7004314 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term170 A s t.
Proof. exact (@lem7004313 A s t). Qed.
Lemma lem7004315 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term170 A v u.
Proof. exact (@lem7004314 A v u). Qed.
Lemma lem7004317 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : (@FINITE A v) = True.
Proof. exact (EQ_MP (@lem7004126 A v) (@lem7004018 A v h1)). Qed.
Lemma lem7004318 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : True = (@FINITE A v).
Proof. exact (SYM (@lem7004317 A v h1)). Qed.
Lemma lem7004319 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : @FINITE A v.
Proof. exact (EQ_MP (@lem7004318 A v h1) (@lem0)). Qed.
Lemma lem7004320 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A v) : (term152 A v u) = True.
Proof. exact (@lem7004315 A v u (@lem7004319 A v h1)). Qed.
Lemma lem7004321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7004322 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A v) : (term171 A v u) = (and True).
Proof. exact (MK_COMB (@lem7004321) (@lem7004320 A u v h1)). Qed.
Lemma lem7004323 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term193 A v u) = (term193 A v u).
Proof. exact (eq_refl (term193 A v u)). Qed.
Lemma lem7004324 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A v) : (term194 A v u) = (term195 A v u).
Proof. exact (MK_COMB (@lem7004322 A u v h1) (@lem7004323 A v u)). Qed.
Lemma lem7004326 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7004327 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term195 A v u) = (term193 A v u).
Proof. exact (@lem7004326 (term193 A v u)). Qed.
Lemma lem7004328 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A v) : (term194 A v u) = (term193 A v u).
Proof. exact (TRANS (@lem7004324 A u v h1) (@lem7004327 A v u)). Qed.
Lemma lem7004329 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term188 A v u) = (term195 A v u).
Proof. exact (MK_COMB (@lem7004309 A u v h1 h2) (@lem7004328 A u v h2)). Qed.
Lemma lem7004331 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7004332 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term195 A v u) = (term193 A v u).
Proof. exact (@lem7004331 (term193 A v u)). Qed.
Lemma lem7004333 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term188 A v u) = (term193 A v u).
Proof. exact (TRANS (@lem7004329 A u v h1 h2) (@lem7004332 A v u)). Qed.
Lemma lem7004334 {A : Type'} (f : A -> nat) (v : A -> Prop) (u : A -> Prop) (q' : Prop) : term196 A f v u q'.
Proof. exact (@lem7004285 A v u f (term193 A v u) q'). Qed.
Lemma lem7004335 {A : Type'} (f : A -> nat) (q' : Prop) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term197 A f v u q'.
Proof. exact (@lem7004334 A f v u q' (@lem7004333 A u v h1 h2)). Qed.
Lemma lem7004341 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((@nsum A v f) = (term132 A v u f)) = ((@nsum A v f) = (term132 A v u f)).
Proof. exact (eq_refl ((@nsum A v f) = (term132 A v u f))). Qed.
Lemma lem7004342 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term198 A v u f.
Proof. exact (fun h0 : term193 A v u => @lem7004341 A v u f). Qed.
Lemma lem7004343 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term199 A v u f.
Proof. exact (@lem7004335 A f ((@nsum A v f) = (term132 A v u f)) u v h1 h2). Qed.
Lemma lem7004344 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term134 A v u f) = (term200 A v u f).
Proof. exact (@lem7004343 A f u v h1 h2 (@lem7004342 A v u f)). Qed.
Lemma lem7004372 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (q' : Prop) : term201 A v u f q'.
Proof. exact (@lem7004272 A u v f (term200 A v u f) q'). Qed.
Lemma lem7004373 {A : Type'} (f : A -> nat) (q' : Prop) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term202 A v u f q'.
Proof. exact (@lem7004372 A v u f q' (@lem7004344 A f u v h1 h2)). Qed.
Lemma lem7004390 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term137 A u v f) = (term137 A u v f).
Proof. exact (eq_refl (term137 A u v f)). Qed.
Lemma lem7004391 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term203 A u v f.
Proof. exact (fun h0 : term200 A v u f => @lem7004390 A u v f). Qed.
Lemma lem7004392 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term204 A u v f.
Proof. exact (@lem7004373 A f (term137 A u v f) u v h1 h2). Qed.
Lemma lem7004393 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term139 A u v f) = (term205 A u v f).
Proof. exact (@lem7004392 A f u v h1 h2 (@lem7004391 A u v f)). Qed.
Lemma lem7004488 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term206 A u v f.
Proof. exact (fun h0 : term179 A u v f => @lem7004393 A f u v h1 h2). Qed.
Lemma lem7004489 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term207 A u v f.
Proof. exact (@lem7004251 A f (term205 A u v f) u v h1 h2). Qed.
Lemma lem7004490 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term141 A u v f) = (term208 A u v f).
Proof. exact (@lem7004489 A f u v h1 h2 (@lem7004488 A f u v h1 h2)). Qed.
Lemma lem7004753 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term208 A u v f) = (term141 A u v f).
Proof. exact (SYM (@lem7004490 A f u v h1 h2)). Qed.
Lemma lem7004755 (p : Prop) (q : Prop) (r : Prop) : term209 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem7004756 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term210 A u v f.
Proof. exact (@lem7004755 (term172 A u v) ((@nsum A u f) = (term124 A u v f)) (term205 A u v f)). Qed.
Lemma lem7004758 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem7004759 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem7004758 A s t). Qed.
Lemma lem7004760 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term172 A u v) = ((term211 A u v) = (@EMPTY A)).
Proof. exact (@lem7004759 A (@INTER A u v) (@DIFF A u v)). Qed.
Lemma lem7004764 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7004765 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem7004764 A s t). Qed.
Lemma lem7004766 {A : Type'} (u : A -> Prop) (v : A -> Prop) : ((term211 A u v) = (@EMPTY A)) = (term212 A u v).
Proof. exact (@lem7004765 A (term211 A u v) (@EMPTY A)). Qed.
Lemma lem7004771 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term172 A u v) = (term212 A u v).
Proof. exact (TRANS (@lem7004760 A u v) (@lem7004766 A u v)). Qed.
Lemma lem7004776 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term212 A u v) = (term172 A u v).
Proof. exact (SYM (@lem7004771 A u v)). Qed.
Lemma lem7004784 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem7004785 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (@lem7004784 A s x t). Qed.
Lemma lem7004786 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) : (term213 A x u v) = (term214 A x u v).
Proof. exact (@lem7004785 A (@INTER A u v) x (@DIFF A u v)). Qed.
Lemma lem7004790 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem7004791 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (@lem7004790 A s x t). Qed.
Lemma lem7004792 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term7 A x u v) = (term8 A u x v).
Proof. exact (@lem7004791 A u x v). Qed.
Lemma lem7004796 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7004797 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7004796 A P x). Qed.
Lemma lem7004798 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem7004797 A u x). Qed.
Lemma lem7004799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7004800 {A : Type'} (u : A -> Prop) (x : A) : (term9 A x u) = (term10 A u x).
Proof. exact (MK_COMB (@lem7004799) (@lem7004798 A u x)). Qed.
Lemma lem7004802 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7004803 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7004802 A P x). Qed.
Lemma lem7004804 {A : Type'} (v : A -> Prop) (x : A) : (@IN A x v) = (v x).
Proof. exact (@lem7004803 A v x). Qed.
Lemma lem7004805 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term8 A u x v) = (term11 A u v x).
Proof. exact (MK_COMB (@lem7004800 A u x) (@lem7004804 A v x)). Qed.
Lemma lem7004808 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term7 A x u v) = (term11 A u v x).
Proof. exact (TRANS (@lem7004792 A u x v) (@lem7004805 A u v x)). Qed.
Lemma lem7004809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7004810 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term215 A x u v) = (term216 A u v x).
Proof. exact (MK_COMB (@lem7004809) (@lem7004808 A u v x)). Qed.
Lemma lem7004812 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem7004813 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (@lem7004812 A s x t). Qed.
Lemma lem7004814 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term14 A x u v) = (term15 A u x v).
Proof. exact (@lem7004813 A u x v). Qed.
Lemma lem7004818 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7004819 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7004818 A P x). Qed.
Lemma lem7004820 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem7004819 A u x). Qed.
Lemma lem7004821 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7004822 {A : Type'} (u : A -> Prop) (x : A) : (term9 A x u) = (term10 A u x).
Proof. exact (MK_COMB (@lem7004821) (@lem7004820 A u x)). Qed.
Lemma lem7004824 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7004825 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7004824 A P x). Qed.
Lemma lem7004826 {A : Type'} (v : A -> Prop) (x : A) : (@IN A x v) = (v x).
Proof. exact (@lem7004825 A v x). Qed.
Lemma lem7004827 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7004828 {A : Type'} (v : A -> Prop) (x : A) : (term16 A x v) = (term17 A v x).
Proof. exact (MK_COMB (@lem7004827) (@lem7004826 A v x)). Qed.
Lemma lem7004829 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term15 A u x v) = (term18 A u v x).
Proof. exact (MK_COMB (@lem7004822 A u x) (@lem7004828 A v x)). Qed.
Lemma lem7004832 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term14 A x u v) = (term18 A u v x).
Proof. exact (TRANS (@lem7004814 A u x v) (@lem7004829 A u v x)). Qed.
Lemma lem7004833 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term214 A x u v) = (term217 A u v x).
Proof. exact (MK_COMB (@lem7004810 A u v x) (@lem7004832 A u v x)). Qed.
Lemma lem7004836 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term213 A x u v) = (term217 A u v x).
Proof. exact (TRANS (@lem7004786 A x u v) (@lem7004833 A u v x)). Qed.
Lemma lem7004837 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7004838 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term218 A x u v) = (term219 A u v x).
Proof. exact (MK_COMB (@lem7004837) (@lem7004836 A u v x)). Qed.
Lemma lem7004840 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem7004841 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem7004840 A x). Qed.
Lemma lem7004842 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : ((term213 A x u v) = (@IN A x (@EMPTY A))) = ((term217 A u v x) = False).
Proof. exact (MK_COMB (@lem7004838 A u v x) (@lem7004841 A x)). Qed.
Lemma lem7004844 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem7004845 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : ((term217 A u v x) = False) = (term220 A u v x).
Proof. exact (@lem7004844 (term217 A u v x)). Qed.
Lemma lem7004852 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : ((term213 A x u v) = (@IN A x (@EMPTY A))) = (term220 A u v x).
Proof. exact (TRANS (@lem7004842 A u v x) (@lem7004845 A u v x)). Qed.
Lemma lem7004853 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term221 A u v) = (term222 A u v).
Proof. exact (fun_ext (fun x : A => @lem7004852 A u v x)). Qed.
Lemma lem7004854 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7004855 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term212 A u v) = (term223 A u v).
Proof. exact (MK_COMB (@lem7004854 A) (@lem7004853 A u v)). Qed.
Lemma lem7004860 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term223 A u v) = (term212 A u v).
Proof. exact (SYM (@lem7004855 A u v)). Qed.
Lemma lem7004862 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7004863 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term223 A u v) = (term224 A u v).
Proof. exact (@lem7004862 (term223 A u v)). Qed.
Lemma lem7004864 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term224 A u v) = (term223 A u v).
Proof. exact (SYM (@lem7004863 A u v)). Qed.
Lemma lem7004865 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term225 A u v) : term225 A u v.
Proof. exact (h1). Qed.
Lemma lem7004868 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term224 A u v) : term224 A u v.
Proof. exact (h1). Qed.
Lemma lem7004869 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term226 A u v.
Proof. exact (fun h0 : term224 A u v => @lem7004868 A u v h0). Qed.
Lemma lem7004870 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term226 A u v) : term226 A u v.
Proof. exact (h1). Qed.
Lemma lem7004871 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term224 A u v) : term224 A u v.
Proof. exact (h1). Qed.
Lemma lem7004872 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term224 A u v) (h2 : term226 A u v) : term224 A u v.
Proof. exact (@lem7004870 A u v h2 (@lem7004871 A u v h1)). Qed.
Lemma lem7004873 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term224 A u v) : term227 A u v.
Proof. exact (fun h0 : term226 A u v => @lem7004872 A u v h1 h0). Qed.
Lemma lem7004874 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term226 A u v) : term226 A u v.
Proof. exact (h1). Qed.
Lemma lem7004875 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term224 A u v) (h2 : term226 A u v) : term224 A u v.
Proof. exact (@lem7004873 A u v h1 (@lem7004874 A u v h2)). Qed.
Lemma lem7004876 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term226 A u v) : term226 A u v.
Proof. exact (fun h0 : term224 A u v => @lem7004875 A u v h0 h1). Qed.
Lemma lem7004877 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term228 A u v.
Proof. exact (fun h0 : term226 A u v => @lem7004876 A u v h0). Qed.
Lemma lem7004880 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term226 A u v.
Proof. exact (@lem7004877 A u v (@lem7004869 A u v)). Qed.
Lemma lem7004881 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term226 A u v.
Proof. exact (@lem7004880 A u v). Qed.
Lemma lem7004891 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7004892 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term224 A u v) = (term229 A u v).
Proof. exact (@lem7004891 (term225 A u v)). Qed.
Lemma lem7004894 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7004895 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term229 A u v) = (term223 A u v).
Proof. exact (@lem7004894 (term223 A u v)). Qed.
Lemma lem7004900 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term224 A u v) = (term223 A u v).
Proof. exact (TRANS (@lem7004892 A u v) (@lem7004895 A u v)). Qed.
Lemma lem7004907 {A : Type'} (v : A -> Prop) : (term230 A v) = (term231 A v).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7004900 A u v)). Qed.
Lemma lem7004908 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7004909 {A : Type'} (v : A -> Prop) : (term232 A v) = (term233 A v).
Proof. exact (MK_COMB (@lem7004908 A) (@lem7004907 A v)). Qed.
Lemma lem7004914 {A : Type'} : (term234 A) = (term235 A).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7004909 A v)). Qed.
Lemma lem7004915 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7004924 {A : Type'} : (term236 A) = (term237 A).
Proof. exact (MK_COMB (@lem7004915 A) (@lem7004914 A)). Qed.
Lemma lem7004941 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term220 A u v x) = (term220 A u v x).
Proof. exact (eq_refl (term220 A u v x)). Qed.
Lemma lem7004942 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term222 A u v) = (term222 A u v).
Proof. exact (fun_ext (fun x : A => @lem7004941 A u v x)). Qed.
Lemma lem7004943 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7004944 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term223 A u v) = (term223 A u v).
Proof. exact (MK_COMB (@lem7004943 A) (@lem7004942 A u v)). Qed.
Lemma lem7004945 {A : Type'} (v : A -> Prop) : (term231 A v) = (term231 A v).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7004944 A u v)). Qed.
Lemma lem7004946 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7004947 {A : Type'} (v : A -> Prop) : (term233 A v) = (term233 A v).
Proof. exact (MK_COMB (@lem7004946 A) (@lem7004945 A v)). Qed.
Lemma lem7004948 {A : Type'} : (term235 A) = (term235 A).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7004947 A v)). Qed.
Lemma lem7004949 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7004950 {A : Type'} : (term237 A) = (term237 A).
Proof. exact (MK_COMB (@lem7004949 A) (@lem7004948 A)). Qed.
Lemma lem7004977 {A : Type'} : (term236 A) = (term237 A).
Proof. exact (TRANS (@lem7004924 A) (@lem7004950 A)). Qed.
Lemma lem7004978 {A : Type'} : (term237 A) = (term236 A).
Proof. exact (SYM (@lem7004977 A)). Qed.
Lemma lem7004997 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : term217 A u v x.
Proof. exact (h1). Qed.
Lemma lem7005021 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : term217 A u v x.
Proof. exact (h1). Qed.
Lemma lem7005022 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : term18 A u v x.
Proof. exact (proj2 (@lem7005021 A u v x h1)). Qed.
Lemma lem7005023 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : term11 A u v x.
Proof. exact (proj1 (@lem7005021 A u v x h1)). Qed.
Lemma lem7005047 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : term17 A v x.
Proof. exact (proj2 (@lem7005022 A u v x h1)). Qed.
Lemma lem7005053 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : v x.
Proof. exact (proj2 (@lem7005023 A u v x h1)). Qed.
Lemma lem7005054 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : term63 A v x.
Proof. exact (fun h0 : term17 A v x => @lem7005053 A u v x h1). Qed.
Lemma lem7005056 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7005057 {A : Type'} (v : A -> Prop) (x : A) : (term63 A v x) = (v x).
Proof. exact (@lem7005056 (v x)). Qed.
Lemma lem7005058 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : v x.
Proof. exact (EQ_MP (@lem7005057 A v x) (@lem7005054 A u v x h1)). Qed.
Lemma lem7005061 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7005063 {A : Type'} (v : A -> Prop) (x : A) : (term17 A v x) = (term65 A v x).
Proof. exact (@lem7005061 (v x)). Qed.
Lemma lem7005066 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : term65 A v x.
Proof. exact (EQ_MP (@lem7005063 A v x) (@lem7005047 A u v x h1)). Qed.
Lemma lem7005069 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : False.
Proof. exact (@lem7005066 A u v x h1 (@lem7005058 A u v x h1)). Qed.
Lemma lem7005070 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : term66.
Proof. exact (fun h0 : ~ False => @lem7005069 A u v x h1). Qed.
Lemma lem7005072 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7005073 : term66 = False.
Proof. exact (@lem7005072 False). Qed.
Lemma lem7005074 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : False.
Proof. exact (EQ_MP (@lem7005073) (@lem7005070 A u v x h1)). Qed.
Lemma lem7005075 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : (term217 A u v x) = False.
Proof. exact (prop_ext (fun h2 : term217 A u v x => @lem7005074 A u v x h1) (fun h2 : False => @lem7005021 A u v x h1)). Qed.
Lemma lem7005076 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : False.
Proof. exact (EQ_MP (@lem7005075 A u v x h1) (@lem7005021 A u v x h1)). Qed.
Lemma lem7005077 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : (term217 A u v x) = False.
Proof. exact (prop_ext (fun h2 : term217 A u v x => @lem7005076 A u v x h1) (fun h2 : False => @lem7004997 A u v x h1)). Qed.
Lemma lem7005078 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term217 A u v x) : False.
Proof. exact (EQ_MP (@lem7005077 A u v x h1) (@lem7004997 A u v x h1)). Qed.
Lemma lem7005079 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : term238 A u v x.
Proof. exact (fun h0 : term217 A u v x => @lem7005078 A u v x h0). Qed.
Lemma lem7005080 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term238 A u v x) = (term220 A u v x).
Proof. exact (@lem69 (term217 A u v x)). Qed.
Lemma lem7005081 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : term220 A u v x.
Proof. exact (EQ_MP (@lem7005080 A u v x) (@lem7005079 A u v x)). Qed.
Lemma lem7005086 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term223 A u v.
Proof. exact (fun x : A => @lem7005081 A u v x). Qed.
Lemma lem7005091 {A : Type'} (v : A -> Prop) : term233 A v.
Proof. exact (fun u : A -> Prop => @lem7005086 A u v). Qed.
Lemma lem7005096 {A : Type'} : term237 A.
Proof. exact (fun v : A -> Prop => @lem7005091 A v). Qed.
Lemma lem7005097 {A : Type'} : term236 A.
Proof. exact (EQ_MP (@lem7004978 A) (@lem7005096 A)). Qed.
Lemma lem7005098 {A : Type'} (v : A -> Prop) : term239 A v.
Proof. exact (@lem7005097 A v). Qed.
Lemma lem7005099 {A : Type'} (v : A -> Prop) : (term239 A v) = (term232 A v).
Proof. exact (eq_refl (term239 A v)). Qed.
Lemma lem7005100 {A : Type'} (v : A -> Prop) : term232 A v.
Proof. exact (EQ_MP (@lem7005099 A v) (@lem7005098 A v)). Qed.
Lemma lem7005101 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term240 A v u.
Proof. exact (@lem7005100 A v u). Qed.
Lemma lem7005102 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term240 A v u) = (term224 A u v).
Proof. exact (eq_refl (term240 A v u)). Qed.
Lemma lem7005103 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term224 A u v.
Proof. exact (EQ_MP (@lem7005102 A u v) (@lem7005101 A v u)). Qed.
Lemma lem7005105 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term224 A u v.
Proof. exact (@lem7004881 A u v (@lem7005103 A u v)). Qed.
Lemma lem7005106 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term225 A u v) : False.
Proof. exact (@lem7005105 A u v (@lem7004865 A u v h1)). Qed.
Lemma lem7005107 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term225 A u v) : (term225 A u v) = False.
Proof. exact (prop_ext (fun h2 : term225 A u v => @lem7005106 A u v h1) (fun h2 : False => @lem7004865 A u v h1)). Qed.
Lemma lem7005108 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term225 A u v) : False.
Proof. exact (EQ_MP (@lem7005107 A u v h1) (@lem7004865 A u v h1)). Qed.
Lemma lem7005109 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term224 A u v.
Proof. exact (fun h0 : term225 A u v => @lem7005108 A u v h0). Qed.
Lemma lem7005110 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term223 A u v.
Proof. exact (EQ_MP (@lem7004864 A u v) (@lem7005109 A u v)). Qed.
Lemma lem7005111 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term212 A u v.
Proof. exact (EQ_MP (@lem7004860 A u v) (@lem7005110 A u v)). Qed.
Lemma lem7005112 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term172 A u v.
Proof. exact (EQ_MP (@lem7004776 A u v) (@lem7005111 A u v)). Qed.
Lemma lem7005113 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : (@nsum A u f) = (term124 A u v f)) : (@nsum A u f) = (term124 A u v f).
Proof. exact (h1). Qed.
Lemma lem7005114 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term241 A u v f) = (term241 A u v f).
Proof. exact (eq_refl (term241 A u v f)). Qed.
Lemma lem7005115 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : (@nsum A u f) = (term124 A u v f)) : (term242 A v u f) = (term243 A u v f).
Proof. exact (MK_COMB (@lem7005114 A u v f) (@lem7005113 A u v f h1)). Qed.
Lemma lem7005116 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term243 A u v f) = (term244 A u v f).
Proof. exact (eq_refl (term243 A u v f)). Qed.
Lemma lem7005117 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term245 A v u f) = (term245 A v u f).
Proof. exact (eq_refl (term245 A v u f)). Qed.
Lemma lem7005118 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : ((term242 A v u f) = (term243 A u v f)) = ((term242 A v u f) = (term244 A u v f)).
Proof. exact (MK_COMB (@lem7005117 A v u f) (@lem7005116 A u v f)). Qed.
Lemma lem7005119 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term242 A v u f) = (term205 A u v f).
Proof. exact (eq_refl (term242 A v u f)). Qed.
Lemma lem7005120 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7005121 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term245 A v u f) = (term246 A u v f).
Proof. exact (MK_COMB (@lem7005120) (@lem7005119 A u v f)). Qed.
Lemma lem7005122 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term244 A u v f) = (term244 A u v f).
Proof. exact (eq_refl (term244 A u v f)). Qed.
Lemma lem7005123 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : ((term242 A v u f) = (term244 A u v f)) = ((term205 A u v f) = (term244 A u v f)).
Proof. exact (MK_COMB (@lem7005121 A u v f) (@lem7005122 A u v f)). Qed.
Lemma lem7005124 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : ((term242 A v u f) = (term243 A u v f)) = ((term205 A u v f) = (term244 A u v f)).
Proof. exact (TRANS (@lem7005118 A u v f) (@lem7005123 A u v f)). Qed.
Lemma lem7005125 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : (@nsum A u f) = (term124 A u v f)) : (term205 A u v f) = (term244 A u v f).
Proof. exact (EQ_MP (@lem7005124 A u v f) (@lem7005115 A u v f h1)). Qed.
Lemma lem7005126 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : (@nsum A u f) = (term124 A u v f)) : (term244 A u v f) = (term205 A u v f).
Proof. exact (SYM (@lem7005125 A u v f h1)). Qed.
Lemma lem7005128 (p : Prop) (q : Prop) (r : Prop) : term209 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem7005129 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term247 A u v f.
Proof. exact (@lem7005128 (term193 A v u) ((@nsum A v f) = (term132 A v u f)) (term248 A u v f)). Qed.
Lemma lem7005131 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem7005132 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem7005131 A s t). Qed.
Lemma lem7005133 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term193 A v u) = ((term249 A v u) = (@EMPTY A)).
Proof. exact (@lem7005132 A (@INTER A u v) (@DIFF A v u)). Qed.
Lemma lem7005137 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7005138 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem7005137 A s t). Qed.
Lemma lem7005139 {A : Type'} (v : A -> Prop) (u : A -> Prop) : ((term249 A v u) = (@EMPTY A)) = (term250 A v u).
Proof. exact (@lem7005138 A (term249 A v u) (@EMPTY A)). Qed.
Lemma lem7005144 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term193 A v u) = (term250 A v u).
Proof. exact (TRANS (@lem7005133 A v u) (@lem7005139 A v u)). Qed.
Lemma lem7005149 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term250 A v u) = (term193 A v u).
Proof. exact (SYM (@lem7005144 A v u)). Qed.
Lemma lem7005157 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem7005158 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (@lem7005157 A s x t). Qed.
Lemma lem7005159 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) : (term251 A x v u) = (term252 A x v u).
Proof. exact (@lem7005158 A (@INTER A u v) x (@DIFF A v u)). Qed.
Lemma lem7005163 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem7005164 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (@lem7005163 A s x t). Qed.
Lemma lem7005165 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term7 A x u v) = (term8 A u x v).
Proof. exact (@lem7005164 A u x v). Qed.
Lemma lem7005169 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7005170 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7005169 A P x). Qed.
Lemma lem7005171 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem7005170 A u x). Qed.
Lemma lem7005172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7005173 {A : Type'} (u : A -> Prop) (x : A) : (term9 A x u) = (term10 A u x).
Proof. exact (MK_COMB (@lem7005172) (@lem7005171 A u x)). Qed.
Lemma lem7005175 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7005176 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7005175 A P x). Qed.
Lemma lem7005177 {A : Type'} (v : A -> Prop) (x : A) : (@IN A x v) = (v x).
Proof. exact (@lem7005176 A v x). Qed.
Lemma lem7005178 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term8 A u x v) = (term11 A u v x).
Proof. exact (MK_COMB (@lem7005173 A u x) (@lem7005177 A v x)). Qed.
Lemma lem7005181 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term7 A x u v) = (term11 A u v x).
Proof. exact (TRANS (@lem7005165 A u x v) (@lem7005178 A u v x)). Qed.
Lemma lem7005182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7005183 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term215 A x u v) = (term216 A u v x).
Proof. exact (MK_COMB (@lem7005182) (@lem7005181 A u v x)). Qed.
Lemma lem7005185 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem7005186 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (@lem7005185 A s x t). Qed.
Lemma lem7005187 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term14 A x v u) = (term15 A v x u).
Proof. exact (@lem7005186 A v x u). Qed.
Lemma lem7005191 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7005192 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7005191 A P x). Qed.
Lemma lem7005193 {A : Type'} (v : A -> Prop) (x : A) : (@IN A x v) = (v x).
Proof. exact (@lem7005192 A v x). Qed.
Lemma lem7005194 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7005195 {A : Type'} (v : A -> Prop) (x : A) : (term9 A x v) = (term10 A v x).
Proof. exact (MK_COMB (@lem7005194) (@lem7005193 A v x)). Qed.
Lemma lem7005197 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7005198 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7005197 A P x). Qed.
Lemma lem7005199 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem7005198 A u x). Qed.
Lemma lem7005200 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7005201 {A : Type'} (u : A -> Prop) (x : A) : (term16 A x u) = (term17 A u x).
Proof. exact (MK_COMB (@lem7005200) (@lem7005199 A u x)). Qed.
Lemma lem7005202 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : (term15 A v x u) = (term18 A v u x).
Proof. exact (MK_COMB (@lem7005195 A v x) (@lem7005201 A u x)). Qed.
Lemma lem7005205 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : (term14 A x v u) = (term18 A v u x).
Proof. exact (TRANS (@lem7005187 A v x u) (@lem7005202 A v u x)). Qed.
Lemma lem7005206 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : (term252 A x v u) = (term253 A v u x).
Proof. exact (MK_COMB (@lem7005183 A u v x) (@lem7005205 A v u x)). Qed.
Lemma lem7005209 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : (term251 A x v u) = (term253 A v u x).
Proof. exact (TRANS (@lem7005159 A x v u) (@lem7005206 A v u x)). Qed.
Lemma lem7005210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7005211 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : (term254 A x v u) = (term255 A v u x).
Proof. exact (MK_COMB (@lem7005210) (@lem7005209 A v u x)). Qed.
Lemma lem7005213 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem7005214 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem7005213 A x). Qed.
Lemma lem7005215 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : ((term251 A x v u) = (@IN A x (@EMPTY A))) = ((term253 A v u x) = False).
Proof. exact (MK_COMB (@lem7005211 A v u x) (@lem7005214 A x)). Qed.
Lemma lem7005217 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem7005218 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : ((term253 A v u x) = False) = (term256 A v u x).
Proof. exact (@lem7005217 (term253 A v u x)). Qed.
Lemma lem7005225 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : ((term251 A x v u) = (@IN A x (@EMPTY A))) = (term256 A v u x).
Proof. exact (TRANS (@lem7005215 A v u x) (@lem7005218 A v u x)). Qed.
Lemma lem7005226 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term257 A v u) = (term258 A v u).
Proof. exact (fun_ext (fun x : A => @lem7005225 A v u x)). Qed.
Lemma lem7005227 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7005228 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term250 A v u) = (term259 A v u).
Proof. exact (MK_COMB (@lem7005227 A) (@lem7005226 A v u)). Qed.
Lemma lem7005233 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term259 A v u) = (term250 A v u).
Proof. exact (SYM (@lem7005228 A v u)). Qed.
Lemma lem7005235 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7005236 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term259 A v u) = (term260 A v u).
Proof. exact (@lem7005235 (term259 A v u)). Qed.
Lemma lem7005237 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term260 A v u) = (term259 A v u).
Proof. exact (SYM (@lem7005236 A v u)). Qed.
Lemma lem7005238 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term261 A v u) : term261 A v u.
Proof. exact (h1). Qed.
Lemma lem7005241 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term260 A v u) : term260 A v u.
Proof. exact (h1). Qed.
Lemma lem7005242 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term262 A v u.
Proof. exact (fun h0 : term260 A v u => @lem7005241 A v u h0). Qed.
Lemma lem7005243 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term262 A v u) : term262 A v u.
Proof. exact (h1). Qed.
Lemma lem7005244 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term260 A v u) : term260 A v u.
Proof. exact (h1). Qed.
Lemma lem7005245 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term260 A v u) (h2 : term262 A v u) : term260 A v u.
Proof. exact (@lem7005243 A v u h2 (@lem7005244 A v u h1)). Qed.
Lemma lem7005246 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term260 A v u) : term263 A v u.
Proof. exact (fun h0 : term262 A v u => @lem7005245 A v u h1 h0). Qed.
Lemma lem7005247 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term262 A v u) : term262 A v u.
Proof. exact (h1). Qed.
Lemma lem7005248 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term260 A v u) (h2 : term262 A v u) : term260 A v u.
Proof. exact (@lem7005246 A v u h1 (@lem7005247 A v u h2)). Qed.
Lemma lem7005249 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term262 A v u) : term262 A v u.
Proof. exact (fun h0 : term260 A v u => @lem7005248 A v u h0 h1). Qed.
Lemma lem7005250 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term264 A v u.
Proof. exact (fun h0 : term262 A v u => @lem7005249 A v u h0). Qed.
Lemma lem7005253 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term262 A v u.
Proof. exact (@lem7005250 A v u (@lem7005242 A v u)). Qed.
Lemma lem7005254 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term262 A v u.
Proof. exact (@lem7005253 A v u). Qed.
Lemma lem7005264 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7005265 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term260 A v u) = (term265 A v u).
Proof. exact (@lem7005264 (term261 A v u)). Qed.
Lemma lem7005267 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7005268 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term265 A v u) = (term259 A v u).
Proof. exact (@lem7005267 (term259 A v u)). Qed.
Lemma lem7005273 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term260 A v u) = (term259 A v u).
Proof. exact (TRANS (@lem7005265 A v u) (@lem7005268 A v u)). Qed.
Lemma lem7005280 {A : Type'} (u : A -> Prop) : (term266 A u) = (term267 A u).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7005273 A v u)). Qed.
Lemma lem7005281 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7005282 {A : Type'} (u : A -> Prop) : (term268 A u) = (term269 A u).
Proof. exact (MK_COMB (@lem7005281 A) (@lem7005280 A u)). Qed.
Lemma lem7005287 {A : Type'} : (term270 A) = (term271 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7005282 A u)). Qed.
Lemma lem7005288 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7005297 {A : Type'} : (term272 A) = (term273 A).
Proof. exact (MK_COMB (@lem7005288 A) (@lem7005287 A)). Qed.
Lemma lem7005314 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : (term256 A v u x) = (term256 A v u x).
Proof. exact (eq_refl (term256 A v u x)). Qed.
Lemma lem7005315 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term258 A v u) = (term258 A v u).
Proof. exact (fun_ext (fun x : A => @lem7005314 A v u x)). Qed.
Lemma lem7005316 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7005317 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term259 A v u) = (term259 A v u).
Proof. exact (MK_COMB (@lem7005316 A) (@lem7005315 A v u)). Qed.
Lemma lem7005318 {A : Type'} (u : A -> Prop) : (term267 A u) = (term267 A u).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7005317 A v u)). Qed.
Lemma lem7005319 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7005320 {A : Type'} (u : A -> Prop) : (term269 A u) = (term269 A u).
Proof. exact (MK_COMB (@lem7005319 A) (@lem7005318 A u)). Qed.
Lemma lem7005321 {A : Type'} : (term271 A) = (term271 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7005320 A u)). Qed.
Lemma lem7005322 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7005323 {A : Type'} : (term273 A) = (term273 A).
Proof. exact (MK_COMB (@lem7005322 A) (@lem7005321 A)). Qed.
Lemma lem7005350 {A : Type'} : (term272 A) = (term273 A).
Proof. exact (TRANS (@lem7005297 A) (@lem7005323 A)). Qed.
Lemma lem7005351 {A : Type'} : (term273 A) = (term272 A).
Proof. exact (SYM (@lem7005350 A)). Qed.
Lemma lem7005370 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : term253 A v u x.
Proof. exact (h1). Qed.
Lemma lem7005394 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : term253 A v u x.
Proof. exact (h1). Qed.
Lemma lem7005395 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : term18 A v u x.
Proof. exact (proj2 (@lem7005394 A v u x h1)). Qed.
Lemma lem7005396 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : term11 A u v x.
Proof. exact (proj1 (@lem7005394 A v u x h1)). Qed.
Lemma lem7005420 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : term17 A u x.
Proof. exact (proj2 (@lem7005395 A v u x h1)). Qed.
Lemma lem7005426 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : u x.
Proof. exact (proj1 (@lem7005396 A v u x h1)). Qed.
Lemma lem7005427 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : term63 A u x.
Proof. exact (fun h0 : term17 A u x => @lem7005426 A v u x h1). Qed.
Lemma lem7005429 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7005430 {A : Type'} (u : A -> Prop) (x : A) : (term63 A u x) = (u x).
Proof. exact (@lem7005429 (u x)). Qed.
Lemma lem7005431 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : u x.
Proof. exact (EQ_MP (@lem7005430 A u x) (@lem7005427 A v u x h1)). Qed.
Lemma lem7005434 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7005436 {A : Type'} (u : A -> Prop) (x : A) : (term17 A u x) = (term65 A u x).
Proof. exact (@lem7005434 (u x)). Qed.
Lemma lem7005439 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : term65 A u x.
Proof. exact (EQ_MP (@lem7005436 A u x) (@lem7005420 A v u x h1)). Qed.
Lemma lem7005442 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : False.
Proof. exact (@lem7005439 A v u x h1 (@lem7005431 A v u x h1)). Qed.
Lemma lem7005443 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem7005442 A v u x h1). Qed.
Lemma lem7005445 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7005446 : term66 = False.
Proof. exact (@lem7005445 False). Qed.
Lemma lem7005447 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : False.
Proof. exact (EQ_MP (@lem7005446) (@lem7005443 A v u x h1)). Qed.
Lemma lem7005448 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : (term253 A v u x) = False.
Proof. exact (prop_ext (fun h2 : term253 A v u x => @lem7005447 A v u x h1) (fun h2 : False => @lem7005394 A v u x h1)). Qed.
Lemma lem7005449 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : False.
Proof. exact (EQ_MP (@lem7005448 A v u x h1) (@lem7005394 A v u x h1)). Qed.
Lemma lem7005450 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : (term253 A v u x) = False.
Proof. exact (prop_ext (fun h2 : term253 A v u x => @lem7005449 A v u x h1) (fun h2 : False => @lem7005370 A v u x h1)). Qed.
Lemma lem7005451 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term253 A v u x) : False.
Proof. exact (EQ_MP (@lem7005450 A v u x h1) (@lem7005370 A v u x h1)). Qed.
Lemma lem7005452 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : term274 A v u x.
Proof. exact (fun h0 : term253 A v u x => @lem7005451 A v u x h0). Qed.
Lemma lem7005453 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : (term274 A v u x) = (term256 A v u x).
Proof. exact (@lem69 (term253 A v u x)). Qed.
Lemma lem7005454 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : term256 A v u x.
Proof. exact (EQ_MP (@lem7005453 A v u x) (@lem7005452 A v u x)). Qed.
Lemma lem7005459 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term259 A v u.
Proof. exact (fun x : A => @lem7005454 A v u x). Qed.
Lemma lem7005464 {A : Type'} (u : A -> Prop) : term269 A u.
Proof. exact (fun v : A -> Prop => @lem7005459 A v u). Qed.
Lemma lem7005469 {A : Type'} : term273 A.
Proof. exact (fun u : A -> Prop => @lem7005464 A u). Qed.
Lemma lem7005470 {A : Type'} : term272 A.
Proof. exact (EQ_MP (@lem7005351 A) (@lem7005469 A)). Qed.
Lemma lem7005471 {A : Type'} (u : A -> Prop) : term275 A u.
Proof. exact (@lem7005470 A u). Qed.
Lemma lem7005472 {A : Type'} (u : A -> Prop) : (term275 A u) = (term268 A u).
Proof. exact (eq_refl (term275 A u)). Qed.
Lemma lem7005473 {A : Type'} (u : A -> Prop) : term268 A u.
Proof. exact (EQ_MP (@lem7005472 A u) (@lem7005471 A u)). Qed.
Lemma lem7005474 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term276 A u v.
Proof. exact (@lem7005473 A u v). Qed.
Lemma lem7005475 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term276 A u v) = (term260 A v u).
Proof. exact (eq_refl (term276 A u v)). Qed.
Lemma lem7005476 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term260 A v u.
Proof. exact (EQ_MP (@lem7005475 A v u) (@lem7005474 A u v)). Qed.
Lemma lem7005478 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term260 A v u.
Proof. exact (@lem7005254 A v u (@lem7005476 A v u)). Qed.
Lemma lem7005479 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term261 A v u) : False.
Proof. exact (@lem7005478 A v u (@lem7005238 A v u h1)). Qed.
Lemma lem7005480 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term261 A v u) : (term261 A v u) = False.
Proof. exact (prop_ext (fun h2 : term261 A v u => @lem7005479 A v u h1) (fun h2 : False => @lem7005238 A v u h1)). Qed.
Lemma lem7005481 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term261 A v u) : False.
Proof. exact (EQ_MP (@lem7005480 A v u h1) (@lem7005238 A v u h1)). Qed.
Lemma lem7005482 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term260 A v u.
Proof. exact (fun h0 : term261 A v u => @lem7005481 A v u h0). Qed.
Lemma lem7005483 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term259 A v u.
Proof. exact (EQ_MP (@lem7005237 A v u) (@lem7005482 A v u)). Qed.
Lemma lem7005484 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term250 A v u.
Proof. exact (EQ_MP (@lem7005233 A v u) (@lem7005483 A v u)). Qed.
Lemma lem7005485 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term193 A v u.
Proof. exact (EQ_MP (@lem7005149 A v u) (@lem7005484 A v u)). Qed.
Lemma lem7005486 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : (@nsum A v f) = (term132 A v u f)) : (@nsum A v f) = (term132 A v u f).
Proof. exact (h1). Qed.
Lemma lem7005487 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term277 A u v f) = (term277 A u v f).
Proof. exact (eq_refl (term277 A u v f)). Qed.
Lemma lem7005488 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : (@nsum A v f) = (term132 A v u f)) : (term278 A u v f) = (term279 A v u f).
Proof. exact (MK_COMB (@lem7005487 A u v f) (@lem7005486 A v u f h1)). Qed.
Lemma lem7005489 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term279 A v u f) = (term280 A v u f).
Proof. exact (eq_refl (term279 A v u f)). Qed.
Lemma lem7005490 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term281 A u v f) = (term281 A u v f).
Proof. exact (eq_refl (term281 A u v f)). Qed.
Lemma lem7005491 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term278 A u v f) = (term279 A v u f)) = ((term278 A u v f) = (term280 A v u f)).
Proof. exact (MK_COMB (@lem7005490 A u v f) (@lem7005489 A v u f)). Qed.
Lemma lem7005492 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term278 A u v f) = (term248 A u v f).
Proof. exact (eq_refl (term278 A u v f)). Qed.
Lemma lem7005493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7005494 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term281 A u v f) = (term282 A u v f).
Proof. exact (MK_COMB (@lem7005493) (@lem7005492 A u v f)). Qed.
Lemma lem7005495 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term280 A v u f) = (term280 A v u f).
Proof. exact (eq_refl (term280 A v u f)). Qed.
Lemma lem7005496 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term278 A u v f) = (term280 A v u f)) = ((term248 A u v f) = (term280 A v u f)).
Proof. exact (MK_COMB (@lem7005494 A u v f) (@lem7005495 A v u f)). Qed.
Lemma lem7005497 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term278 A u v f) = (term279 A v u f)) = ((term248 A u v f) = (term280 A v u f)).
Proof. exact (TRANS (@lem7005491 A v u f) (@lem7005496 A v u f)). Qed.
Lemma lem7005498 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : (@nsum A v f) = (term132 A v u f)) : (term248 A u v f) = (term280 A v u f).
Proof. exact (EQ_MP (@lem7005497 A v u f) (@lem7005488 A v u f h1)). Qed.
Lemma lem7005499 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : (@nsum A v f) = (term132 A v u f)) : (term280 A v u f) = (term248 A u v f).
Proof. exact (SYM (@lem7005498 A v u f h1)). Qed.
Lemma lem7005502 {A : Type'} (f : A -> nat) : term283 A f.
Proof. exact (@lem6930973 A f). Qed.
Lemma lem7005503 {A : Type'} (f : A -> nat) : (term283 A f) = (term284 A f).
Proof. exact (eq_refl (term283 A f)). Qed.
Lemma lem7005504 {A : Type'} (f : A -> nat) : term284 A f.
Proof. exact (EQ_MP (@lem7005503 A f) (@lem7005502 A f)). Qed.
Lemma lem7005505 {A : Type'} (f : A -> nat) (s : A -> Prop) : term285 A f s.
Proof. exact (@lem7005504 A f s). Qed.
Lemma lem7005506 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term285 A f s) = (term286 A s f).
Proof. exact (eq_refl (term285 A f s)). Qed.
Lemma lem7005507 {A : Type'} (s : A -> Prop) (f : A -> nat) : term286 A s f.
Proof. exact (EQ_MP (@lem7005506 A s f) (@lem7005505 A f s)). Qed.
Lemma lem7005508 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term287 A s f) : term287 A s f.
Proof. exact (h1). Qed.
Lemma lem7005509 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term287 A s f) : (@nsum A s f) = (NUMERAL 0).
Proof. exact (@lem7005507 A s f (@lem7005508 A s f h1)). Qed.
Lemma lem7005519 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : term288 A u v f x.
Proof. exact (@lem7004017 A u v f h1 x). Qed.
Lemma lem7005520 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (x : A) : (term288 A u v f x) = (term289 A u v f x).
Proof. exact (eq_refl (term288 A u v f x)). Qed.
Lemma lem7005521 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : term289 A u v f x.
Proof. exact (EQ_MP (@lem7005520 A u v f x) (@lem7005519 A x u v f h1)). Qed.
Lemma lem7005522 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term14 A x u v) : term14 A x u v.
Proof. exact (h1). Qed.
Lemma lem7005523 {A : Type'} (f : A -> nat) (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term115 A u v f) (h2 : term14 A x u v) : (f x) = (NUMERAL 0).
Proof. exact (@lem7005521 A x u v f h1 (@lem7005522 A x u v h2)). Qed.
Lemma lem7005577 {A : Type'} (s : A -> Prop) (f : A -> nat) : term286 A s f.
Proof. exact (fun h0 : term287 A s f => @lem7005509 A s f h0). Qed.
Lemma lem7005578 {A : Type'} (s : A -> Prop) (f : A -> nat) : term286 A s f.
Proof. exact (@lem7005577 A s f). Qed.
Lemma lem7005579 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term290 A u v f.
Proof. exact (@lem7005578 A (@DIFF A u v) f). Qed.
Lemma lem7005587 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term153 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7005588 (p : Prop) (q : Prop) (p' : Prop) : term154 p q p'.
Proof. exact (fun q' : Prop => @lem7005587 p q p' q'). Qed.
Lemma lem7005589 (p : Prop) (q : Prop) : term155 p q.
Proof. exact (fun p' : Prop => @lem7005588 p q p'). Qed.
Lemma lem7005590 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (x : A) : term291 A u v f x.
Proof. exact (@lem7005589 (term14 A x u v) ((f x) = (NUMERAL 0))). Qed.
Lemma lem7005591 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term292 A u v f x p'.
Proof. exact (@lem7005590 A u v f x p'). Qed.
Lemma lem7005592 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) : (term292 A u v f x p') = (term293 A u v f x p').
Proof. exact (eq_refl (term292 A u v f x p')). Qed.
Lemma lem7005593 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term293 A u v f x p'.
Proof. exact (EQ_MP (@lem7005592 A u v f x p') (@lem7005591 A u v f x p')). Qed.
Lemma lem7005594 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term294 A u v f x p' q'.
Proof. exact (@lem7005593 A u v f x p' q'). Qed.
Lemma lem7005595 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : (term294 A u v f x p' q') = (term295 A u v f x p' q').
Proof. exact (eq_refl (term294 A u v f x p' q')). Qed.
Lemma lem7005596 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term295 A u v f x p' q'.
Proof. exact (EQ_MP (@lem7005595 A u v f x p' q') (@lem7005594 A u v f x p' q')). Qed.
Lemma lem7005597 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) : (term14 A x u v) = (term14 A x u v).
Proof. exact (eq_refl (term14 A x u v)). Qed.
Lemma lem7005598 {A : Type'} (f : A -> nat) (x : A) (u : A -> Prop) (v : A -> Prop) (q' : Prop) : term296 A f x u v q'.
Proof. exact (@lem7005596 A u v f x (term14 A x u v) q'). Qed.
Lemma lem7005599 {A : Type'} (f : A -> nat) (x : A) (u : A -> Prop) (v : A -> Prop) (q' : Prop) : term297 A f x u v q'.
Proof. exact (@lem7005598 A f x u v q' (@lem7005597 A x u v)). Qed.
Lemma lem7005600 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term14 A x u v) : term14 A x u v.
Proof. exact (h1). Qed.
Lemma lem7005601 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) : (term14 A x u v) = ((term14 A x u v) = True).
Proof. exact (@lem7 (term14 A x u v)). Qed.
Lemma lem7005606 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : term289 A u v f x.
Proof. exact (fun h0 : term14 A x u v => @lem7005523 A f x u v h1 h0). Qed.
Lemma lem7005607 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : term289 A u v f x.
Proof. exact (@lem7005606 A x u v f h1). Qed.
Lemma lem7005609 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term14 A x u v) : (term14 A x u v) = True.
Proof. exact (EQ_MP (@lem7005601 A x u v) (@lem7005600 A x u v h1)). Qed.
Lemma lem7005610 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term14 A x u v) : True = (term14 A x u v).
Proof. exact (SYM (@lem7005609 A x u v h1)). Qed.
Lemma lem7005611 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term14 A x u v) : term14 A x u v.
Proof. exact (EQ_MP (@lem7005610 A x u v h1) (@lem0)). Qed.
Lemma lem7005612 {A : Type'} (f : A -> nat) (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term115 A u v f) (h2 : term14 A x u v) : (f x) = (NUMERAL 0).
Proof. exact (@lem7005607 A x u v f h1 (@lem7005611 A x u v h2)). Qed.
Lemma lem7005613 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7005614 {A : Type'} (f : A -> nat) (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term115 A u v f) (h2 : term14 A x u v) : (term298 A f x) = term299.
Proof. exact (MK_COMB (@lem7005613) (@lem7005612 A f x u v h1 h2)). Qed.
Lemma lem7005615 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7005616 {A : Type'} (f : A -> nat) (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term115 A u v f) (h2 : term14 A x u v) : ((f x) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem7005614 A f x u v h1 h2) (@lem7005615)). Qed.
Lemma lem7005618 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7005619 (x : nat) : (x = x) = True.
Proof. exact (@lem7005618 nat x). Qed.
Lemma lem7005620 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem7005619 (NUMERAL 0)). Qed.
Lemma lem7005621 {A : Type'} (f : A -> nat) (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term115 A u v f) (h2 : term14 A x u v) : ((f x) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem7005616 A f x u v h1 h2) (@lem7005620)). Qed.
Lemma lem7005622 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : term300 A u v f x.
Proof. exact (fun h0 : term14 A x u v => @lem7005621 A f x u v h1 h0). Qed.
Lemma lem7005623 {A : Type'} (f : A -> nat) (x : A) (u : A -> Prop) (v : A -> Prop) : term301 A f x u v.
Proof. exact (@lem7005599 A f x u v True). Qed.
Lemma lem7005624 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : (term289 A u v f x) = (term302 A x u v).
Proof. exact (@lem7005623 A f x u v (@lem7005622 A x u v f h1)). Qed.
Lemma lem7005626 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7005627 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) : (term302 A x u v) = True.
Proof. exact (@lem7005626 (term14 A x u v)). Qed.
Lemma lem7005628 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : (term289 A u v f x) = True.
Proof. exact (TRANS (@lem7005624 A x u v f h1) (@lem7005627 A x u v)). Qed.
Lemma lem7005629 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : (term303 A u v f) = (term304 A).
Proof. exact (fun_ext (fun x : A => @lem7005628 A x u v f h1)). Qed.
Lemma lem7005630 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7005631 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : (term115 A u v f) = (term305 A).
Proof. exact (MK_COMB (@lem7005630 A) (@lem7005629 A u v f h1)). Qed.
Lemma lem7005633 {A : Type'} (t : Prop) : (term306 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7005634 {A : Type'} (t : Prop) : (term306 A t) = t.
Proof. exact (@lem7005633 A t). Qed.
Lemma lem7005635 {A : Type'} : (term305 A) = True.
Proof. exact (@lem7005634 A True). Qed.
Lemma lem7005636 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : (term115 A u v f) = True.
Proof. exact (TRANS (@lem7005631 A u v f h1) (@lem7005635 A)). Qed.
Lemma lem7005637 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : True = (term115 A u v f).
Proof. exact (SYM (@lem7005636 A u v f h1)). Qed.
Lemma lem7005638 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : term115 A u v f.
Proof. exact (EQ_MP (@lem7005637 A u v f h1) (@lem0)). Qed.
Lemma lem7005639 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : (term307 A u v f) = (NUMERAL 0).
Proof. exact (@lem7005579 A u v f (@lem7005638 A u v f h1)). Qed.
Lemma lem7005640 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term308 A u v f) = (term308 A u v f).
Proof. exact (eq_refl (term308 A u v f)). Qed.
Lemma lem7005641 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : (term124 A u v f) = (term309 A u v f).
Proof. exact (MK_COMB (@lem7005640 A u v f) (@lem7005639 A u v f h1)). Qed.
Lemma lem7005689 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7005690 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : (term310 A u v f) = (term311 A u v f).
Proof. exact (MK_COMB (@lem7005689) (@lem7005641 A u v f h1)). Qed.
Lemma lem7005832 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term132 A v u f) = (term132 A v u f).
Proof. exact (eq_refl (term132 A v u f)). Qed.
Lemma lem7005833 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : (term280 A v u f) = (term312 A v u f).
Proof. exact (MK_COMB (@lem7005690 A u v f h1) (@lem7005832 A v u f)). Qed.
Lemma lem7005975 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : (term312 A v u f) = (term280 A v u f).
Proof. exact (SYM (@lem7005833 A u v f h1)). Qed.
Lemma lem7005995 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term132 A v u f) = (term313 A u v f).
Proof. exact (@lem1032098 (term307 A v u f) (term314 A u v f)). Qed.
Lemma lem7006002 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term309 A u v f) = (term314 A u v f).
Proof. exact (@lem1032060 (term314 A u v f)). Qed.
Lemma lem7006003 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7006004 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term311 A u v f) = (term315 A u v f).
Proof. exact (MK_COMB (@lem7006003) (@lem7006002 A u v f)). Qed.
Lemma lem7006008 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term312 A v u f) = (term316 A u v f).
Proof. exact (MK_COMB (@lem7006004 A u v f) (@lem7005995 A u v f)). Qed.
Lemma lem7006010 (m : nat) (n : nat) : (Peano.le m n) = (term317 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7006011 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term316 A u v f) = (term318 A u v f).
Proof. exact (@lem7006010 (term314 A u v f) (term313 A u v f)). Qed.
Lemma lem7006013 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7006014 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term321 A u v f) = (term322 A u v f).
Proof. exact (@lem7006013 (term307 A v u f) (term314 A u v f)). Qed.
Lemma lem7006015 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term323 A u v f) = (term323 A u v f).
Proof. exact (eq_refl (term323 A u v f)). Qed.
Lemma lem7006016 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term318 A u v f) = (term324 A u v f).
Proof. exact (MK_COMB (@lem7006015 A u v f) (@lem7006014 A u v f)). Qed.
Lemma lem7006017 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term316 A u v f) = (term324 A u v f).
Proof. exact (TRANS (@lem7006011 A u v f) (@lem7006016 A u v f)). Qed.
Lemma lem7006018 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term312 A v u f) = (term324 A u v f).
Proof. exact (TRANS (@lem7006008 A u v f) (@lem7006017 A u v f)). Qed.
Lemma lem7006019 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term325 A v u f.
Proof. exact (@lem2307535 (term307 A v u f)). Qed.
Lemma lem7006020 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term325 A v u f) = (term326 A v u f).
Proof. exact (eq_refl (term325 A v u f)). Qed.
Lemma lem7006021 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term326 A v u f.
Proof. exact (EQ_MP (@lem7006020 A v u f) (@lem7006019 A v u f)). Qed.
Lemma lem7006022 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term327 A u v f.
Proof. exact (@lem2307535 (term314 A u v f)). Qed.
Lemma lem7006023 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term327 A u v f) = (term328 A u v f).
Proof. exact (eq_refl (term327 A u v f)). Qed.
Lemma lem7006024 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term328 A u v f.
Proof. exact (EQ_MP (@lem7006023 A u v f) (@lem7006022 A u v f)). Qed.
Lemma lem7006025 (_93489 : int) (_93490 : int) : (term329 _93489 _93490) = (term330 _93489 _93490).
Proof. exact (@lem2318604 (term330 _93489 _93490)). Qed.
Lemma lem7006042 (_93489 : int) (_93490 : int) : (term331 _93489 _93490) = (term332 _93489 _93490).
Proof. exact (@lem17362 (term333 _93490) (term334 _93489 _93490)). Qed.
Lemma lem7006044 (_93489 : int) : (term335 _93489) = (term335 _93489).
Proof. exact (eq_refl (term335 _93489)). Qed.
Lemma lem7006045 (_93489 : int) (_93490 : int) : (term336 _93489 _93490) = (term337 _93489 _93490).
Proof. exact (MK_COMB (@lem7006044 _93489) (@lem7006042 _93489 _93490)). Qed.
Lemma lem7006046 (_93489 : int) (_93490 : int) : (term338 _93489 _93490) = (term336 _93489 _93490).
Proof. exact (@lem17362 (term333 _93489) (term339 _93489 _93490)). Qed.
Lemma lem7006060 (_93489 : int) (_93490 : int) : (term338 _93489 _93490) = (term337 _93489 _93490).
Proof. exact (TRANS (@lem7006046 _93489 _93490) (@lem7006045 _93489 _93490)). Qed.
Lemma lem7006063 (x : int) (y : int) : (int_le x y) = (term340 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7006064 (_93489 : int) : (term333 _93489) = (term341 _93489).
Proof. exact (@lem7006063 term342 _93489). Qed.
Lemma lem7006066 (n : nat) : (term343 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7006067 : term344 = term345.
Proof. exact (@lem7006066 (NUMERAL 0)). Qed.
Lemma lem7006068 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7006069 : term346 = term347.
Proof. exact (MK_COMB (@lem7006068) (@lem7006067)). Qed.
Lemma lem7006070 (_93489 : int) : (real_of_int _93489) = (real_of_int _93489).
Proof. exact (eq_refl (real_of_int _93489)). Qed.
Lemma lem7006071 (_93489 : int) : (term341 _93489) = (term348 _93489).
Proof. exact (MK_COMB (@lem7006069) (@lem7006070 _93489)). Qed.
Lemma lem7006073 (_93489 : int) : (term333 _93489) = (term348 _93489).
Proof. exact (TRANS (@lem7006064 _93489) (@lem7006071 _93489)). Qed.
Lemma lem7006076 (x : int) (y : int) : (int_le x y) = (term340 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7006077 (_93490 : int) : (term333 _93490) = (term341 _93490).
Proof. exact (@lem7006076 term342 _93490). Qed.
Lemma lem7006079 (n : nat) : (term343 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7006080 : term344 = term345.
Proof. exact (@lem7006079 (NUMERAL 0)). Qed.
Lemma lem7006081 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7006082 : term346 = term347.
Proof. exact (MK_COMB (@lem7006081) (@lem7006080)). Qed.
Lemma lem7006083 (_93490 : int) : (real_of_int _93490) = (real_of_int _93490).
Proof. exact (eq_refl (real_of_int _93490)). Qed.
Lemma lem7006084 (_93490 : int) : (term341 _93490) = (term348 _93490).
Proof. exact (MK_COMB (@lem7006082) (@lem7006083 _93490)). Qed.
Lemma lem7006086 (_93490 : int) : (term333 _93490) = (term348 _93490).
Proof. exact (TRANS (@lem7006077 _93490) (@lem7006084 _93490)). Qed.
Lemma lem7006088 (y : int) (x : int) : (term349 x y) = (term350 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7006089 (_93489 : int) (_93490 : int) : (term351 _93489 _93490) = (term352 _93489 _93490).
Proof. exact (@lem7006088 (int_add _93489 _93490) _93490). Qed.
Lemma lem7006091 (x : int) (y : int) : (int_le x y) = (term340 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7006092 (_93489 : int) (_93490 : int) : (term352 _93489 _93490) = (term353 _93489 _93490).
Proof. exact (@lem7006091 (term354 _93489 _93490) _93490). Qed.
Lemma lem7006094 (x : int) (y : int) : (term355 x y) = (term356 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7006095 (_93489 : int) (_93490 : int) : (term357 _93489 _93490) = (term358 _93489 _93490).
Proof. exact (@lem7006094 (int_add _93489 _93490) term359). Qed.
Lemma lem7006097 (x : int) (y : int) : (term355 x y) = (term356 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7006098 (_93489 : int) (_93490 : int) : (term355 _93489 _93490) = (term356 _93489 _93490).
Proof. exact (@lem7006097 _93489 _93490). Qed.
Lemma lem7006099 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7006100 (_93489 : int) (_93490 : int) : (term360 _93489 _93490) = (term361 _93489 _93490).
Proof. exact (MK_COMB (@lem7006099) (@lem7006098 _93489 _93490)). Qed.
Lemma lem7006102 (n : nat) : (term343 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7006103 : term362 = term363.
Proof. exact (@lem7006102 term364). Qed.
Lemma lem7006104 (_93489 : int) (_93490 : int) : (term358 _93489 _93490) = (term365 _93489 _93490).
Proof. exact (MK_COMB (@lem7006100 _93489 _93490) (@lem7006103)). Qed.
Lemma lem7006105 (_93489 : int) (_93490 : int) : (term357 _93489 _93490) = (term365 _93489 _93490).
Proof. exact (TRANS (@lem7006095 _93489 _93490) (@lem7006104 _93489 _93490)). Qed.
Lemma lem7006106 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7006107 (_93489 : int) (_93490 : int) : (term366 _93489 _93490) = (term367 _93489 _93490).
Proof. exact (MK_COMB (@lem7006106) (@lem7006105 _93489 _93490)). Qed.
Lemma lem7006108 (_93490 : int) : (real_of_int _93490) = (real_of_int _93490).
Proof. exact (eq_refl (real_of_int _93490)). Qed.
Lemma lem7006109 (_93489 : int) (_93490 : int) : (term353 _93489 _93490) = (term368 _93489 _93490).
Proof. exact (MK_COMB (@lem7006107 _93489 _93490) (@lem7006108 _93490)). Qed.
Lemma lem7006110 (_93489 : int) (_93490 : int) : (term352 _93489 _93490) = (term368 _93489 _93490).
Proof. exact (TRANS (@lem7006092 _93489 _93490) (@lem7006109 _93489 _93490)). Qed.
Lemma lem7006111 (_93489 : int) (_93490 : int) : (term351 _93489 _93490) = (term368 _93489 _93490).
Proof. exact (TRANS (@lem7006089 _93489 _93490) (@lem7006110 _93489 _93490)). Qed.
Lemma lem7006112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7006113 (_93490 : int) : (term335 _93490) = (term369 _93490).
Proof. exact (MK_COMB (@lem7006112) (@lem7006086 _93490)). Qed.
Lemma lem7006114 (_93489 : int) (_93490 : int) : (term332 _93489 _93490) = (term370 _93489 _93490).
Proof. exact (MK_COMB (@lem7006113 _93490) (@lem7006111 _93489 _93490)). Qed.
Lemma lem7006115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7006116 (_93489 : int) : (term335 _93489) = (term369 _93489).
Proof. exact (MK_COMB (@lem7006115) (@lem7006073 _93489)). Qed.
Lemma lem7006117 (_93489 : int) (_93490 : int) : (term337 _93489 _93490) = (term371 _93489 _93490).
Proof. exact (MK_COMB (@lem7006116 _93489) (@lem7006114 _93489 _93490)). Qed.
Lemma lem7006118 (_93489 : int) (_93490 : int) : (term338 _93489 _93490) = (term371 _93489 _93490).
Proof. exact (TRANS (@lem7006060 _93489 _93490) (@lem7006117 _93489 _93490)). Qed.
Lemma lem7006122 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7006148 (_93489 : int) (_93490 : int) : (term372 _93489 _93490) = (term371 _93489 _93490).
Proof. exact (@lem7006122 (term371 _93489 _93490)). Qed.
Lemma lem7006149 (_93489 : int) : (term348 _93489) = (term373 _93489).
Proof. exact (@lem1988287 (real_of_int _93489) term345). Qed.
Lemma lem7006155 (_93489 : int) : (term374 _93489) = (term375 _93489).
Proof. exact (@lem1982792 (real_of_int _93489) term345). Qed.
Lemma lem7006157 (x : nat) : (real_of_num x) = (term376 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7006158 : term345 = term377.
Proof. exact (@lem7006157 (NUMERAL 0)). Qed.
Lemma lem7006160 (x : nat) : (term378 x) = (term379 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7006161 : term380 = term381.
Proof. exact (@lem7006160 term364). Qed.
Lemma lem7006162 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7006163 : term382 = term383.
Proof. exact (MK_COMB (@lem7006162) (@lem7006161)). Qed.
Lemma lem7006164 : term384 = term385.
Proof. exact (MK_COMB (@lem7006163) (@lem7006158)). Qed.
Lemma lem7006165 : term385 = term386.
Proof. exact (@lem1981613 term380 term345 term363 term363). Qed.
Lemma lem7006167 (m : nat) (n : nat) : (term387 m n) = (term388 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7006168 : term389 = term390.
Proof. exact (@lem7006167 term364 term364). Qed.
Lemma lem7006169 : (term391 = (BIT1 0)) = (term392 = term364).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7006170 : term392 = term364.
Proof. exact (EQ_MP (@lem7006169) (@lem940073)). Qed.
Lemma lem7006171 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7006172 : term390 = term363.
Proof. exact (MK_COMB (@lem7006171) (@lem7006170)). Qed.
Lemma lem7006173 : term389 = term363.
Proof. exact (TRANS (@lem7006168) (@lem7006172)). Qed.
Lemma lem7006175 (x : nat) : (term393 x) = term345.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7006176 : term384 = term345.
Proof. exact (@lem7006175 term364). Qed.
Lemma lem7006177 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7006178 : term394 = term395.
Proof. exact (MK_COMB (@lem7006177) (@lem7006176)). Qed.
Lemma lem7006179 : term386 = term377.
Proof. exact (MK_COMB (@lem7006178) (@lem7006173)). Qed.
Lemma lem7006180 : term385 = term377.
Proof. exact (TRANS (@lem7006165) (@lem7006179)). Qed.
Lemma lem7006181 : term384 = term377.
Proof. exact (TRANS (@lem7006164) (@lem7006180)). Qed.
Lemma lem7006183 (x : real) : (term396 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7006184 : term377 = term345.
Proof. exact (@lem7006183 term345). Qed.
Lemma lem7006185 : term384 = term345.
Proof. exact (TRANS (@lem7006181) (@lem7006184)). Qed.
Lemma lem7006186 (_93489 : int) : (term397 _93489) = (term397 _93489).
Proof. exact (eq_refl (term397 _93489)). Qed.
Lemma lem7006187 (_93489 : int) : (term375 _93489) = (term398 _93489).
Proof. exact (MK_COMB (@lem7006186 _93489) (@lem7006185)). Qed.
Lemma lem7006188 (_93489 : int) : (term398 _93489) = (real_of_int _93489).
Proof. exact (@lem1982723 (real_of_int _93489)). Qed.
Lemma lem7006189 (_93489 : int) : (term375 _93489) = (real_of_int _93489).
Proof. exact (TRANS (@lem7006187 _93489) (@lem7006188 _93489)). Qed.
Lemma lem7006191 (_93489 : int) : (term374 _93489) = (real_of_int _93489).
Proof. exact (TRANS (@lem7006155 _93489) (@lem7006189 _93489)). Qed.
Lemma lem7006192 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7006193 (_93489 : int) : (term399 _93489) = (term400 _93489).
Proof. exact (MK_COMB (@lem7006192) (@lem7006191 _93489)). Qed.
Lemma lem7006194 : term345 = term345.
Proof. exact (eq_refl term345). Qed.
Lemma lem7006195 (_93489 : int) : (term373 _93489) = (term401 _93489).
Proof. exact (MK_COMB (@lem7006193 _93489) (@lem7006194)). Qed.
Lemma lem7006196 (_93489 : int) : (term348 _93489) = (term401 _93489).
Proof. exact (TRANS (@lem7006149 _93489) (@lem7006195 _93489)). Qed.
Lemma lem7006197 (_93490 : int) : (term348 _93490) = (term373 _93490).
Proof. exact (@lem1988287 (real_of_int _93490) term345). Qed.
Lemma lem7006203 (_93490 : int) : (term374 _93490) = (term375 _93490).
Proof. exact (@lem1982792 (real_of_int _93490) term345). Qed.
Lemma lem7006205 (x : nat) : (real_of_num x) = (term376 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7006206 : term345 = term377.
Proof. exact (@lem7006205 (NUMERAL 0)). Qed.
Lemma lem7006208 (x : nat) : (term378 x) = (term379 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7006209 : term380 = term381.
Proof. exact (@lem7006208 term364). Qed.
Lemma lem7006210 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7006211 : term382 = term383.
Proof. exact (MK_COMB (@lem7006210) (@lem7006209)). Qed.
Lemma lem7006212 : term384 = term385.
Proof. exact (MK_COMB (@lem7006211) (@lem7006206)). Qed.
Lemma lem7006213 : term385 = term386.
Proof. exact (@lem1981613 term380 term345 term363 term363). Qed.
Lemma lem7006215 (m : nat) (n : nat) : (term387 m n) = (term388 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7006216 : term389 = term390.
Proof. exact (@lem7006215 term364 term364). Qed.
Lemma lem7006217 : (term391 = (BIT1 0)) = (term392 = term364).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7006218 : term392 = term364.
Proof. exact (EQ_MP (@lem7006217) (@lem940073)). Qed.
Lemma lem7006219 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7006220 : term390 = term363.
Proof. exact (MK_COMB (@lem7006219) (@lem7006218)). Qed.
Lemma lem7006221 : term389 = term363.
Proof. exact (TRANS (@lem7006216) (@lem7006220)). Qed.
Lemma lem7006223 (x : nat) : (term393 x) = term345.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7006224 : term384 = term345.
Proof. exact (@lem7006223 term364). Qed.
Lemma lem7006225 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7006226 : term394 = term395.
Proof. exact (MK_COMB (@lem7006225) (@lem7006224)). Qed.
Lemma lem7006227 : term386 = term377.
Proof. exact (MK_COMB (@lem7006226) (@lem7006221)). Qed.
Lemma lem7006228 : term385 = term377.
Proof. exact (TRANS (@lem7006213) (@lem7006227)). Qed.
Lemma lem7006229 : term384 = term377.
Proof. exact (TRANS (@lem7006212) (@lem7006228)). Qed.
Lemma lem7006231 (x : real) : (term396 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7006232 : term377 = term345.
Proof. exact (@lem7006231 term345). Qed.
Lemma lem7006233 : term384 = term345.
Proof. exact (TRANS (@lem7006229) (@lem7006232)). Qed.
Lemma lem7006234 (_93490 : int) : (term397 _93490) = (term397 _93490).
Proof. exact (eq_refl (term397 _93490)). Qed.
Lemma lem7006235 (_93490 : int) : (term375 _93490) = (term398 _93490).
Proof. exact (MK_COMB (@lem7006234 _93490) (@lem7006233)). Qed.
Lemma lem7006236 (_93490 : int) : (term398 _93490) = (real_of_int _93490).
Proof. exact (@lem1982723 (real_of_int _93490)). Qed.
Lemma lem7006237 (_93490 : int) : (term375 _93490) = (real_of_int _93490).
Proof. exact (TRANS (@lem7006235 _93490) (@lem7006236 _93490)). Qed.
Lemma lem7006239 (_93490 : int) : (term374 _93490) = (real_of_int _93490).
Proof. exact (TRANS (@lem7006203 _93490) (@lem7006237 _93490)). Qed.
Lemma lem7006240 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7006241 (_93490 : int) : (term399 _93490) = (term400 _93490).
Proof. exact (MK_COMB (@lem7006240) (@lem7006239 _93490)). Qed.
Lemma lem7006242 : term345 = term345.
Proof. exact (eq_refl term345). Qed.
Lemma lem7006243 (_93490 : int) : (term373 _93490) = (term401 _93490).
Proof. exact (MK_COMB (@lem7006241 _93490) (@lem7006242)). Qed.
Lemma lem7006244 (_93490 : int) : (term348 _93490) = (term401 _93490).
Proof. exact (TRANS (@lem7006197 _93490) (@lem7006243 _93490)). Qed.
Lemma lem7006245 (_93489 : int) (_93490 : int) : (term368 _93489 _93490) = (term402 _93489 _93490).
Proof. exact (@lem1988287 (real_of_int _93490) (term365 _93489 _93490)). Qed.
Lemma lem7006262 (_93489 : int) (_93490 : int) : (term365 _93489 _93490) = (term403 _93489 _93490).
Proof. exact (@lem1982755 (real_of_int _93489) (real_of_int _93490) term363). Qed.
Lemma lem7006265 (_93490 : int) : (term404 _93490) = (term404 _93490).
Proof. exact (eq_refl (term404 _93490)). Qed.
Lemma lem7006266 (_93489 : int) (_93490 : int) : (term405 _93489 _93490) = (term406 _93489 _93490).
Proof. exact (MK_COMB (@lem7006265 _93490) (@lem7006262 _93489 _93490)). Qed.
Lemma lem7006267 (_93489 : int) (_93490 : int) : (term406 _93489 _93490) = (term407 _93489 _93490).
Proof. exact (@lem1982792 (real_of_int _93490) (term403 _93489 _93490)). Qed.
Lemma lem7006268 (_93489 : int) (_93490 : int) : (term408 _93489 _93490) = (term409 _93489 _93490).
Proof. exact (@lem1982781 (real_of_int _93489) term380 (term410 _93490)). Qed.
Lemma lem7006269 (_93490 : int) : (term411 _93490) = (term412 _93490).
Proof. exact (@lem1982781 (real_of_int _93490) term380 term363). Qed.
Lemma lem7006271 (x : nat) : (real_of_num x) = (term376 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7006272 : term363 = term413.
Proof. exact (@lem7006271 term364). Qed.
Lemma lem7006274 (x : nat) : (term378 x) = (term379 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7006275 : term380 = term381.
Proof. exact (@lem7006274 term364). Qed.
Lemma lem7006276 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7006277 : term382 = term383.
Proof. exact (MK_COMB (@lem7006276) (@lem7006275)). Qed.
Lemma lem7006278 : term414 = term415.
Proof. exact (MK_COMB (@lem7006277) (@lem7006272)). Qed.
Lemma lem7006279 : term415 = term416.
Proof. exact (@lem1981613 term380 term363 term363 term363). Qed.
Lemma lem7006281 (m : nat) (n : nat) : (term387 m n) = (term388 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7006282 : term389 = term390.
Proof. exact (@lem7006281 term364 term364). Qed.
Lemma lem7006283 : (term391 = (BIT1 0)) = (term392 = term364).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7006284 : term392 = term364.
Proof. exact (EQ_MP (@lem7006283) (@lem940073)). Qed.
Lemma lem7006285 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7006286 : term390 = term363.
Proof. exact (MK_COMB (@lem7006285) (@lem7006284)). Qed.
Lemma lem7006287 : term389 = term363.
Proof. exact (TRANS (@lem7006282) (@lem7006286)). Qed.
Lemma lem7006289 (m : nat) (n : nat) : (term417 m n) = (term418 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7006290 : term414 = term419.
Proof. exact (@lem7006289 term364 term364). Qed.
Lemma lem7006291 : (term391 = (BIT1 0)) = (term392 = term364).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7006292 : term392 = term364.
Proof. exact (EQ_MP (@lem7006291) (@lem940073)). Qed.
Lemma lem7006293 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7006294 : term390 = term363.
Proof. exact (MK_COMB (@lem7006293) (@lem7006292)). Qed.
Lemma lem7006295 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7006296 : term419 = term380.
Proof. exact (MK_COMB (@lem7006295) (@lem7006294)). Qed.
Lemma lem7006297 : term414 = term380.
Proof. exact (TRANS (@lem7006290) (@lem7006296)). Qed.
Lemma lem7006298 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7006299 : term420 = term421.
Proof. exact (MK_COMB (@lem7006298) (@lem7006297)). Qed.
Lemma lem7006300 : term416 = term381.
Proof. exact (MK_COMB (@lem7006299) (@lem7006287)). Qed.
Lemma lem7006301 : term415 = term381.
Proof. exact (TRANS (@lem7006279) (@lem7006300)). Qed.
Lemma lem7006302 : term414 = term381.
Proof. exact (TRANS (@lem7006278) (@lem7006301)). Qed.
Lemma lem7006304 (x : real) : (term396 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7006305 : term381 = term380.
Proof. exact (@lem7006304 term380). Qed.
Lemma lem7006306 : term414 = term380.
Proof. exact (TRANS (@lem7006302) (@lem7006305)). Qed.
Lemma lem7006309 (_93490 : int) : (term422 _93490) = (term422 _93490).
Proof. exact (eq_refl (term422 _93490)). Qed.
Lemma lem7006310 (_93490 : int) : (term412 _93490) = (term423 _93490).
Proof. exact (MK_COMB (@lem7006309 _93490) (@lem7006306)). Qed.
Lemma lem7006311 (_93490 : int) : (term411 _93490) = (term423 _93490).
Proof. exact (TRANS (@lem7006269 _93490) (@lem7006310 _93490)). Qed.
Lemma lem7006314 (_93489 : int) : (term422 _93489) = (term422 _93489).
Proof. exact (eq_refl (term422 _93489)). Qed.
Lemma lem7006315 (_93489 : int) (_93490 : int) : (term409 _93489 _93490) = (term424 _93489 _93490).
Proof. exact (MK_COMB (@lem7006314 _93489) (@lem7006311 _93490)). Qed.
Lemma lem7006316 (_93489 : int) (_93490 : int) : (term408 _93489 _93490) = (term424 _93489 _93490).
Proof. exact (TRANS (@lem7006268 _93489 _93490) (@lem7006315 _93489 _93490)). Qed.
Lemma lem7006317 (_93490 : int) : (term397 _93490) = (term397 _93490).
Proof. exact (eq_refl (term397 _93490)). Qed.
Lemma lem7006318 (_93489 : int) (_93490 : int) : (term407 _93489 _93490) = (term425 _93489 _93490).
Proof. exact (MK_COMB (@lem7006317 _93490) (@lem7006316 _93489 _93490)). Qed.
Lemma lem7006319 (_93489 : int) (_93490 : int) : (term425 _93489 _93490) = (term426 _93489 _93490).
Proof. exact (@lem1982757 (term427 _93489) (real_of_int _93490) (term423 _93490)). Qed.
Lemma lem7006320 (_93490 : int) : (term428 _93490) = (term429 _93490).
Proof. exact (@lem1982763 (real_of_int _93490) (term427 _93490) term380). Qed.
Lemma lem7006321 (_93490 : int) : (term430 _93490) = (term431 _93490).
Proof. exact (@lem1982715 term380 (real_of_int _93490)). Qed.
Lemma lem7006323 (x : nat) : (real_of_num x) = (term376 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7006324 : term363 = term413.
Proof. exact (@lem7006323 term364). Qed.
Lemma lem7006326 (x : nat) : (term378 x) = (term379 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7006327 : term380 = term381.
Proof. exact (@lem7006326 term364). Qed.
Lemma lem7006328 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7006329 : term432 = term433.
Proof. exact (MK_COMB (@lem7006328) (@lem7006327)). Qed.
Lemma lem7006330 : term434 = term435.
Proof. exact (MK_COMB (@lem7006329) (@lem7006324)). Qed.
Lemma lem7006331 : term436.
Proof. exact (@lem1981473 term380 term363 term363 term363 term345 term363). Qed.
Lemma lem7006333 (m : nat) (n : nat) : (term437 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7006334 : term438 = term439.
Proof. exact (@lem7006333 (NUMERAL 0) term364). Qed.
Lemma lem7006335 : term440 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7006336 (h1 : term440 = (BIT1 0)) : term439 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7006337 : (term440 = (BIT1 0)) = (term439 = True).
Proof. exact (prop_ext (fun h1 : term440 = (BIT1 0) => @lem7006336 h1) (fun h1 : term439 = True => @lem7006335)). Qed.
Lemma lem7006338 : term439 = True.
Proof. exact (EQ_MP (@lem7006337) (@lem7006335)). Qed.
Lemma lem7006339 : term438 = True.
Proof. exact (TRANS (@lem7006334) (@lem7006338)). Qed.
Lemma lem7006340 : True = term438.
Proof. exact (SYM (@lem7006339)). Qed.
Lemma lem7006341 : term438.
Proof. exact (EQ_MP (@lem7006340) (@lem0)). Qed.
Lemma lem7006342 : term441.
Proof. exact (@lem7006331 (@lem7006341)). Qed.
Lemma lem7006344 (m : nat) (n : nat) : (term437 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7006345 : term438 = term439.
Proof. exact (@lem7006344 (NUMERAL 0) term364). Qed.
Lemma lem7006346 : term440 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7006347 (h1 : term440 = (BIT1 0)) : term439 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7006348 : (term440 = (BIT1 0)) = (term439 = True).
Proof. exact (prop_ext (fun h1 : term440 = (BIT1 0) => @lem7006347 h1) (fun h1 : term439 = True => @lem7006346)). Qed.
Lemma lem7006349 : term439 = True.
Proof. exact (EQ_MP (@lem7006348) (@lem7006346)). Qed.
Lemma lem7006350 : term438 = True.
Proof. exact (TRANS (@lem7006345) (@lem7006349)). Qed.
Lemma lem7006351 : True = term438.
Proof. exact (SYM (@lem7006350)). Qed.
Lemma lem7006352 : term438.
Proof. exact (EQ_MP (@lem7006351) (@lem0)). Qed.
Lemma lem7006353 : term442.
Proof. exact (@lem7006342 (@lem7006352)). Qed.
Lemma lem7006355 (m : nat) (n : nat) : (term437 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7006356 : term438 = term439.
Proof. exact (@lem7006355 (NUMERAL 0) term364). Qed.
Lemma lem7006357 : term440 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7006358 (h1 : term440 = (BIT1 0)) : term439 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7006359 : (term440 = (BIT1 0)) = (term439 = True).
Proof. exact (prop_ext (fun h1 : term440 = (BIT1 0) => @lem7006358 h1) (fun h1 : term439 = True => @lem7006357)). Qed.
Lemma lem7006360 : term439 = True.
Proof. exact (EQ_MP (@lem7006359) (@lem7006357)). Qed.
Lemma lem7006361 : term438 = True.
Proof. exact (TRANS (@lem7006356) (@lem7006360)). Qed.
Lemma lem7006362 : True = term438.
Proof. exact (SYM (@lem7006361)). Qed.
Lemma lem7006363 : term438.
Proof. exact (EQ_MP (@lem7006362) (@lem0)). Qed.
Lemma lem7006364 : term443.
Proof. exact (@lem7006353 (@lem7006363)). Qed.
Lemma lem7006366 (m : nat) (n : nat) : (term387 m n) = (term388 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7006367 : term389 = term390.
Proof. exact (@lem7006366 term364 term364). Qed.
Lemma lem7006368 : (term391 = (BIT1 0)) = (term392 = term364).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7006369 : term392 = term364.
Proof. exact (EQ_MP (@lem7006368) (@lem940073)). Qed.
Lemma lem7006370 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7006371 : term390 = term363.
Proof. exact (MK_COMB (@lem7006370) (@lem7006369)). Qed.
Lemma lem7006372 : term389 = term363.
Proof. exact (TRANS (@lem7006367) (@lem7006371)). Qed.
Lemma lem7006374 (m : nat) (n : nat) : (term417 m n) = (term418 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7006375 : term414 = term419.
Proof. exact (@lem7006374 term364 term364). Qed.
Lemma lem7006376 : (term391 = (BIT1 0)) = (term392 = term364).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7006377 : term392 = term364.
Proof. exact (EQ_MP (@lem7006376) (@lem940073)). Qed.
Lemma lem7006378 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7006379 : term390 = term363.
Proof. exact (MK_COMB (@lem7006378) (@lem7006377)). Qed.
Lemma lem7006380 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7006381 : term419 = term380.
Proof. exact (MK_COMB (@lem7006380) (@lem7006379)). Qed.
Lemma lem7006382 : term414 = term380.
Proof. exact (TRANS (@lem7006375) (@lem7006381)). Qed.
Lemma lem7006383 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7006384 : term444 = term432.
Proof. exact (MK_COMB (@lem7006383) (@lem7006382)). Qed.
Lemma lem7006385 : term445 = term434.
Proof. exact (MK_COMB (@lem7006384) (@lem7006372)). Qed.
Lemma lem7006387 (m : nat) : (term446 m) = term345.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7006388 : term434 = term345.
Proof. exact (@lem7006387 term364). Qed.
Lemma lem7006389 : term445 = term345.
Proof. exact (TRANS (@lem7006385) (@lem7006388)). Qed.
Lemma lem7006390 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7006391 : term447 = term448.
Proof. exact (MK_COMB (@lem7006390) (@lem7006389)). Qed.
Lemma lem7006392 : term363 = term363.
Proof. exact (eq_refl term363). Qed.
Lemma lem7006393 : term449 = term450.
Proof. exact (MK_COMB (@lem7006391) (@lem7006392)). Qed.
Lemma lem7006395 (x : nat) : (term451 x) = term345.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7006396 : term450 = term345.
Proof. exact (@lem7006395 term364). Qed.
Lemma lem7006397 : term449 = term345.
Proof. exact (TRANS (@lem7006393) (@lem7006396)). Qed.
Lemma lem7006399 (m : nat) (n : nat) : (term387 m n) = (term388 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7006400 : term389 = term390.
Proof. exact (@lem7006399 term364 term364). Qed.
Lemma lem7006401 : (term391 = (BIT1 0)) = (term392 = term364).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7006402 : term392 = term364.
Proof. exact (EQ_MP (@lem7006401) (@lem940073)). Qed.
Lemma lem7006403 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7006404 : term390 = term363.
Proof. exact (MK_COMB (@lem7006403) (@lem7006402)). Qed.
Lemma lem7006405 : term389 = term363.
Proof. exact (TRANS (@lem7006400) (@lem7006404)). Qed.
Lemma lem7006406 : term448 = term448.
Proof. exact (eq_refl term448). Qed.
Lemma lem7006407 : term452 = term450.
Proof. exact (MK_COMB (@lem7006406) (@lem7006405)). Qed.
Lemma lem7006409 (x : nat) : (term451 x) = term345.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7006410 : term450 = term345.
Proof. exact (@lem7006409 term364). Qed.
Lemma lem7006411 : term452 = term345.
Proof. exact (TRANS (@lem7006407) (@lem7006410)). Qed.
Lemma lem7006412 : term345 = term452.
Proof. exact (SYM (@lem7006411)). Qed.
Lemma lem7006413 : term449 = term452.
Proof. exact (TRANS (@lem7006397) (@lem7006412)). Qed.
Lemma lem7006414 : term435 = term377.
Proof. exact (@lem7006364 (@lem7006413)). Qed.
Lemma lem7006415 : term434 = term377.
Proof. exact (TRANS (@lem7006330) (@lem7006414)). Qed.
Lemma lem7006417 (x : real) : (term396 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7006418 : term377 = term345.
Proof. exact (@lem7006417 term345). Qed.
Lemma lem7006419 : term434 = term345.
Proof. exact (TRANS (@lem7006415) (@lem7006418)). Qed.
Lemma lem7006420 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7006421 : term453 = term448.
Proof. exact (MK_COMB (@lem7006420) (@lem7006419)). Qed.
Lemma lem7006422 (_93490 : int) : (real_of_int _93490) = (real_of_int _93490).
Proof. exact (eq_refl (real_of_int _93490)). Qed.
Lemma lem7006423 (_93490 : int) : (term431 _93490) = (term454 _93490).
Proof. exact (MK_COMB (@lem7006421) (@lem7006422 _93490)). Qed.
Lemma lem7006424 (_93490 : int) : (term430 _93490) = (term454 _93490).
Proof. exact (TRANS (@lem7006321 _93490) (@lem7006423 _93490)). Qed.
Lemma lem7006425 (_93490 : int) : (term454 _93490) = term345.
Proof. exact (@lem1982719 (real_of_int _93490)). Qed.
Lemma lem7006426 (_93490 : int) : (term430 _93490) = term345.
Proof. exact (TRANS (@lem7006424 _93490) (@lem7006425 _93490)). Qed.
Lemma lem7006427 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7006428 (_93490 : int) : (term455 _93490) = term456.
Proof. exact (MK_COMB (@lem7006427) (@lem7006426 _93490)). Qed.
Lemma lem7006429 : term380 = term380.
Proof. exact (eq_refl term380). Qed.
Lemma lem7006430 (_93490 : int) : (term429 _93490) = term457.
Proof. exact (MK_COMB (@lem7006428 _93490) (@lem7006429)). Qed.
Lemma lem7006431 (_93490 : int) : (term428 _93490) = term457.
Proof. exact (TRANS (@lem7006320 _93490) (@lem7006430 _93490)). Qed.
Lemma lem7006432 : term457 = term380.
Proof. exact (@lem1982721 term380). Qed.
Lemma lem7006433 (_93490 : int) : (term428 _93490) = term380.
Proof. exact (TRANS (@lem7006431 _93490) (@lem7006432)). Qed.
Lemma lem7006434 (_93489 : int) : (term422 _93489) = (term422 _93489).
Proof. exact (eq_refl (term422 _93489)). Qed.
Lemma lem7006435 (_93490 : int) (_93489 : int) : (term426 _93489 _93490) = (term423 _93489).
Proof. exact (MK_COMB (@lem7006434 _93489) (@lem7006433 _93490)). Qed.
Lemma lem7006436 (_93490 : int) (_93489 : int) : (term425 _93489 _93490) = (term423 _93489).
Proof. exact (TRANS (@lem7006319 _93489 _93490) (@lem7006435 _93490 _93489)). Qed.
Lemma lem7006437 (_93490 : int) (_93489 : int) : (term407 _93489 _93490) = (term423 _93489).
Proof. exact (TRANS (@lem7006318 _93489 _93490) (@lem7006436 _93490 _93489)). Qed.
Lemma lem7006438 (_93490 : int) (_93489 : int) : (term406 _93489 _93490) = (term423 _93489).
Proof. exact (TRANS (@lem7006267 _93489 _93490) (@lem7006437 _93490 _93489)). Qed.
Lemma lem7006439 (_93490 : int) (_93489 : int) : (term405 _93489 _93490) = (term423 _93489).
Proof. exact (TRANS (@lem7006266 _93489 _93490) (@lem7006438 _93490 _93489)). Qed.
Lemma lem7006440 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7006441 (_93490 : int) (_93489 : int) : (term458 _93489 _93490) = (term459 _93489).
Proof. exact (MK_COMB (@lem7006440) (@lem7006439 _93490 _93489)). Qed.
Lemma lem7006442 : term345 = term345.
Proof. exact (eq_refl term345). Qed.
Lemma lem7006443 (_93490 : int) (_93489 : int) : (term402 _93489 _93490) = (term460 _93489).
Proof. exact (MK_COMB (@lem7006441 _93490 _93489) (@lem7006442)). Qed.
Lemma lem7006444 (_93490 : int) (_93489 : int) : (term368 _93489 _93490) = (term460 _93489).
Proof. exact (TRANS (@lem7006245 _93489 _93490) (@lem7006443 _93490 _93489)). Qed.
Lemma lem7006445 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7006446 (_93490 : int) : (term369 _93490) = (term461 _93490).
Proof. exact (MK_COMB (@lem7006445) (@lem7006244 _93490)). Qed.
Lemma lem7006447 (_93490 : int) (_93489 : int) : (term370 _93489 _93490) = (term462 _93490 _93489).
Proof. exact (MK_COMB (@lem7006446 _93490) (@lem7006444 _93490 _93489)). Qed.
Lemma lem7006448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7006449 (_93489 : int) : (term369 _93489) = (term461 _93489).
Proof. exact (MK_COMB (@lem7006448) (@lem7006196 _93489)). Qed.
Lemma lem7006450 (_93490 : int) (_93489 : int) : (term371 _93489 _93490) = (term463 _93490 _93489).
Proof. exact (MK_COMB (@lem7006449 _93489) (@lem7006447 _93490 _93489)). Qed.
Lemma lem7006471 (_93490 : int) (_93489 : int) : (term372 _93489 _93490) = (term463 _93490 _93489).
Proof. exact (TRANS (@lem7006148 _93489 _93490) (@lem7006450 _93490 _93489)). Qed.
Lemma lem7006475 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : term463 _93490 _93489.
Proof. exact (h1). Qed.
Lemma lem7006476 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : term462 _93490 _93489.
Proof. exact (proj2 (@lem7006475 _93490 _93489 h1)). Qed.
Lemma lem7006477 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : term401 _93489.
Proof. exact (proj1 (@lem7006475 _93490 _93489 h1)). Qed.
Lemma lem7006478 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : term460 _93489.
Proof. exact (proj2 (@lem7006476 _93490 _93489 h1)). Qed.
Lemma lem7006481 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7006482 : term464 = term438.
Proof. exact (@lem7006481 term345 term363). Qed.
Lemma lem7006484 (x : nat) : (real_of_num x) = (term376 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7006485 : term363 = term413.
Proof. exact (@lem7006484 term364). Qed.
Lemma lem7006487 (x : nat) : (real_of_num x) = (term376 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7006488 : term345 = term377.
Proof. exact (@lem7006487 (NUMERAL 0)). Qed.
Lemma lem7006489 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7006490 : term465 = term466.
Proof. exact (MK_COMB (@lem7006489) (@lem7006488)). Qed.
Lemma lem7006491 : term438 = term467.
Proof. exact (MK_COMB (@lem7006490) (@lem7006485)). Qed.
Lemma lem7006492 : term468.
Proof. exact (@lem1980255 term345 term363 term363 term363). Qed.
Lemma lem7006494 (m : nat) (n : nat) : (term437 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7006495 : term438 = term439.
Proof. exact (@lem7006494 (NUMERAL 0) term364). Qed.
Lemma lem7006496 : term440 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7006497 (h1 : term440 = (BIT1 0)) : term439 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7006498 : (term440 = (BIT1 0)) = (term439 = True).
Proof. exact (prop_ext (fun h1 : term440 = (BIT1 0) => @lem7006497 h1) (fun h1 : term439 = True => @lem7006496)). Qed.
Lemma lem7006499 : term439 = True.
Proof. exact (EQ_MP (@lem7006498) (@lem7006496)). Qed.
Lemma lem7006500 : term438 = True.
Proof. exact (TRANS (@lem7006495) (@lem7006499)). Qed.
Lemma lem7006501 : True = term438.
Proof. exact (SYM (@lem7006500)). Qed.
Lemma lem7006502 : term438.
Proof. exact (EQ_MP (@lem7006501) (@lem0)). Qed.
Lemma lem7006503 : term469.
Proof. exact (@lem7006492 (@lem7006502)). Qed.
Lemma lem7006505 (m : nat) (n : nat) : (term437 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7006506 : term438 = term439.
Proof. exact (@lem7006505 (NUMERAL 0) term364). Qed.
Lemma lem7006507 : term440 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7006508 (h1 : term440 = (BIT1 0)) : term439 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7006509 : (term440 = (BIT1 0)) = (term439 = True).
Proof. exact (prop_ext (fun h1 : term440 = (BIT1 0) => @lem7006508 h1) (fun h1 : term439 = True => @lem7006507)). Qed.
Lemma lem7006510 : term439 = True.
Proof. exact (EQ_MP (@lem7006509) (@lem7006507)). Qed.
Lemma lem7006511 : term438 = True.
Proof. exact (TRANS (@lem7006506) (@lem7006510)). Qed.
Lemma lem7006512 : True = term438.
Proof. exact (SYM (@lem7006511)). Qed.
Lemma lem7006513 : term438.
Proof. exact (EQ_MP (@lem7006512) (@lem0)). Qed.
Lemma lem7006514 : term467 = term470.
Proof. exact (@lem7006503 (@lem7006513)). Qed.
Lemma lem7006516 (m : nat) (n : nat) : (term387 m n) = (term388 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7006517 : term389 = term390.
Proof. exact (@lem7006516 term364 term364). Qed.
Lemma lem7006518 : (term391 = (BIT1 0)) = (term392 = term364).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7006519 : term392 = term364.
Proof. exact (EQ_MP (@lem7006518) (@lem940073)). Qed.
Lemma lem7006520 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7006521 : term390 = term363.
Proof. exact (MK_COMB (@lem7006520) (@lem7006519)). Qed.
Lemma lem7006522 : term389 = term363.
Proof. exact (TRANS (@lem7006517) (@lem7006521)). Qed.
Lemma lem7006524 (x : nat) : (term451 x) = term345.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7006525 : term450 = term345.
Proof. exact (@lem7006524 term364). Qed.
Lemma lem7006526 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7006527 : term471 = term465.
Proof. exact (MK_COMB (@lem7006526) (@lem7006525)). Qed.
Lemma lem7006528 : term470 = term438.
Proof. exact (MK_COMB (@lem7006527) (@lem7006522)). Qed.
Lemma lem7006530 (m : nat) (n : nat) : (term437 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7006531 : term438 = term439.
Proof. exact (@lem7006530 (NUMERAL 0) term364). Qed.
Lemma lem7006532 : term440 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7006533 (h1 : term440 = (BIT1 0)) : term439 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7006534 : (term440 = (BIT1 0)) = (term439 = True).
Proof. exact (prop_ext (fun h1 : term440 = (BIT1 0) => @lem7006533 h1) (fun h1 : term439 = True => @lem7006532)). Qed.
Lemma lem7006535 : term439 = True.
Proof. exact (EQ_MP (@lem7006534) (@lem7006532)). Qed.
Lemma lem7006536 : term438 = True.
Proof. exact (TRANS (@lem7006531) (@lem7006535)). Qed.
Lemma lem7006537 : term470 = True.
Proof. exact (TRANS (@lem7006528) (@lem7006536)). Qed.
Lemma lem7006538 : term467 = True.
Proof. exact (TRANS (@lem7006514) (@lem7006537)). Qed.
Lemma lem7006539 : term438 = True.
Proof. exact (TRANS (@lem7006491) (@lem7006538)). Qed.
Lemma lem7006540 : term464 = True.
Proof. exact (TRANS (@lem7006482) (@lem7006539)). Qed.
Lemma lem7006541 : True = term464.
Proof. exact (SYM (@lem7006540)). Qed.
Lemma lem7006542 : term464.
Proof. exact (EQ_MP (@lem7006541) (@lem0)). Qed.
Lemma lem7006543 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : term472 _93489.
Proof. exact (conj (@lem7006542) (@lem7006477 _93490 _93489 h1)). Qed.
Lemma lem7006545 (x : real) (y : real) : term473 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7006546 (_93489 : int) : term474 _93489.
Proof. exact (@lem7006545 term363 (real_of_int _93489)). Qed.
Lemma lem7006547 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : term475 _93489.
Proof. exact (@lem7006546 _93489 (@lem7006543 _93490 _93489 h1)). Qed.
Lemma lem7006548 (_93489 : int) : (term476 _93489) = (real_of_int _93489).
Proof. exact (@lem1982733 (real_of_int _93489)). Qed.
Lemma lem7006549 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7006550 (_93489 : int) : (term477 _93489) = (term400 _93489).
Proof. exact (MK_COMB (@lem7006549) (@lem7006548 _93489)). Qed.
Lemma lem7006551 : term345 = term345.
Proof. exact (eq_refl term345). Qed.
Lemma lem7006552 (_93489 : int) : (term475 _93489) = (term401 _93489).
Proof. exact (MK_COMB (@lem7006550 _93489) (@lem7006551)). Qed.
Lemma lem7006553 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : term401 _93489.
Proof. exact (EQ_MP (@lem7006552 _93489) (@lem7006547 _93490 _93489 h1)). Qed.
Lemma lem7006555 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7006556 : term464 = term438.
Proof. exact (@lem7006555 term345 term363). Qed.
Lemma lem7006558 (x : nat) : (real_of_num x) = (term376 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7006559 : term363 = term413.
Proof. exact (@lem7006558 term364). Qed.
Lemma lem7006561 (x : nat) : (real_of_num x) = (term376 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7006562 : term345 = term377.
Proof. exact (@lem7006561 (NUMERAL 0)). Qed.
Lemma lem7006563 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7006564 : term465 = term466.
Proof. exact (MK_COMB (@lem7006563) (@lem7006562)). Qed.
Lemma lem7006565 : term438 = term467.
Proof. exact (MK_COMB (@lem7006564) (@lem7006559)). Qed.
Lemma lem7006566 : term468.
Proof. exact (@lem1980255 term345 term363 term363 term363). Qed.
Lemma lem7006568 (m : nat) (n : nat) : (term437 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7006569 : term438 = term439.
Proof. exact (@lem7006568 (NUMERAL 0) term364). Qed.
Lemma lem7006570 : term440 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7006571 (h1 : term440 = (BIT1 0)) : term439 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7006572 : (term440 = (BIT1 0)) = (term439 = True).
Proof. exact (prop_ext (fun h1 : term440 = (BIT1 0) => @lem7006571 h1) (fun h1 : term439 = True => @lem7006570)). Qed.
Lemma lem7006573 : term439 = True.
Proof. exact (EQ_MP (@lem7006572) (@lem7006570)). Qed.
Lemma lem7006574 : term438 = True.
Proof. exact (TRANS (@lem7006569) (@lem7006573)). Qed.
Lemma lem7006575 : True = term438.
Proof. exact (SYM (@lem7006574)). Qed.
Lemma lem7006576 : term438.
Proof. exact (EQ_MP (@lem7006575) (@lem0)). Qed.
Lemma lem7006577 : term469.
Proof. exact (@lem7006566 (@lem7006576)). Qed.
Lemma lem7006579 (m : nat) (n : nat) : (term437 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7006580 : term438 = term439.
Proof. exact (@lem7006579 (NUMERAL 0) term364). Qed.
Lemma lem7006581 : term440 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7006582 (h1 : term440 = (BIT1 0)) : term439 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7006583 : (term440 = (BIT1 0)) = (term439 = True).
Proof. exact (prop_ext (fun h1 : term440 = (BIT1 0) => @lem7006582 h1) (fun h1 : term439 = True => @lem7006581)). Qed.
Lemma lem7006584 : term439 = True.
Proof. exact (EQ_MP (@lem7006583) (@lem7006581)). Qed.
Lemma lem7006585 : term438 = True.
Proof. exact (TRANS (@lem7006580) (@lem7006584)). Qed.
Lemma lem7006586 : True = term438.
Proof. exact (SYM (@lem7006585)). Qed.
Lemma lem7006587 : term438.
Proof. exact (EQ_MP (@lem7006586) (@lem0)). Qed.
Lemma lem7006588 : term467 = term470.
Proof. exact (@lem7006577 (@lem7006587)). Qed.
Lemma lem7006590 (m : nat) (n : nat) : (term387 m n) = (term388 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7006591 : term389 = term390.
Proof. exact (@lem7006590 term364 term364). Qed.
Lemma lem7006592 : (term391 = (BIT1 0)) = (term392 = term364).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7006593 : term392 = term364.
Proof. exact (EQ_MP (@lem7006592) (@lem940073)). Qed.
Lemma lem7006594 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7006595 : term390 = term363.
Proof. exact (MK_COMB (@lem7006594) (@lem7006593)). Qed.
Lemma lem7006596 : term389 = term363.
Proof. exact (TRANS (@lem7006591) (@lem7006595)). Qed.
Lemma lem7006598 (x : nat) : (term451 x) = term345.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7006599 : term450 = term345.
Proof. exact (@lem7006598 term364). Qed.
Lemma lem7006600 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7006601 : term471 = term465.
Proof. exact (MK_COMB (@lem7006600) (@lem7006599)). Qed.
Lemma lem7006602 : term470 = term438.
Proof. exact (MK_COMB (@lem7006601) (@lem7006596)). Qed.
Lemma lem7006604 (m : nat) (n : nat) : (term437 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7006605 : term438 = term439.
Proof. exact (@lem7006604 (NUMERAL 0) term364). Qed.
Lemma lem7006606 : term440 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7006607 (h1 : term440 = (BIT1 0)) : term439 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7006608 : (term440 = (BIT1 0)) = (term439 = True).
Proof. exact (prop_ext (fun h1 : term440 = (BIT1 0) => @lem7006607 h1) (fun h1 : term439 = True => @lem7006606)). Qed.
Lemma lem7006609 : term439 = True.
Proof. exact (EQ_MP (@lem7006608) (@lem7006606)). Qed.
Lemma lem7006610 : term438 = True.
Proof. exact (TRANS (@lem7006605) (@lem7006609)). Qed.
Lemma lem7006611 : term470 = True.
Proof. exact (TRANS (@lem7006602) (@lem7006610)). Qed.
Lemma lem7006612 : term467 = True.
Proof. exact (TRANS (@lem7006588) (@lem7006611)). Qed.
Lemma lem7006613 : term438 = True.
Proof. exact (TRANS (@lem7006565) (@lem7006612)). Qed.
Lemma lem7006614 : term464 = True.
Proof. exact (TRANS (@lem7006556) (@lem7006613)). Qed.
Lemma lem7006615 : True = term464.
Proof. exact (SYM (@lem7006614)). Qed.
Lemma lem7006616 : term464.
Proof. exact (EQ_MP (@lem7006615) (@lem0)). Qed.
Lemma lem7006617 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : term478 _93489.
Proof. exact (conj (@lem7006616) (@lem7006478 _93490 _93489 h1)). Qed.
Lemma lem7006619 (x : real) (y : real) : term473 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7006620 (_93489 : int) : term479 _93489.
Proof. exact (@lem7006619 term363 (term423 _93489)). Qed.
Lemma lem7006621 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : term480 _93489.
Proof. exact (@lem7006620 _93489 (@lem7006617 _93490 _93489 h1)). Qed.
Lemma lem7006622 (_93489 : int) : (term481 _93489) = (term423 _93489).
Proof. exact (@lem1982733 (term423 _93489)). Qed.
Lemma lem7006623 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7006624 (_93489 : int) : (term482 _93489) = (term459 _93489).
Proof. exact (MK_COMB (@lem7006623) (@lem7006622 _93489)). Qed.
Lemma lem7006625 : term345 = term345.
Proof. exact (eq_refl term345). Qed.
Lemma lem7006626 (_93489 : int) : (term480 _93489) = (term460 _93489).
Proof. exact (MK_COMB (@lem7006624 _93489) (@lem7006625)). Qed.
Lemma lem7006627 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : term460 _93489.
Proof. exact (EQ_MP (@lem7006626 _93489) (@lem7006621 _93490 _93489 h1)). Qed.
Lemma lem7006628 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : term483 _93489.
Proof. exact (conj (@lem7006627 _93490 _93489 h1) (@lem7006553 _93490 _93489 h1)). Qed.
Lemma lem7006630 (x : real) (y : real) : term484 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7006631 (_93489 : int) : term485 _93489.
Proof. exact (@lem7006630 (term423 _93489) (real_of_int _93489)). Qed.
Lemma lem7006632 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : term486 _93489.
Proof. exact (@lem7006631 _93489 (@lem7006628 _93490 _93489 h1)). Qed.
Lemma lem7006633 (_93489 : int) : (term487 _93489) = (term488 _93489).
Proof. exact (@lem1982759 (term427 _93489) (real_of_int _93489) term380). Qed.
Lemma lem7006634 (_93489 : int) : (term489 _93489) = (term431 _93489).
Proof. exact (@lem1982713 term380 (real_of_int _93489)). Qed.
Lemma lem7006636 (x : nat) : (real_of_num x) = (term376 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7006637 : term363 = term413.
Proof. exact (@lem7006636 term364). Qed.
Lemma lem7006639 (x : nat) : (term378 x) = (term379 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7006640 : term380 = term381.
Proof. exact (@lem7006639 term364). Qed.
Lemma lem7006641 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7006642 : term432 = term433.
Proof. exact (MK_COMB (@lem7006641) (@lem7006640)). Qed.
Lemma lem7006643 : term434 = term435.
Proof. exact (MK_COMB (@lem7006642) (@lem7006637)). Qed.
Lemma lem7006644 : term436.
Proof. exact (@lem1981473 term380 term363 term363 term363 term345 term363). Qed.
Lemma lem7006646 (m : nat) (n : nat) : (term437 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7006647 : term438 = term439.
Proof. exact (@lem7006646 (NUMERAL 0) term364). Qed.
Lemma lem7006648 : term440 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7006649 (h1 : term440 = (BIT1 0)) : term439 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7006650 : (term440 = (BIT1 0)) = (term439 = True).
Proof. exact (prop_ext (fun h1 : term440 = (BIT1 0) => @lem7006649 h1) (fun h1 : term439 = True => @lem7006648)). Qed.
Lemma lem7006651 : term439 = True.
Proof. exact (EQ_MP (@lem7006650) (@lem7006648)). Qed.
Lemma lem7006652 : term438 = True.
Proof. exact (TRANS (@lem7006647) (@lem7006651)). Qed.
Lemma lem7006653 : True = term438.
Proof. exact (SYM (@lem7006652)). Qed.
Lemma lem7006654 : term438.
Proof. exact (EQ_MP (@lem7006653) (@lem0)). Qed.
Lemma lem7006655 : term441.
Proof. exact (@lem7006644 (@lem7006654)). Qed.
Lemma lem7006657 (m : nat) (n : nat) : (term437 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7006658 : term438 = term439.
Proof. exact (@lem7006657 (NUMERAL 0) term364). Qed.
Lemma lem7006659 : term440 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7006660 (h1 : term440 = (BIT1 0)) : term439 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7006661 : (term440 = (BIT1 0)) = (term439 = True).
Proof. exact (prop_ext (fun h1 : term440 = (BIT1 0) => @lem7006660 h1) (fun h1 : term439 = True => @lem7006659)). Qed.
Lemma lem7006662 : term439 = True.
Proof. exact (EQ_MP (@lem7006661) (@lem7006659)). Qed.
Lemma lem7006663 : term438 = True.
Proof. exact (TRANS (@lem7006658) (@lem7006662)). Qed.
Lemma lem7006664 : True = term438.
Proof. exact (SYM (@lem7006663)). Qed.
Lemma lem7006665 : term438.
Proof. exact (EQ_MP (@lem7006664) (@lem0)). Qed.
Lemma lem7006666 : term442.
Proof. exact (@lem7006655 (@lem7006665)). Qed.
Lemma lem7006668 (m : nat) (n : nat) : (term437 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7006669 : term438 = term439.
Proof. exact (@lem7006668 (NUMERAL 0) term364). Qed.
Lemma lem7006670 : term440 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7006671 (h1 : term440 = (BIT1 0)) : term439 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7006672 : (term440 = (BIT1 0)) = (term439 = True).
Proof. exact (prop_ext (fun h1 : term440 = (BIT1 0) => @lem7006671 h1) (fun h1 : term439 = True => @lem7006670)). Qed.
Lemma lem7006673 : term439 = True.
Proof. exact (EQ_MP (@lem7006672) (@lem7006670)). Qed.
Lemma lem7006674 : term438 = True.
Proof. exact (TRANS (@lem7006669) (@lem7006673)). Qed.
Lemma lem7006675 : True = term438.
Proof. exact (SYM (@lem7006674)). Qed.
Lemma lem7006676 : term438.
Proof. exact (EQ_MP (@lem7006675) (@lem0)). Qed.
Lemma lem7006677 : term443.
Proof. exact (@lem7006666 (@lem7006676)). Qed.
Lemma lem7006679 (m : nat) (n : nat) : (term387 m n) = (term388 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7006680 : term389 = term390.
Proof. exact (@lem7006679 term364 term364). Qed.
Lemma lem7006681 : (term391 = (BIT1 0)) = (term392 = term364).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7006682 : term392 = term364.
Proof. exact (EQ_MP (@lem7006681) (@lem940073)). Qed.
Lemma lem7006683 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7006684 : term390 = term363.
Proof. exact (MK_COMB (@lem7006683) (@lem7006682)). Qed.
Lemma lem7006685 : term389 = term363.
Proof. exact (TRANS (@lem7006680) (@lem7006684)). Qed.
Lemma lem7006687 (m : nat) (n : nat) : (term417 m n) = (term418 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7006688 : term414 = term419.
Proof. exact (@lem7006687 term364 term364). Qed.
Lemma lem7006689 : (term391 = (BIT1 0)) = (term392 = term364).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7006690 : term392 = term364.
Proof. exact (EQ_MP (@lem7006689) (@lem940073)). Qed.
Lemma lem7006691 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7006692 : term390 = term363.
Proof. exact (MK_COMB (@lem7006691) (@lem7006690)). Qed.
Lemma lem7006693 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7006694 : term419 = term380.
Proof. exact (MK_COMB (@lem7006693) (@lem7006692)). Qed.
Lemma lem7006695 : term414 = term380.
Proof. exact (TRANS (@lem7006688) (@lem7006694)). Qed.
Lemma lem7006696 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7006697 : term444 = term432.
Proof. exact (MK_COMB (@lem7006696) (@lem7006695)). Qed.
Lemma lem7006698 : term445 = term434.
Proof. exact (MK_COMB (@lem7006697) (@lem7006685)). Qed.
Lemma lem7006700 (m : nat) : (term446 m) = term345.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7006701 : term434 = term345.
Proof. exact (@lem7006700 term364). Qed.
Lemma lem7006702 : term445 = term345.
Proof. exact (TRANS (@lem7006698) (@lem7006701)). Qed.
Lemma lem7006703 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7006704 : term447 = term448.
Proof. exact (MK_COMB (@lem7006703) (@lem7006702)). Qed.
Lemma lem7006705 : term363 = term363.
Proof. exact (eq_refl term363). Qed.
Lemma lem7006706 : term449 = term450.
Proof. exact (MK_COMB (@lem7006704) (@lem7006705)). Qed.
Lemma lem7006708 (x : nat) : (term451 x) = term345.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7006709 : term450 = term345.
Proof. exact (@lem7006708 term364). Qed.
Lemma lem7006710 : term449 = term345.
Proof. exact (TRANS (@lem7006706) (@lem7006709)). Qed.
Lemma lem7006712 (m : nat) (n : nat) : (term387 m n) = (term388 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7006713 : term389 = term390.
Proof. exact (@lem7006712 term364 term364). Qed.
Lemma lem7006714 : (term391 = (BIT1 0)) = (term392 = term364).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7006715 : term392 = term364.
Proof. exact (EQ_MP (@lem7006714) (@lem940073)). Qed.
Lemma lem7006716 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7006717 : term390 = term363.
Proof. exact (MK_COMB (@lem7006716) (@lem7006715)). Qed.
Lemma lem7006718 : term389 = term363.
Proof. exact (TRANS (@lem7006713) (@lem7006717)). Qed.
Lemma lem7006719 : term448 = term448.
Proof. exact (eq_refl term448). Qed.
Lemma lem7006720 : term452 = term450.
Proof. exact (MK_COMB (@lem7006719) (@lem7006718)). Qed.
Lemma lem7006722 (x : nat) : (term451 x) = term345.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7006723 : term450 = term345.
Proof. exact (@lem7006722 term364). Qed.
Lemma lem7006724 : term452 = term345.
Proof. exact (TRANS (@lem7006720) (@lem7006723)). Qed.
Lemma lem7006725 : term345 = term452.
Proof. exact (SYM (@lem7006724)). Qed.
Lemma lem7006726 : term449 = term452.
Proof. exact (TRANS (@lem7006710) (@lem7006725)). Qed.
Lemma lem7006727 : term435 = term377.
Proof. exact (@lem7006677 (@lem7006726)). Qed.
Lemma lem7006728 : term434 = term377.
Proof. exact (TRANS (@lem7006643) (@lem7006727)). Qed.
Lemma lem7006730 (x : real) : (term396 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7006731 : term377 = term345.
Proof. exact (@lem7006730 term345). Qed.
Lemma lem7006732 : term434 = term345.
Proof. exact (TRANS (@lem7006728) (@lem7006731)). Qed.
Lemma lem7006733 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7006734 : term453 = term448.
Proof. exact (MK_COMB (@lem7006733) (@lem7006732)). Qed.
Lemma lem7006735 (_93489 : int) : (real_of_int _93489) = (real_of_int _93489).
Proof. exact (eq_refl (real_of_int _93489)). Qed.
Lemma lem7006736 (_93489 : int) : (term431 _93489) = (term454 _93489).
Proof. exact (MK_COMB (@lem7006734) (@lem7006735 _93489)). Qed.
Lemma lem7006737 (_93489 : int) : (term489 _93489) = (term454 _93489).
Proof. exact (TRANS (@lem7006634 _93489) (@lem7006736 _93489)). Qed.
Lemma lem7006738 (_93489 : int) : (term454 _93489) = term345.
Proof. exact (@lem1982719 (real_of_int _93489)). Qed.
Lemma lem7006739 (_93489 : int) : (term489 _93489) = term345.
Proof. exact (TRANS (@lem7006737 _93489) (@lem7006738 _93489)). Qed.
Lemma lem7006740 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7006741 (_93489 : int) : (term490 _93489) = term456.
Proof. exact (MK_COMB (@lem7006740) (@lem7006739 _93489)). Qed.
Lemma lem7006742 : term380 = term380.
Proof. exact (eq_refl term380). Qed.
Lemma lem7006743 (_93489 : int) : (term488 _93489) = term457.
Proof. exact (MK_COMB (@lem7006741 _93489) (@lem7006742)). Qed.
Lemma lem7006744 (_93489 : int) : (term487 _93489) = term457.
Proof. exact (TRANS (@lem7006633 _93489) (@lem7006743 _93489)). Qed.
Lemma lem7006745 : term457 = term380.
Proof. exact (@lem1982721 term380). Qed.
Lemma lem7006746 (_93489 : int) : (term487 _93489) = term380.
Proof. exact (TRANS (@lem7006744 _93489) (@lem7006745)). Qed.
Lemma lem7006747 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7006748 (_93489 : int) : (term491 _93489) = term492.
Proof. exact (MK_COMB (@lem7006747) (@lem7006746 _93489)). Qed.
Lemma lem7006749 : term345 = term345.
Proof. exact (eq_refl term345). Qed.
Lemma lem7006750 (_93489 : int) : (term486 _93489) = term493.
Proof. exact (MK_COMB (@lem7006748 _93489) (@lem7006749)). Qed.
Lemma lem7006751 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : term493.
Proof. exact (EQ_MP (@lem7006750 _93489) (@lem7006632 _93490 _93489 h1)). Qed.
Lemma lem7006753 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7006754 : term493 = term494.
Proof. exact (@lem7006753 term345 term380). Qed.
Lemma lem7006756 (x : nat) : (term378 x) = (term379 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7006757 : term380 = term381.
Proof. exact (@lem7006756 term364). Qed.
Lemma lem7006759 (x : nat) : (real_of_num x) = (term376 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7006760 : term345 = term377.
Proof. exact (@lem7006759 (NUMERAL 0)). Qed.
Lemma lem7006761 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7006762 : term347 = term495.
Proof. exact (MK_COMB (@lem7006761) (@lem7006760)). Qed.
Lemma lem7006763 : term494 = term496.
Proof. exact (MK_COMB (@lem7006762) (@lem7006757)). Qed.
Lemma lem7006764 : term497.
Proof. exact (@lem1980026 term345 term363 term380 term363). Qed.
Lemma lem7006766 (m : nat) (n : nat) : (term437 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7006767 : term438 = term439.
Proof. exact (@lem7006766 (NUMERAL 0) term364). Qed.
Lemma lem7006768 : term440 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7006769 (h1 : term440 = (BIT1 0)) : term439 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7006770 : (term440 = (BIT1 0)) = (term439 = True).
Proof. exact (prop_ext (fun h1 : term440 = (BIT1 0) => @lem7006769 h1) (fun h1 : term439 = True => @lem7006768)). Qed.
Lemma lem7006771 : term439 = True.
Proof. exact (EQ_MP (@lem7006770) (@lem7006768)). Qed.
Lemma lem7006772 : term438 = True.
Proof. exact (TRANS (@lem7006767) (@lem7006771)). Qed.
Lemma lem7006773 : True = term438.
Proof. exact (SYM (@lem7006772)). Qed.
Lemma lem7006774 : term438.
Proof. exact (EQ_MP (@lem7006773) (@lem0)). Qed.
Lemma lem7006775 : term498.
Proof. exact (@lem7006764 (@lem7006774)). Qed.
Lemma lem7006777 (m : nat) (n : nat) : (term437 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7006778 : term438 = term439.
Proof. exact (@lem7006777 (NUMERAL 0) term364). Qed.
Lemma lem7006779 : term440 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7006780 (h1 : term440 = (BIT1 0)) : term439 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7006781 : (term440 = (BIT1 0)) = (term439 = True).
Proof. exact (prop_ext (fun h1 : term440 = (BIT1 0) => @lem7006780 h1) (fun h1 : term439 = True => @lem7006779)). Qed.
Lemma lem7006782 : term439 = True.
Proof. exact (EQ_MP (@lem7006781) (@lem7006779)). Qed.
Lemma lem7006783 : term438 = True.
Proof. exact (TRANS (@lem7006778) (@lem7006782)). Qed.
Lemma lem7006784 : True = term438.
Proof. exact (SYM (@lem7006783)). Qed.
Lemma lem7006785 : term438.
Proof. exact (EQ_MP (@lem7006784) (@lem0)). Qed.
Lemma lem7006786 : term496 = term499.
Proof. exact (@lem7006775 (@lem7006785)). Qed.
Lemma lem7006788 (m : nat) (n : nat) : (term417 m n) = (term418 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7006789 : term414 = term419.
Proof. exact (@lem7006788 term364 term364). Qed.
Lemma lem7006790 : (term391 = (BIT1 0)) = (term392 = term364).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7006791 : term392 = term364.
Proof. exact (EQ_MP (@lem7006790) (@lem940073)). Qed.
Lemma lem7006792 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7006793 : term390 = term363.
Proof. exact (MK_COMB (@lem7006792) (@lem7006791)). Qed.
Lemma lem7006794 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7006795 : term419 = term380.
Proof. exact (MK_COMB (@lem7006794) (@lem7006793)). Qed.
Lemma lem7006796 : term414 = term380.
Proof. exact (TRANS (@lem7006789) (@lem7006795)). Qed.
Lemma lem7006798 (x : nat) : (term451 x) = term345.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7006799 : term450 = term345.
Proof. exact (@lem7006798 term364). Qed.
Lemma lem7006800 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7006801 : term500 = term347.
Proof. exact (MK_COMB (@lem7006800) (@lem7006799)). Qed.
Lemma lem7006802 : term499 = term494.
Proof. exact (MK_COMB (@lem7006801) (@lem7006796)). Qed.
Lemma lem7006804 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7006805 : term494 = term503.
Proof. exact (@lem7006804 (NUMERAL 0) term364). Qed.
Lemma lem7006806 : term440 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7006807 (h1 : term440 = (BIT1 0)) : (term364 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7006808 : (term440 = (BIT1 0)) = ((term364 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term440 = (BIT1 0) => @lem7006807 h1) (fun h1 : (term364 = (NUMERAL 0)) = False => @lem7006806)). Qed.
Lemma lem7006809 : (term364 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7006808) (@lem7006806)). Qed.
Lemma lem7006810 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7006811 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7006812 : term504 = (and True).
Proof. exact (MK_COMB (@lem7006811) (@lem7006810)). Qed.
Lemma lem7006813 : term503 = (True /\ False).
Proof. exact (MK_COMB (@lem7006812) (@lem7006809)). Qed.
Lemma lem7006815 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7006816 : term503 = False.
Proof. exact (TRANS (@lem7006813) (@lem7006815)). Qed.
Lemma lem7006817 : term494 = False.
Proof. exact (TRANS (@lem7006805) (@lem7006816)). Qed.
Lemma lem7006818 : term499 = False.
Proof. exact (TRANS (@lem7006802) (@lem7006817)). Qed.
Lemma lem7006819 : term496 = False.
Proof. exact (TRANS (@lem7006786) (@lem7006818)). Qed.
Lemma lem7006820 : term494 = False.
Proof. exact (TRANS (@lem7006763) (@lem7006819)). Qed.
Lemma lem7006821 : term493 = False.
Proof. exact (TRANS (@lem7006754) (@lem7006820)). Qed.
Lemma lem7006822 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : False.
Proof. exact (EQ_MP (@lem7006821) (@lem7006751 _93490 _93489 h1)). Qed.
Lemma lem7006824 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : term463 _93490 _93489.
Proof. exact (h1). Qed.
Lemma lem7006825 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : (term463 _93490 _93489) = False.
Proof. exact (prop_ext (fun h2 : term463 _93490 _93489 => @lem7006822 _93490 _93489 h1) (fun h2 : False => @lem7006824 _93490 _93489 h1)). Qed.
Lemma lem7006826 (_93490 : int) (_93489 : int) (h1 : term463 _93490 _93489) : False.
Proof. exact (EQ_MP (@lem7006825 _93490 _93489 h1) (@lem7006824 _93490 _93489 h1)). Qed.
Lemma lem7006827 (_93489 : int) (_93490 : int) (h1 : term372 _93489 _93490) : term372 _93489 _93490.
Proof. exact (h1). Qed.
Lemma lem7006828 (_93489 : int) (_93490 : int) (h1 : term372 _93489 _93490) : term463 _93490 _93489.
Proof. exact (EQ_MP (@lem7006471 _93490 _93489) (@lem7006827 _93489 _93490 h1)). Qed.
Lemma lem7006829 (_93489 : int) (_93490 : int) (h1 : term372 _93489 _93490) : (term463 _93490 _93489) = False.
Proof. exact (prop_ext (fun h2 : term463 _93490 _93489 => @lem7006826 _93490 _93489 h2) (fun h2 : False => @lem7006828 _93489 _93490 h1)). Qed.
Lemma lem7006830 (_93489 : int) (_93490 : int) (h1 : term372 _93489 _93490) : False.
Proof. exact (EQ_MP (@lem7006829 _93489 _93490 h1) (@lem7006828 _93489 _93490 h1)). Qed.
Lemma lem7006831 (_93489 : int) (_93490 : int) : term505 _93489 _93490.
Proof. exact (fun h0 : term372 _93489 _93490 => @lem7006830 _93489 _93490 h0). Qed.
Lemma lem7006832 (_93489 : int) (_93490 : int) : term506 _93489 _93490.
Proof. exact (@lem1386578 (term507 _93489 _93490)). Qed.
Lemma lem7006835 (_93489 : int) (_93490 : int) : term507 _93489 _93490.
Proof. exact (@lem7006832 _93489 _93490 (@lem7006831 _93489 _93490)). Qed.
Lemma lem7006836 (_93489 : int) (_93490 : int) : (term371 _93489 _93490) = (term338 _93489 _93490).
Proof. exact (SYM (@lem7006118 _93489 _93490)). Qed.
Lemma lem7006837 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7006838 (_93489 : int) (_93490 : int) : (term507 _93489 _93490) = (term329 _93489 _93490).
Proof. exact (MK_COMB (@lem7006837) (@lem7006836 _93489 _93490)). Qed.
Lemma lem7006839 (_93489 : int) (_93490 : int) : term329 _93489 _93490.
Proof. exact (EQ_MP (@lem7006838 _93489 _93490) (@lem7006835 _93489 _93490)). Qed.
Lemma lem7006840 (_93489 : int) (_93490 : int) : term330 _93489 _93490.
Proof. exact (EQ_MP (@lem7006025 _93489 _93490) (@lem7006839 _93489 _93490)). Qed.
Lemma lem7006841 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term508 A u v f.
Proof. exact (@lem7006840 (term509 A v u f) (term510 A u v f)). Qed.
Lemma lem7006842 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term511 A u v f.
Proof. exact (@lem7006841 A u v f (@lem7006021 A v u f)). Qed.
Lemma lem7006843 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term324 A u v f.
Proof. exact (@lem7006842 A u v f (@lem7006024 A u v f)). Qed.
Lemma lem7006844 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term324 A u v f) = (term312 A v u f).
Proof. exact (SYM (@lem7006018 A u v f)). Qed.
Lemma lem7006845 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term312 A v u f.
Proof. exact (EQ_MP (@lem7006844 A v u f) (@lem7006843 A u v f)). Qed.
Lemma lem7006846 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term312 A v u f) = ((term312 A v u f) = True).
Proof. exact (@lem7 (term312 A v u f)). Qed.
Lemma lem7006847 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term312 A v u f) = True.
Proof. exact (EQ_MP (@lem7006846 A v u f) (@lem7006845 A v u f)). Qed.
Lemma lem7006848 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : True = (term312 A v u f).
Proof. exact (SYM (@lem7006847 A v u f)). Qed.
Lemma lem7006849 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term312 A v u f.
Proof. exact (EQ_MP (@lem7006848 A v u f) (@lem0)). Qed.
Lemma lem7006850 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : term280 A v u f.
Proof. exact (EQ_MP (@lem7005975 A u v f h1) (@lem7006849 A v u f)). Qed.
Lemma lem7006851 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) (h2 : (@nsum A v f) = (term132 A v u f)) : term248 A u v f.
Proof. exact (EQ_MP (@lem7005499 A v u f h2) (@lem7006850 A u v f h1)). Qed.
Lemma lem7006852 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : term512 A u v f.
Proof. exact (fun h0 : (@nsum A v f) = (term132 A v u f) => @lem7006851 A v u f h1 h0). Qed.
Lemma lem7006853 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : term513 A u v f.
Proof. exact (conj (@lem7005485 A v u) (@lem7006852 A u v f h1)). Qed.
Lemma lem7006854 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : term244 A u v f.
Proof. exact (@lem7005129 A u v f (@lem7006853 A u v f h1)). Qed.
Lemma lem7006855 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) (h2 : (@nsum A u f) = (term124 A u v f)) : term205 A u v f.
Proof. exact (EQ_MP (@lem7005126 A u v f h2) (@lem7006854 A u v f h1)). Qed.
Lemma lem7006856 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : term514 A u v f.
Proof. exact (fun h0 : (@nsum A u f) = (term124 A u v f) => @lem7006855 A u v f h1 h0). Qed.
Lemma lem7006857 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : term515 A u v f.
Proof. exact (conj (@lem7005112 A u v) (@lem7006856 A u v f h1)). Qed.
Lemma lem7006858 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term115 A u v f) : term208 A u v f.
Proof. exact (@lem7004756 A u v f (@lem7006857 A u v f h1)). Qed.
Lemma lem7006859 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : term115 A u v f) (h2 : @FINITE A u) (h3 : @FINITE A v) : term141 A u v f.
Proof. exact (EQ_MP (@lem7004753 A f u v h2 h3) (@lem7006858 A u v f h1)). Qed.
Lemma lem7006860 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : term115 A u v f) (h2 : @FINITE A u) (h3 : @FINITE A v) : term140 A u v f.
Proof. exact (EQ_MP (@lem7004093 A u v f) (@lem7006859 A f u v h1 h2 h3)). Qed.
Lemma lem7006861 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : term115 A u v f) (h2 : term112 A u v f) (h3 : @FINITE A u) (h4 : @FINITE A v) : term138 A u v f.
Proof. exact (@lem7006860 A f u v h1 h3 h4 (@lem7004022 A u v f h2)). Qed.
Lemma lem7006862 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : term115 A u v f) (h2 : term112 A u v f) (h3 : @FINITE A u) (h4 : @FINITE A v) : term137 A u v f.
Proof. exact (@lem7006861 A f u v h1 h2 h3 h4 (@lem7004025 A u v f h2)). Qed.
Lemma lem7006863 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : term115 A u v f) (h2 : @FINITE A u) (h3 : @FINITE A v) : term516 A u v f.
Proof. exact (fun h0 : term112 A u v f => @lem7006862 A f u v h1 h0 h2 h3). Qed.
Lemma lem7006864 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : term115 A u v f) (h2 : @FINITE A u) (h3 : @FINITE A v) : term137 A u v f.
Proof. exact (@lem7006863 A f u v h1 h2 h3 (@lem7004013 A u v f)). Qed.
Lemma lem7006865 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term113 A u v f) : term114 A u v f.
Proof. exact (proj2 (@lem7004014 A u v f h1)). Qed.
Lemma lem7006866 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term113 A u v f) : @FINITE A u.
Proof. exact (proj1 (@lem7004014 A u v f h1)). Qed.
Lemma lem7006867 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term114 A u v f) : term115 A u v f.
Proof. exact (proj2 (@lem7004015 A u v f h1)). Qed.
Lemma lem7006868 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term114 A u v f) : @FINITE A v.
Proof. exact (proj1 (@lem7004015 A u v f h1)). Qed.
Lemma lem7006869 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : term115 A u v f) (h2 : @FINITE A u) (h3 : @FINITE A v) : (term115 A u v f) = (term137 A u v f).
Proof. exact (prop_ext (fun h4 : term115 A u v f => @lem7006864 A f u v h1 h2 h3) (fun h4 : term137 A u v f => @lem7004017 A u v f h1)). Qed.
Lemma lem7006870 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : term115 A u v f) (h2 : @FINITE A u) (h3 : @FINITE A v) : term137 A u v f.
Proof. exact (EQ_MP (@lem7006869 A f u v h1 h2 h3) (@lem7004017 A u v f h1)). Qed.
Lemma lem7006871 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : term115 A u v f) (h2 : @FINITE A u) (h3 : @FINITE A v) : (@FINITE A v) = (term137 A u v f).
Proof. exact (prop_ext (fun h4 : @FINITE A v => @lem7006870 A f u v h1 h2 h3) (fun h4 : term137 A u v f => @lem7004018 A v h3)). Qed.
Lemma lem7006872 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : term115 A u v f) (h2 : @FINITE A u) (h3 : @FINITE A v) : term137 A u v f.
Proof. exact (EQ_MP (@lem7006871 A f u v h1 h2 h3) (@lem7004018 A v h3)). Qed.
Lemma lem7006873 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : @FINITE A u) (h2 : @FINITE A v) (h3 : term114 A u v f) : (term115 A u v f) = (term137 A u v f).
Proof. exact (prop_ext (fun h4 : term115 A u v f => @lem7006872 A f u v h4 h1 h2) (fun h4 : term137 A u v f => @lem7006867 A u v f h3)). Qed.
Lemma lem7006874 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : @FINITE A u) (h2 : @FINITE A v) (h3 : term114 A u v f) : term137 A u v f.
Proof. exact (EQ_MP (@lem7006873 A u v f h1 h2 h3) (@lem7006867 A u v f h3)). Qed.
Lemma lem7006875 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : @FINITE A u) (h2 : term114 A u v f) : (@FINITE A v) = (term137 A u v f).
Proof. exact (prop_ext (fun h3 : @FINITE A v => @lem7006874 A u v f h1 h3 h2) (fun h3 : term137 A u v f => @lem7006868 A u v f h2)). Qed.
Lemma lem7006876 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : @FINITE A u) (h2 : term114 A u v f) : term137 A u v f.
Proof. exact (EQ_MP (@lem7006875 A u v f h1 h2) (@lem7006868 A u v f h2)). Qed.
Lemma lem7006877 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : @FINITE A u) (h2 : term114 A u v f) : (@FINITE A u) = (term137 A u v f).
Proof. exact (prop_ext (fun h3 : @FINITE A u => @lem7006876 A u v f h1 h2) (fun h3 : term137 A u v f => @lem7004016 A u h1)). Qed.
Lemma lem7006878 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : @FINITE A u) (h2 : term114 A u v f) : term137 A u v f.
Proof. exact (EQ_MP (@lem7006877 A u v f h1 h2) (@lem7004016 A u h1)). Qed.
Lemma lem7006879 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : @FINITE A u) (h2 : term113 A u v f) : (term114 A u v f) = (term137 A u v f).
Proof. exact (prop_ext (fun h3 : term114 A u v f => @lem7006878 A u v f h1 h3) (fun h3 : term137 A u v f => @lem7006865 A u v f h2)). Qed.
Lemma lem7006880 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : @FINITE A u) (h2 : term113 A u v f) : term137 A u v f.
Proof. exact (EQ_MP (@lem7006879 A u v f h1 h2) (@lem7006865 A u v f h2)). Qed.
Lemma lem7006881 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term113 A u v f) : (@FINITE A u) = (term137 A u v f).
Proof. exact (prop_ext (fun h2 : @FINITE A u => @lem7006880 A u v f h2 h1) (fun h2 : term137 A u v f => @lem7006866 A u v f h1)). Qed.
Lemma lem7006882 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term113 A u v f) : term137 A u v f.
Proof. exact (EQ_MP (@lem7006881 A u v f h1) (@lem7006866 A u v f h1)). Qed.
Lemma lem7006883 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term517 A u v f.
Proof. exact (fun h0 : term113 A u v f => @lem7006882 A u v f h0). Qed.
Lemma lem7006888 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term518 A u v.
Proof. exact (fun f : A -> nat => @lem7006883 A u v f). Qed.
Lemma lem7006893 {A : Type'} (u : A -> Prop) : term519 A u.
Proof. exact (fun v : A -> Prop => @lem7006888 A u v). Qed.
Lemma lem7006898 {A : Type'} : term520 A.
Proof. exact (fun u : A -> Prop => @lem7006893 A u). Qed.
