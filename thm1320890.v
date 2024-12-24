Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1320890_term_abbrevs.
Require Import NADD_MUL_LID_spec.
Require Import thm1317782_spec.
Require Import thm1317787_spec.
Require Import thm1318030_spec.
Require Import thm1318035_spec.
Require Import thm1318759_spec.
Require Import thm1318760_spec.
Require Import thm1318766_spec.
Require Import thm1318767_spec.
Lemma lem1320837 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1320838 (x : nadd) : (term1 x) = ((term2 x) = (term0 x)).
Proof. exact (@lem1320837 (term3 x) x). Qed.
Lemma lem1320842 (x : nadd) (y : nadd) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem1318035 x y) (@lem1318030 x y)). Qed.
Lemma lem1320843 (x : nadd) : (term2 x) = (term6 x).
Proof. exact (@lem1320842 term7 x). Qed.
Lemma lem1320845 (m : nat) : (term8 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1320846 : term9 = term10.
Proof. exact (@lem1320845 term11). Qed.
Lemma lem1320847 : hreal_mul = hreal_mul.
Proof. exact (eq_refl hreal_mul). Qed.
Lemma lem1320848 : term12 = term13.
Proof. exact (MK_COMB (@lem1320847) (@lem1320846)). Qed.
Lemma lem1320849 (x : nadd) : (term0 x) = (term0 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1320850 (x : nadd) : (term6 x) = (term14 x).
Proof. exact (MK_COMB (@lem1320848) (@lem1320849 x)). Qed.
Lemma lem1320851 (x : nadd) : (term2 x) = (term14 x).
Proof. exact (TRANS (@lem1320843 x) (@lem1320850 x)). Qed.
Lemma lem1320852 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1320853 (x : nadd) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem1320852) (@lem1320851 x)). Qed.
Lemma lem1320854 (x : nadd) : (term0 x) = (term0 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1320855 (x : nadd) : ((term2 x) = (term0 x)) = ((term14 x) = (term0 x)).
Proof. exact (MK_COMB (@lem1320853 x) (@lem1320854 x)). Qed.
Lemma lem1320858 (x : nadd) : (term1 x) = ((term14 x) = (term0 x)).
Proof. exact (TRANS (@lem1320838 x) (@lem1320855 x)). Qed.
Lemma lem1320859 : term17 = term18.
Proof. exact (fun_ext (fun x : nadd => @lem1320858 x)). Qed.
Lemma lem1320860 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320861 : term19 = term20.
Proof. exact (MK_COMB (@lem1320860) (@lem1320859)). Qed.
Lemma lem1320867 (P : hreal -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1320868 : term23 = term24.
Proof. exact (@lem1320867 term25). Qed.
Lemma lem1320869 (x : nadd) : (term26 x) = ((term14 x) = (term0 x)).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1320870 : term27 = term18.
Proof. exact (fun_ext (fun x : nadd => @lem1320869 x)). Qed.
Lemma lem1320871 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320872 : term23 = term20.
Proof. exact (MK_COMB (@lem1320871) (@lem1320870)). Qed.
Lemma lem1320873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1320874 : term28 = term29.
Proof. exact (MK_COMB (@lem1320873) (@lem1320872)). Qed.
Lemma lem1320875 (x : hreal) : (term30 x) = ((term31 x) = x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1320876 : term32 = term25.
Proof. exact (fun_ext (fun x : hreal => @lem1320875 x)). Qed.
Lemma lem1320877 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1320878 : term24 = term33.
Proof. exact (MK_COMB (@lem1320877) (@lem1320876)). Qed.
Lemma lem1320879 : (term23 = term24) = (term20 = term33).
Proof. exact (MK_COMB (@lem1320874) (@lem1320878)). Qed.
Lemma lem1320880 : term20 = term33.
Proof. exact (EQ_MP (@lem1320879) (@lem1320868)). Qed.
Lemma lem1320889 : term19 = term33.
Proof. exact (TRANS (@lem1320861) (@lem1320880)). Qed.
Lemma lem1320890 : term33.
Proof. exact (EQ_MP (@lem1320889) (@lem1278627)). Qed.
