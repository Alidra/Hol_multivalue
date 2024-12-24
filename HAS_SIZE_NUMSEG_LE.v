Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_NUMSEG_LE_term_abbrevs.
Require Import ADD1_spec.
Require Import HAS_SIZE_NUMSEG_LT_spec.
Require Import LT_SUC_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem4621863 (m : nat) (n : nat) (h1 : (term0 m n) = (Peano.le m n)) : (term0 m n) = (Peano.le m n).
Proof. exact (h1). Qed.
Lemma lem4621864 (m : nat) (n : nat) (h1 : (term0 m n) = (Peano.le m n)) : (Peano.le m n) = (term0 m n).
Proof. exact (SYM (@lem4621863 m n h1)). Qed.
Lemma lem4621865 (m : nat) (n : nat) (h1 : (Peano.le m n) = (term0 m n)) : (Peano.le m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem4621866 (m : nat) (n : nat) (h1 : (Peano.le m n) = (term0 m n)) : (term0 m n) = (Peano.le m n).
Proof. exact (SYM (@lem4621865 m n h1)). Qed.
Lemma lem4621867 (m : nat) (n : nat) : ((term0 m n) = (Peano.le m n)) = ((Peano.le m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.le m n) => @lem4621864 m n h1) (fun h1 : (Peano.le m n) = (term0 m n) => @lem4621866 m n h1)). Qed.
Lemma lem4621868 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem4621867 m n)). Qed.
Lemma lem4621869 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621870 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem4621869) (@lem4621868 m)). Qed.
Lemma lem4621871 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem4621870 m)). Qed.
Lemma lem4621872 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621873 : term7 = term8.
Proof. exact (MK_COMB (@lem4621872) (@lem4621871)). Qed.
Lemma lem4621874 : term8.
Proof. exact (EQ_MP (@lem4621873) (@lem91305)). Qed.
Lemma lem4621875 (m : nat) : term9 m.
Proof. exact (@lem80621 m). Qed.
Lemma lem4621876 (m : nat) : (term9 m) = ((S m) = (term10 m)).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem4621878 (n : nat) : term11 n.
Proof. exact (@lem4621384 n). Qed.
Lemma lem4621879 (n : nat) : (term11 n) = (term12 n).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem4621880 (n : nat) : term12 n.
Proof. exact (EQ_MP (@lem4621879 n) (@lem4621878 n)). Qed.
Lemma lem4621881 (n : nat) : (term12 n) = ((term12 n) = True).
Proof. exact (@lem7 (term12 n)). Qed.
Lemma lem4621883 (m : nat) : term13 m.
Proof. exact (@lem4621874 m). Qed.
Lemma lem4621884 (m : nat) : (term13 m) = (term4 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem4621885 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem4621884 m) (@lem4621883 m)). Qed.
Lemma lem4621886 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem4621885 m n). Qed.
Lemma lem4621887 (m : nat) (n : nat) : (term14 m n) = ((Peano.le m n) = (term0 m n)).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem4621898 (m : nat) (n : nat) : (Peano.le m n) = (term0 m n).
Proof. exact (EQ_MP (@lem4621887 m n) (@lem4621886 m n)). Qed.
Lemma lem4621900 (m : nat) : (S m) = (term10 m).
Proof. exact (EQ_MP (@lem4621876 m) (@lem4621875 m)). Qed.
Lemma lem4621901 (n : nat) : (S n) = (term10 n).
Proof. exact (@lem4621900 n). Qed.
Lemma lem4621902 (m : nat) : (Peano.lt m) = (Peano.lt m).
Proof. exact (eq_refl (Peano.lt m)). Qed.
Lemma lem4621903 (m : nat) (n : nat) : (term0 m n) = (term15 m n).
Proof. exact (MK_COMB (@lem4621902 m) (@lem4621901 n)). Qed.
Lemma lem4621904 (m : nat) (n : nat) : (Peano.le m n) = (term15 m n).
Proof. exact (TRANS (@lem4621898 m n) (@lem4621903 m n)). Qed.
Lemma lem4621905 (GEN_PVAR_188 : nat) : (@SETSPEC nat GEN_PVAR_188) = (@SETSPEC nat GEN_PVAR_188).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_188)). Qed.
Lemma lem4621906 (GEN_PVAR_188 : nat) (m : nat) (n : nat) : (term16 GEN_PVAR_188 m n) = (term17 GEN_PVAR_188 m n).
Proof. exact (MK_COMB (@lem4621905 GEN_PVAR_188) (@lem4621904 m n)). Qed.
Lemma lem4621907 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem4621908 (GEN_PVAR_188 : nat) (n : nat) (m : nat) : (term18 GEN_PVAR_188 n m) = (term19 GEN_PVAR_188 n m).
Proof. exact (MK_COMB (@lem4621906 GEN_PVAR_188 m n) (@lem4621907 m)). Qed.
Lemma lem4621909 (GEN_PVAR_188 : nat) (n : nat) : (term20 GEN_PVAR_188 n) = (term21 GEN_PVAR_188 n).
Proof. exact (fun_ext (fun m : nat => @lem4621908 GEN_PVAR_188 n m)). Qed.
Lemma lem4621910 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4621911 (GEN_PVAR_188 : nat) (n : nat) : (term22 GEN_PVAR_188 n) = (term23 GEN_PVAR_188 n).
Proof. exact (MK_COMB (@lem4621910) (@lem4621909 GEN_PVAR_188 n)). Qed.
Lemma lem4621916 (n : nat) : (term24 n) = (term25 n).
Proof. exact (fun_ext (fun GEN_PVAR_188 : nat => @lem4621911 GEN_PVAR_188 n)). Qed.
Lemma lem4621917 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem4621918 (n : nat) : (term26 n) = (term27 n).
Proof. exact (MK_COMB (@lem4621917) (@lem4621916 n)). Qed.
Lemma lem4621919 : (@HAS_SIZE nat) = (@HAS_SIZE nat).
Proof. exact (eq_refl (@HAS_SIZE nat)). Qed.
Lemma lem4621920 (n : nat) : (term28 n) = (term29 n).
Proof. exact (MK_COMB (@lem4621919) (@lem4621918 n)). Qed.
Lemma lem4621921 (n : nat) : (term10 n) = (term10 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem4621922 (n : nat) : (term30 n) = (term31 n).
Proof. exact (MK_COMB (@lem4621920 n) (@lem4621921 n)). Qed.
Lemma lem4621924 (n : nat) : (term12 n) = True.
Proof. exact (EQ_MP (@lem4621881 n) (@lem4621880 n)). Qed.
Lemma lem4621925 (n : nat) : (term31 n) = True.
Proof. exact (@lem4621924 (term10 n)). Qed.
Lemma lem4621926 (n : nat) : (term30 n) = True.
Proof. exact (TRANS (@lem4621922 n) (@lem4621925 n)). Qed.
Lemma lem4621927 : term32 = term33.
Proof. exact (fun_ext (fun n : nat => @lem4621926 n)). Qed.
Lemma lem4621928 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621929 : term34 = term35.
Proof. exact (MK_COMB (@lem4621928) (@lem4621927)). Qed.
Lemma lem4621931 {A : Type'} (t : Prop) : (term36 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4621932 (t : Prop) : (term37 t) = t.
Proof. exact (@lem4621931 nat t). Qed.
Lemma lem4621933 : term35 = True.
Proof. exact (@lem4621932 True). Qed.
Lemma lem4621934 : term34 = True.
Proof. exact (TRANS (@lem4621929) (@lem4621933)). Qed.
Lemma lem4621935 : True = term34.
Proof. exact (SYM (@lem4621934)). Qed.
Lemma lem4621936 : term34.
Proof. exact (EQ_MP (@lem4621935) (@lem0)). Qed.
