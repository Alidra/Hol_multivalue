Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7598119_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_spec.
Require Import dimindex_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18964_spec.
Require Import thm18965_spec.
Require Import thm19490_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Lemma lem7594703 {A : Type'} (n : nat) (h1 : term0 A n) : term0 A n.
Proof. exact (h1). Qed.
Lemma lem7594706 {A : Type'} : term1 A.
Proof. exact (@lem3863773 A). Qed.
Lemma lem7594711 {_100044 A : Type'} (n : nat) (h1 : term2 _100044 A n) : term2 _100044 A n.
Proof. exact (h1). Qed.
Lemma lem7594712 {_100044 A : Type'} (n : nat) : term3 _100044 A n.
Proof. exact (fun h0 : term2 _100044 A n => @lem7594711 _100044 A n h0). Qed.
Lemma lem7594713 {_100044 A : Type'} (n : nat) (h1 : term3 _100044 A n) : term3 _100044 A n.
Proof. exact (h1). Qed.
Lemma lem7594714 {_100044 A : Type'} (n : nat) (h1 : term2 _100044 A n) : term2 _100044 A n.
Proof. exact (h1). Qed.
Lemma lem7594715 {_100044 A : Type'} (n : nat) (h1 : term2 _100044 A n) (h2 : term3 _100044 A n) : term2 _100044 A n.
Proof. exact (@lem7594713 _100044 A n h2 (@lem7594714 _100044 A n h1)). Qed.
Lemma lem7594716 {_100044 A : Type'} (n : nat) (h1 : term2 _100044 A n) : term4 _100044 A n.
Proof. exact (fun h0 : term3 _100044 A n => @lem7594715 _100044 A n h1 h0). Qed.
Lemma lem7594717 {_100044 A : Type'} (n : nat) (h1 : term3 _100044 A n) : term3 _100044 A n.
Proof. exact (h1). Qed.
Lemma lem7594718 {_100044 A : Type'} (n : nat) (h1 : term2 _100044 A n) (h2 : term3 _100044 A n) : term2 _100044 A n.
Proof. exact (@lem7594716 _100044 A n h1 (@lem7594717 _100044 A n h2)). Qed.
Lemma lem7594719 {_100044 A : Type'} (n : nat) (h1 : term3 _100044 A n) : term3 _100044 A n.
Proof. exact (fun h0 : term2 _100044 A n => @lem7594718 _100044 A n h0 h1). Qed.
Lemma lem7594720 {_100044 A : Type'} (n : nat) : term5 _100044 A n.
Proof. exact (fun h0 : term3 _100044 A n => @lem7594719 _100044 A n h0). Qed.
Lemma lem7594723 {_100044 A : Type'} (n : nat) : term3 _100044 A n.
Proof. exact (@lem7594720 _100044 A n (@lem7594712 _100044 A n)). Qed.
Lemma lem7594724 {_100044 A : Type'} (n : nat) : term3 _100044 A n.
Proof. exact (@lem7594723 _100044 A n). Qed.
Lemma lem7594758 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7594759 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (@lem7594758 (term8 A)). Qed.
Lemma lem7594764 {A : Type'} : (term9 A) = (term9 A).
Proof. exact (eq_refl (term9 A)). Qed.
Lemma lem7594765 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (MK_COMB (@lem7594764 A) (@lem7594759 A)). Qed.
Lemma lem7594768 {_100044 : Type'} : (term9 _100044) = (term9 _100044).
Proof. exact (eq_refl (term9 _100044)). Qed.
Lemma lem7594769 {_100044 A : Type'} : (term12 _100044 A) = (term13 _100044 A).
Proof. exact (MK_COMB (@lem7594768 _100044) (@lem7594765 A)). Qed.
Lemma lem7594772 {A : Type'} (n : nat) : (term14 A n) = (term14 A n).
Proof. exact (eq_refl (term14 A n)). Qed.
Lemma lem7594773 {_100044 A : Type'} (n : nat) : (term2 _100044 A n) = (term15 _100044 A n).
Proof. exact (MK_COMB (@lem7594772 A n) (@lem7594769 _100044 A)). Qed.
Lemma lem7594776 {_100044 A : Type'} : (term16 _100044 A) = (term17 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7594773 _100044 A n)). Qed.
Lemma lem7594777 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7594786 {_100044 A : Type'} : (term18 _100044 A) = (term19 _100044 A).
Proof. exact (MK_COMB (@lem7594777) (@lem7594776 _100044 A)). Qed.
Lemma lem7594822 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (@FINITE A (@UNIV A)) = False.
Proof. exact (h1). Qed.
Lemma lem7594823 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7594824 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term20 A) = (@COND nat False).
Proof. exact (MK_COMB (@lem7594823) (@lem7594822 A h1)). Qed.
Lemma lem7594825 {A : Type'} : (@CARD A (@UNIV A)) = (@CARD A (@UNIV A)).
Proof. exact (eq_refl (@CARD A (@UNIV A))). Qed.
Lemma lem7594826 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term21 A) = (term22 A).
Proof. exact (MK_COMB (@lem7594824 A h1) (@lem7594825 A)). Qed.
Lemma lem7594827 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7594828 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term24 A) = (term25 A).
Proof. exact (MK_COMB (@lem7594826 A h1) (@lem7594827)). Qed.
Lemma lem7594830 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7594831 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7594830 nat t1 t2). Qed.
Lemma lem7594832 {A : Type'} : (term25 A) = term23.
Proof. exact (@lem7594831 (@CARD A (@UNIV A)) term23). Qed.
Lemma lem7594833 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term24 A) = term23.
Proof. exact (TRANS (@lem7594828 A h1) (@lem7594832 A)). Qed.
Lemma lem7594834 {A : Type'} (s : A -> Prop) : (term26 A s) = (term26 A s).
Proof. exact (eq_refl (term26 A s)). Qed.
Lemma lem7594835 {A : Type'} (s : A -> Prop) (h1 : (@FINITE A (@UNIV A)) = False) : ((@dimindex A s) = (term24 A)) = ((@dimindex A s) = term23).
Proof. exact (MK_COMB (@lem7594834 A s) (@lem7594833 A h1)). Qed.
Lemma lem7594838 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term27 A) = (term28 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7594835 A s h1)). Qed.
Lemma lem7594839 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7594840 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term8 A) = (term29 A).
Proof. exact (MK_COMB (@lem7594839 A) (@lem7594838 A h1)). Qed.
Lemma lem7594845 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7594846 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term7 A) = (term30 A).
Proof. exact (MK_COMB (@lem7594845) (@lem7594840 A h1)). Qed.
Lemma lem7594847 {A : Type'} : (term9 A) = (term9 A).
Proof. exact (eq_refl (term9 A)). Qed.
Lemma lem7594848 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term11 A) = (term31 A).
Proof. exact (MK_COMB (@lem7594847 A) (@lem7594846 A h1)). Qed.
Lemma lem7594851 {_100044 : Type'} : (term9 _100044) = (term9 _100044).
Proof. exact (eq_refl (term9 _100044)). Qed.
Lemma lem7594852 {_100044 A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term13 _100044 A) = (term32 _100044 A).
Proof. exact (MK_COMB (@lem7594851 _100044) (@lem7594848 A h1)). Qed.
Lemma lem7594855 {A : Type'} (n : nat) : (term14 A n) = (term14 A n).
Proof. exact (eq_refl (term14 A n)). Qed.
Lemma lem7594856 {_100044 A : Type'} (n : nat) (h1 : (@FINITE A (@UNIV A)) = False) : (term15 _100044 A n) = (term33 _100044 A n).
Proof. exact (MK_COMB (@lem7594855 A n) (@lem7594852 _100044 A h1)). Qed.
Lemma lem7594859 {_100044 A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term17 _100044 A) = (term34 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7594856 _100044 A n h1)). Qed.
Lemma lem7594860 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7594861 {_100044 A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term19 _100044 A) = (term35 _100044 A).
Proof. exact (MK_COMB (@lem7594860) (@lem7594859 _100044 A h1)). Qed.
Lemma lem7594866 {_100044 A : Type'} : term36 _100044 A.
Proof. exact (fun h0 : (@FINITE A (@UNIV A)) = False => @lem7594861 _100044 A h0). Qed.
Lemma lem7594900 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (@FINITE A (@UNIV A)) = True.
Proof. exact (h1). Qed.
Lemma lem7594901 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7594902 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term20 A) = (@COND nat True).
Proof. exact (MK_COMB (@lem7594901) (@lem7594900 A h1)). Qed.
Lemma lem7594903 {A : Type'} : (@CARD A (@UNIV A)) = (@CARD A (@UNIV A)).
Proof. exact (eq_refl (@CARD A (@UNIV A))). Qed.
Lemma lem7594904 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term21 A) = (term37 A).
Proof. exact (MK_COMB (@lem7594902 A h1) (@lem7594903 A)). Qed.
Lemma lem7594905 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7594906 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term24 A) = (term38 A).
Proof. exact (MK_COMB (@lem7594904 A h1) (@lem7594905)). Qed.
Lemma lem7594908 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7594909 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7594908 nat t2 t1). Qed.
Lemma lem7594910 {A : Type'} : (term38 A) = (@CARD A (@UNIV A)).
Proof. exact (@lem7594909 term23 (@CARD A (@UNIV A))). Qed.
Lemma lem7594911 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term24 A) = (@CARD A (@UNIV A)).
Proof. exact (TRANS (@lem7594906 A h1) (@lem7594910 A)). Qed.
Lemma lem7594912 {A : Type'} (s : A -> Prop) : (term26 A s) = (term26 A s).
Proof. exact (eq_refl (term26 A s)). Qed.
Lemma lem7594913 {A : Type'} (s : A -> Prop) (h1 : (@FINITE A (@UNIV A)) = True) : ((@dimindex A s) = (term24 A)) = ((@dimindex A s) = (@CARD A (@UNIV A))).
Proof. exact (MK_COMB (@lem7594912 A s) (@lem7594911 A h1)). Qed.
Lemma lem7594916 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term27 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7594913 A s h1)). Qed.
Lemma lem7594917 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7594918 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term8 A) = (term40 A).
Proof. exact (MK_COMB (@lem7594917 A) (@lem7594916 A h1)). Qed.
Lemma lem7594923 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7594924 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term7 A) = (term41 A).
Proof. exact (MK_COMB (@lem7594923) (@lem7594918 A h1)). Qed.
Lemma lem7594925 {A : Type'} : (term9 A) = (term9 A).
Proof. exact (eq_refl (term9 A)). Qed.
Lemma lem7594926 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term11 A) = (term42 A).
Proof. exact (MK_COMB (@lem7594925 A) (@lem7594924 A h1)). Qed.
Lemma lem7594929 {_100044 : Type'} : (term9 _100044) = (term9 _100044).
Proof. exact (eq_refl (term9 _100044)). Qed.
Lemma lem7594930 {_100044 A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term13 _100044 A) = (term43 _100044 A).
Proof. exact (MK_COMB (@lem7594929 _100044) (@lem7594926 A h1)). Qed.
Lemma lem7594933 {A : Type'} (n : nat) : (term14 A n) = (term14 A n).
Proof. exact (eq_refl (term14 A n)). Qed.
Lemma lem7594934 {_100044 A : Type'} (n : nat) (h1 : (@FINITE A (@UNIV A)) = True) : (term15 _100044 A n) = (term44 _100044 A n).
Proof. exact (MK_COMB (@lem7594933 A n) (@lem7594930 _100044 A h1)). Qed.
Lemma lem7594937 {_100044 A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term17 _100044 A) = (term45 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7594934 _100044 A n h1)). Qed.
Lemma lem7594938 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7594939 {_100044 A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term19 _100044 A) = (term46 _100044 A).
Proof. exact (MK_COMB (@lem7594938) (@lem7594937 _100044 A h1)). Qed.
Lemma lem7594944 {_100044 A : Type'} : term47 _100044 A.
Proof. exact (fun h0 : (@FINITE A (@UNIV A)) = True => @lem7594939 _100044 A h0). Qed.
Lemma lem7594945 {_100044 A : Type'} : term48 _100044 A.
Proof. exact (conj (@lem7594866 _100044 A) (@lem7594944 _100044 A)). Qed.
Lemma lem7594947 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term49 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem7594948 {_100044 A : Type'} : term50 _100044 A.
Proof. exact (@lem7594947 (term19 _100044 A) (term46 _100044 A) (@FINITE A (@UNIV A)) (term35 _100044 A)). Qed.
Lemma lem7594963 {_100044 A : Type'} : (term19 _100044 A) = (term51 _100044 A).
Proof. exact (@lem7594948 _100044 A (@lem7594945 _100044 A)). Qed.
Lemma lem7594964 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = term23) = ((@dimindex A s) = term23).
Proof. exact (eq_refl ((@dimindex A s) = term23)). Qed.
Lemma lem7594965 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7594964 A s)). Qed.
Lemma lem7594966 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7594967 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (MK_COMB (@lem7594966 A) (@lem7594965 A)). Qed.
Lemma lem7594968 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7594969 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (MK_COMB (@lem7594968) (@lem7594967 A)). Qed.
Lemma lem7594978 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term52 A s n)) = ((@HAS_SIZE A s n) = (term52 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE A s n) = (term52 A s n))). Qed.
Lemma lem7594979 {A : Type'} (s : A -> Prop) : (term53 A s) = (term53 A s).
Proof. exact (fun_ext (fun n : nat => @lem7594978 A s n)). Qed.
Lemma lem7594980 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7594981 {A : Type'} (s : A -> Prop) : (term54 A s) = (term54 A s).
Proof. exact (MK_COMB (@lem7594980) (@lem7594979 A s)). Qed.
Lemma lem7594982 {A : Type'} : (term55 A) = (term55 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7594981 A s)). Qed.
Lemma lem7594983 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7594984 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (MK_COMB (@lem7594983 A) (@lem7594982 A)). Qed.
Lemma lem7594985 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7594986 {A : Type'} : (term9 A) = (term9 A).
Proof. exact (MK_COMB (@lem7594985) (@lem7594984 A)). Qed.
Lemma lem7594987 {A : Type'} : (term31 A) = (term31 A).
Proof. exact (MK_COMB (@lem7594986 A) (@lem7594969 A)). Qed.
Lemma lem7594996 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term52 _100044 s n)) = ((@HAS_SIZE _100044 s n) = (term52 _100044 s n)).
Proof. exact (eq_refl ((@HAS_SIZE _100044 s n) = (term52 _100044 s n))). Qed.
Lemma lem7594997 {_100044 : Type'} (s : _100044 -> Prop) : (term53 _100044 s) = (term53 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7594996 _100044 s n)). Qed.
Lemma lem7594998 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7594999 {_100044 : Type'} (s : _100044 -> Prop) : (term54 _100044 s) = (term54 _100044 s).
Proof. exact (MK_COMB (@lem7594998) (@lem7594997 _100044 s)). Qed.
Lemma lem7595000 {_100044 : Type'} : (term55 _100044) = (term55 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7594999 _100044 s)). Qed.
Lemma lem7595001 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7595002 {_100044 : Type'} : (term1 _100044) = (term1 _100044).
Proof. exact (MK_COMB (@lem7595001 _100044) (@lem7595000 _100044)). Qed.
Lemma lem7595003 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7595004 {_100044 : Type'} : (term9 _100044) = (term9 _100044).
Proof. exact (MK_COMB (@lem7595003) (@lem7595002 _100044)). Qed.
Lemma lem7595005 {_100044 A : Type'} : (term32 _100044 A) = (term32 _100044 A).
Proof. exact (MK_COMB (@lem7595004 _100044) (@lem7594987 A)). Qed.
Lemma lem7595014 {A : Type'} (n : nat) : (term14 A n) = (term14 A n).
Proof. exact (eq_refl (term14 A n)). Qed.
Lemma lem7595015 {_100044 A : Type'} (n : nat) : (term33 _100044 A n) = (term33 _100044 A n).
Proof. exact (MK_COMB (@lem7595014 A n) (@lem7595005 _100044 A)). Qed.
Lemma lem7595016 {_100044 A : Type'} : (term34 _100044 A) = (term34 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7595015 _100044 A n)). Qed.
Lemma lem7595017 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7595018 {_100044 A : Type'} : (term35 _100044 A) = (term35 _100044 A).
Proof. exact (MK_COMB (@lem7595017) (@lem7595016 _100044 A)). Qed.
Lemma lem7595021 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (eq_refl (term56 A)). Qed.
Lemma lem7595022 {_100044 A : Type'} : (term57 _100044 A) = (term57 _100044 A).
Proof. exact (MK_COMB (@lem7595021 A) (@lem7595018 _100044 A)). Qed.
Lemma lem7595023 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (@CARD A (@UNIV A))) = ((@dimindex A s) = (@CARD A (@UNIV A))).
Proof. exact (eq_refl ((@dimindex A s) = (@CARD A (@UNIV A)))). Qed.
Lemma lem7595024 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7595023 A s)). Qed.
Lemma lem7595025 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7595026 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (MK_COMB (@lem7595025 A) (@lem7595024 A)). Qed.
Lemma lem7595027 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7595028 {A : Type'} : (term41 A) = (term41 A).
Proof. exact (MK_COMB (@lem7595027) (@lem7595026 A)). Qed.
Lemma lem7595037 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term52 A s n)) = ((@HAS_SIZE A s n) = (term52 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE A s n) = (term52 A s n))). Qed.
Lemma lem7595038 {A : Type'} (s : A -> Prop) : (term53 A s) = (term53 A s).
Proof. exact (fun_ext (fun n : nat => @lem7595037 A s n)). Qed.
Lemma lem7595039 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7595040 {A : Type'} (s : A -> Prop) : (term54 A s) = (term54 A s).
Proof. exact (MK_COMB (@lem7595039) (@lem7595038 A s)). Qed.
Lemma lem7595041 {A : Type'} : (term55 A) = (term55 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7595040 A s)). Qed.
Lemma lem7595042 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7595043 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (MK_COMB (@lem7595042 A) (@lem7595041 A)). Qed.
Lemma lem7595044 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7595045 {A : Type'} : (term9 A) = (term9 A).
Proof. exact (MK_COMB (@lem7595044) (@lem7595043 A)). Qed.
Lemma lem7595046 {A : Type'} : (term42 A) = (term42 A).
Proof. exact (MK_COMB (@lem7595045 A) (@lem7595028 A)). Qed.
Lemma lem7595055 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term52 _100044 s n)) = ((@HAS_SIZE _100044 s n) = (term52 _100044 s n)).
Proof. exact (eq_refl ((@HAS_SIZE _100044 s n) = (term52 _100044 s n))). Qed.
Lemma lem7595056 {_100044 : Type'} (s : _100044 -> Prop) : (term53 _100044 s) = (term53 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7595055 _100044 s n)). Qed.
Lemma lem7595057 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7595058 {_100044 : Type'} (s : _100044 -> Prop) : (term54 _100044 s) = (term54 _100044 s).
Proof. exact (MK_COMB (@lem7595057) (@lem7595056 _100044 s)). Qed.
Lemma lem7595059 {_100044 : Type'} : (term55 _100044) = (term55 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7595058 _100044 s)). Qed.
Lemma lem7595060 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7595061 {_100044 : Type'} : (term1 _100044) = (term1 _100044).
Proof. exact (MK_COMB (@lem7595060 _100044) (@lem7595059 _100044)). Qed.
Lemma lem7595062 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7595063 {_100044 : Type'} : (term9 _100044) = (term9 _100044).
Proof. exact (MK_COMB (@lem7595062) (@lem7595061 _100044)). Qed.
Lemma lem7595064 {_100044 A : Type'} : (term43 _100044 A) = (term43 _100044 A).
Proof. exact (MK_COMB (@lem7595063 _100044) (@lem7595046 A)). Qed.
Lemma lem7595073 {A : Type'} (n : nat) : (term14 A n) = (term14 A n).
Proof. exact (eq_refl (term14 A n)). Qed.
Lemma lem7595074 {_100044 A : Type'} (n : nat) : (term44 _100044 A n) = (term44 _100044 A n).
Proof. exact (MK_COMB (@lem7595073 A n) (@lem7595064 _100044 A)). Qed.
Lemma lem7595075 {_100044 A : Type'} : (term45 _100044 A) = (term45 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7595074 _100044 A n)). Qed.
Lemma lem7595076 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7595077 {_100044 A : Type'} : (term46 _100044 A) = (term46 _100044 A).
Proof. exact (MK_COMB (@lem7595076) (@lem7595075 _100044 A)). Qed.
Lemma lem7595082 {A : Type'} : (term58 A) = (term58 A).
Proof. exact (eq_refl (term58 A)). Qed.
Lemma lem7595083 {_100044 A : Type'} : (term59 _100044 A) = (term59 _100044 A).
Proof. exact (MK_COMB (@lem7595082 A) (@lem7595077 _100044 A)). Qed.
Lemma lem7595084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595085 {_100044 A : Type'} : (term60 _100044 A) = (term60 _100044 A).
Proof. exact (MK_COMB (@lem7595084) (@lem7595083 _100044 A)). Qed.
Lemma lem7595086 {_100044 A : Type'} : (term51 _100044 A) = (term51 _100044 A).
Proof. exact (MK_COMB (@lem7595085 _100044 A) (@lem7595022 _100044 A)). Qed.
Lemma lem7595087 {_100044 A : Type'} : (term61 _100044 A) = (term61 _100044 A).
Proof. exact (eq_refl (term61 _100044 A)). Qed.
Lemma lem7595088 {_100044 A : Type'} : ((term19 _100044 A) = (term51 _100044 A)) = ((term19 _100044 A) = (term51 _100044 A)).
Proof. exact (MK_COMB (@lem7595087 _100044 A) (@lem7595086 _100044 A)). Qed.
Lemma lem7595089 {_100044 A : Type'} : (term19 _100044 A) = (term51 _100044 A).
Proof. exact (EQ_MP (@lem7595088 _100044 A) (@lem7594963 _100044 A)). Qed.
Lemma lem7595194 {_100044 A : Type'} : (term18 _100044 A) = (term51 _100044 A).
Proof. exact (TRANS (@lem7594786 _100044 A) (@lem7595089 _100044 A)). Qed.
Lemma lem7595195 {_100044 A : Type'} : (term51 _100044 A) = (term18 _100044 A).
Proof. exact (SYM (@lem7595194 _100044 A)). Qed.
Lemma lem7595197 (p : Prop) : p = (term62 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7595198 {_100044 A : Type'} : (term51 _100044 A) = (term63 _100044 A).
Proof. exact (@lem7595197 (term51 _100044 A)). Qed.
Lemma lem7595199 {_100044 A : Type'} : (term63 _100044 A) = (term51 _100044 A).
Proof. exact (SYM (@lem7595198 _100044 A)). Qed.
Lemma lem7595200 {_100044 A : Type'} (h1 : term64 _100044 A) : term64 _100044 A.
Proof. exact (h1). Qed.
Lemma lem7595203 {A : Type'} : (term65 A) = (@FINITE A (@UNIV A)).
Proof. exact (@lem16933 (@FINITE A (@UNIV A))). Qed.
Lemma lem7595210 {A : Type'} (n : nat) : (term0 A n) = (term66 A n).
Proof. exact (@lem17362 (@HAS_SIZE A (@UNIV A) n) ((@dimindex A (@UNIV A)) = n)). Qed.
Lemma lem7595221 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term67 _100044 s n) = (term68 _100044 s n).
Proof. exact (@lem17045 (@FINITE _100044 s) ((@CARD _100044 s) = n)). Qed.
Lemma lem7595227 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term69 _100044 s n) = (term69 _100044 s n).
Proof. exact (eq_refl (term69 _100044 s n)). Qed.
Lemma lem7595229 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term70 _100044 s n) = (term70 _100044 s n).
Proof. exact (eq_refl (term70 _100044 s n)). Qed.
Lemma lem7595230 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term71 _100044 s n) = (term72 _100044 s n).
Proof. exact (MK_COMB (@lem7595229 _100044 s n) (@lem7595221 _100044 s n)). Qed.
Lemma lem7595231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595232 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term73 _100044 s n) = (term74 _100044 s n).
Proof. exact (MK_COMB (@lem7595231) (@lem7595230 _100044 s n)). Qed.
Lemma lem7595233 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term75 _100044 s n) = (term76 _100044 s n).
Proof. exact (MK_COMB (@lem7595232 _100044 s n) (@lem7595227 _100044 s n)). Qed.
Lemma lem7595234 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term52 _100044 s n)) = (term75 _100044 s n).
Proof. exact (@lem17784 (@HAS_SIZE _100044 s n) (term52 _100044 s n)). Qed.
Lemma lem7595235 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term52 _100044 s n)) = (term76 _100044 s n).
Proof. exact (TRANS (@lem7595234 _100044 s n) (@lem7595233 _100044 s n)). Qed.
Lemma lem7595236 {_100044 : Type'} (s : _100044 -> Prop) : (term53 _100044 s) = (term77 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7595235 _100044 s n)). Qed.
Lemma lem7595237 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7595238 {_100044 : Type'} (s : _100044 -> Prop) : (term54 _100044 s) = (term78 _100044 s).
Proof. exact (MK_COMB (@lem7595237) (@lem7595236 _100044 s)). Qed.
Lemma lem7595239 {_100044 : Type'} : (term55 _100044) = (term79 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7595238 _100044 s)). Qed.
Lemma lem7595240 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7595241 {_100044 : Type'} : (term1 _100044) = (term80 _100044).
Proof. exact (MK_COMB (@lem7595240 _100044) (@lem7595239 _100044)). Qed.
Lemma lem7595252 {A : Type'} (s : A -> Prop) (n : nat) : (term67 A s n) = (term68 A s n).
Proof. exact (@lem17045 (@FINITE A s) ((@CARD A s) = n)). Qed.
Lemma lem7595258 {A : Type'} (s : A -> Prop) (n : nat) : (term69 A s n) = (term69 A s n).
Proof. exact (eq_refl (term69 A s n)). Qed.
Lemma lem7595260 {A : Type'} (s : A -> Prop) (n : nat) : (term70 A s n) = (term70 A s n).
Proof. exact (eq_refl (term70 A s n)). Qed.
Lemma lem7595261 {A : Type'} (s : A -> Prop) (n : nat) : (term71 A s n) = (term72 A s n).
Proof. exact (MK_COMB (@lem7595260 A s n) (@lem7595252 A s n)). Qed.
Lemma lem7595262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595263 {A : Type'} (s : A -> Prop) (n : nat) : (term73 A s n) = (term74 A s n).
Proof. exact (MK_COMB (@lem7595262) (@lem7595261 A s n)). Qed.
Lemma lem7595264 {A : Type'} (s : A -> Prop) (n : nat) : (term75 A s n) = (term76 A s n).
Proof. exact (MK_COMB (@lem7595263 A s n) (@lem7595258 A s n)). Qed.
Lemma lem7595265 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term52 A s n)) = (term75 A s n).
Proof. exact (@lem17784 (@HAS_SIZE A s n) (term52 A s n)). Qed.
Lemma lem7595266 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term52 A s n)) = (term76 A s n).
Proof. exact (TRANS (@lem7595265 A s n) (@lem7595264 A s n)). Qed.
Lemma lem7595267 {A : Type'} (s : A -> Prop) : (term53 A s) = (term77 A s).
Proof. exact (fun_ext (fun n : nat => @lem7595266 A s n)). Qed.
Lemma lem7595268 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7595269 {A : Type'} (s : A -> Prop) : (term54 A s) = (term78 A s).
Proof. exact (MK_COMB (@lem7595268) (@lem7595267 A s)). Qed.
Lemma lem7595270 {A : Type'} : (term55 A) = (term79 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7595269 A s)). Qed.
Lemma lem7595271 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7595272 {A : Type'} : (term1 A) = (term80 A).
Proof. exact (MK_COMB (@lem7595271 A) (@lem7595270 A)). Qed.
Lemma lem7595273 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (@CARD A (@UNIV A))) = ((@dimindex A s) = (@CARD A (@UNIV A))).
Proof. exact (eq_refl ((@dimindex A s) = (@CARD A (@UNIV A)))). Qed.
Lemma lem7595274 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7595273 A s)). Qed.
Lemma lem7595275 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7595276 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (MK_COMB (@lem7595275 A) (@lem7595274 A)). Qed.
Lemma lem7595277 {A : Type'} : (term81 A) = (term40 A).
Proof. exact (@lem16933 (term40 A)). Qed.
Lemma lem7595278 {A : Type'} : (term81 A) = (term40 A).
Proof. exact (TRANS (@lem7595277 A) (@lem7595276 A)). Qed.
Lemma lem7595279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595280 {A : Type'} : (term82 A) = (term83 A).
Proof. exact (MK_COMB (@lem7595279) (@lem7595272 A)). Qed.
Lemma lem7595281 {A : Type'} : (term84 A) = (term85 A).
Proof. exact (MK_COMB (@lem7595280 A) (@lem7595278 A)). Qed.
Lemma lem7595282 {A : Type'} : (term86 A) = (term84 A).
Proof. exact (@lem17362 (term1 A) (term41 A)). Qed.
Lemma lem7595283 {A : Type'} : (term86 A) = (term85 A).
Proof. exact (TRANS (@lem7595282 A) (@lem7595281 A)). Qed.
Lemma lem7595284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595285 {_100044 : Type'} : (term82 _100044) = (term83 _100044).
Proof. exact (MK_COMB (@lem7595284) (@lem7595241 _100044)). Qed.
Lemma lem7595286 {_100044 A : Type'} : (term87 _100044 A) = (term88 _100044 A).
Proof. exact (MK_COMB (@lem7595285 _100044) (@lem7595283 A)). Qed.
Lemma lem7595287 {_100044 A : Type'} : (term89 _100044 A) = (term87 _100044 A).
Proof. exact (@lem17362 (term1 _100044) (term42 A)). Qed.
Lemma lem7595288 {_100044 A : Type'} : (term89 _100044 A) = (term88 _100044 A).
Proof. exact (TRANS (@lem7595287 _100044 A) (@lem7595286 _100044 A)). Qed.
Lemma lem7595289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595290 {A : Type'} (n : nat) : (term90 A n) = (term91 A n).
Proof. exact (MK_COMB (@lem7595289) (@lem7595210 A n)). Qed.
Lemma lem7595291 {_100044 A : Type'} (n : nat) : (term92 _100044 A n) = (term93 _100044 A n).
Proof. exact (MK_COMB (@lem7595290 A n) (@lem7595288 _100044 A)). Qed.
Lemma lem7595292 {_100044 A : Type'} (n : nat) : (term94 _100044 A n) = (term92 _100044 A n).
Proof. exact (@lem17362 (term0 A n) (term43 _100044 A)). Qed.
Lemma lem7595293 {_100044 A : Type'} (n : nat) : (term94 _100044 A n) = (term93 _100044 A n).
Proof. exact (TRANS (@lem7595292 _100044 A n) (@lem7595291 _100044 A n)). Qed.
Lemma lem7595294 (P : nat -> Prop) : (term95 P) = (term96 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7595295 {_100044 A : Type'} : (term97 _100044 A) = (term98 _100044 A).
Proof. exact (@lem7595294 (term45 _100044 A)). Qed.
Lemma lem7595296 {_100044 A : Type'} (n : nat) : (term99 _100044 A n) = (term44 _100044 A n).
Proof. exact (eq_refl (term99 _100044 A n)). Qed.
Lemma lem7595297 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7595298 {_100044 A : Type'} (n : nat) : (term100 _100044 A n) = (term94 _100044 A n).
Proof. exact (MK_COMB (@lem7595297) (@lem7595296 _100044 A n)). Qed.
Lemma lem7595299 {_100044 A : Type'} (n : nat) : (term100 _100044 A n) = (term93 _100044 A n).
Proof. exact (TRANS (@lem7595298 _100044 A n) (@lem7595293 _100044 A n)). Qed.
Lemma lem7595300 {_100044 A : Type'} : (term101 _100044 A) = (term102 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7595299 _100044 A n)). Qed.
Lemma lem7595301 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7595302 {_100044 A : Type'} : (term98 _100044 A) = (term103 _100044 A).
Proof. exact (MK_COMB (@lem7595301) (@lem7595300 _100044 A)). Qed.
Lemma lem7595303 {_100044 A : Type'} : (term97 _100044 A) = (term103 _100044 A).
Proof. exact (TRANS (@lem7595295 _100044 A) (@lem7595302 _100044 A)). Qed.
Lemma lem7595304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595305 {A : Type'} : (term104 A) = (term105 A).
Proof. exact (MK_COMB (@lem7595304) (@lem7595203 A)). Qed.
Lemma lem7595306 {_100044 A : Type'} : (term106 _100044 A) = (term107 _100044 A).
Proof. exact (MK_COMB (@lem7595305 A) (@lem7595303 _100044 A)). Qed.
Lemma lem7595307 {_100044 A : Type'} : (term108 _100044 A) = (term106 _100044 A).
Proof. exact (@lem17160 (term109 A) (term46 _100044 A)). Qed.
Lemma lem7595308 {_100044 A : Type'} : (term108 _100044 A) = (term107 _100044 A).
Proof. exact (TRANS (@lem7595307 _100044 A) (@lem7595306 _100044 A)). Qed.
Lemma lem7595316 {A : Type'} (n : nat) : (term0 A n) = (term66 A n).
Proof. exact (@lem17362 (@HAS_SIZE A (@UNIV A) n) ((@dimindex A (@UNIV A)) = n)). Qed.
Lemma lem7595327 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term67 _100044 s n) = (term68 _100044 s n).
Proof. exact (@lem17045 (@FINITE _100044 s) ((@CARD _100044 s) = n)). Qed.
Lemma lem7595333 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term69 _100044 s n) = (term69 _100044 s n).
Proof. exact (eq_refl (term69 _100044 s n)). Qed.
Lemma lem7595335 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term70 _100044 s n) = (term70 _100044 s n).
Proof. exact (eq_refl (term70 _100044 s n)). Qed.
Lemma lem7595336 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term71 _100044 s n) = (term72 _100044 s n).
Proof. exact (MK_COMB (@lem7595335 _100044 s n) (@lem7595327 _100044 s n)). Qed.
Lemma lem7595337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595338 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term73 _100044 s n) = (term74 _100044 s n).
Proof. exact (MK_COMB (@lem7595337) (@lem7595336 _100044 s n)). Qed.
Lemma lem7595339 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term75 _100044 s n) = (term76 _100044 s n).
Proof. exact (MK_COMB (@lem7595338 _100044 s n) (@lem7595333 _100044 s n)). Qed.
Lemma lem7595340 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term52 _100044 s n)) = (term75 _100044 s n).
Proof. exact (@lem17784 (@HAS_SIZE _100044 s n) (term52 _100044 s n)). Qed.
Lemma lem7595341 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term52 _100044 s n)) = (term76 _100044 s n).
Proof. exact (TRANS (@lem7595340 _100044 s n) (@lem7595339 _100044 s n)). Qed.
Lemma lem7595342 {_100044 : Type'} (s : _100044 -> Prop) : (term53 _100044 s) = (term77 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7595341 _100044 s n)). Qed.
Lemma lem7595343 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7595344 {_100044 : Type'} (s : _100044 -> Prop) : (term54 _100044 s) = (term78 _100044 s).
Proof. exact (MK_COMB (@lem7595343) (@lem7595342 _100044 s)). Qed.
Lemma lem7595345 {_100044 : Type'} : (term55 _100044) = (term79 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7595344 _100044 s)). Qed.
Lemma lem7595346 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7595347 {_100044 : Type'} : (term1 _100044) = (term80 _100044).
Proof. exact (MK_COMB (@lem7595346 _100044) (@lem7595345 _100044)). Qed.
Lemma lem7595358 {A : Type'} (s : A -> Prop) (n : nat) : (term67 A s n) = (term68 A s n).
Proof. exact (@lem17045 (@FINITE A s) ((@CARD A s) = n)). Qed.
Lemma lem7595364 {A : Type'} (s : A -> Prop) (n : nat) : (term69 A s n) = (term69 A s n).
Proof. exact (eq_refl (term69 A s n)). Qed.
Lemma lem7595366 {A : Type'} (s : A -> Prop) (n : nat) : (term70 A s n) = (term70 A s n).
Proof. exact (eq_refl (term70 A s n)). Qed.
Lemma lem7595367 {A : Type'} (s : A -> Prop) (n : nat) : (term71 A s n) = (term72 A s n).
Proof. exact (MK_COMB (@lem7595366 A s n) (@lem7595358 A s n)). Qed.
Lemma lem7595368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595369 {A : Type'} (s : A -> Prop) (n : nat) : (term73 A s n) = (term74 A s n).
Proof. exact (MK_COMB (@lem7595368) (@lem7595367 A s n)). Qed.
Lemma lem7595370 {A : Type'} (s : A -> Prop) (n : nat) : (term75 A s n) = (term76 A s n).
Proof. exact (MK_COMB (@lem7595369 A s n) (@lem7595364 A s n)). Qed.
Lemma lem7595371 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term52 A s n)) = (term75 A s n).
Proof. exact (@lem17784 (@HAS_SIZE A s n) (term52 A s n)). Qed.
Lemma lem7595372 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term52 A s n)) = (term76 A s n).
Proof. exact (TRANS (@lem7595371 A s n) (@lem7595370 A s n)). Qed.
Lemma lem7595373 {A : Type'} (s : A -> Prop) : (term53 A s) = (term77 A s).
Proof. exact (fun_ext (fun n : nat => @lem7595372 A s n)). Qed.
Lemma lem7595374 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7595375 {A : Type'} (s : A -> Prop) : (term54 A s) = (term78 A s).
Proof. exact (MK_COMB (@lem7595374) (@lem7595373 A s)). Qed.
Lemma lem7595376 {A : Type'} : (term55 A) = (term79 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7595375 A s)). Qed.
Lemma lem7595377 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7595378 {A : Type'} : (term1 A) = (term80 A).
Proof. exact (MK_COMB (@lem7595377 A) (@lem7595376 A)). Qed.
Lemma lem7595379 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = term23) = ((@dimindex A s) = term23).
Proof. exact (eq_refl ((@dimindex A s) = term23)). Qed.
Lemma lem7595380 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7595379 A s)). Qed.
Lemma lem7595381 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7595382 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (MK_COMB (@lem7595381 A) (@lem7595380 A)). Qed.
Lemma lem7595383 {A : Type'} : (term110 A) = (term29 A).
Proof. exact (@lem16933 (term29 A)). Qed.
Lemma lem7595384 {A : Type'} : (term110 A) = (term29 A).
Proof. exact (TRANS (@lem7595383 A) (@lem7595382 A)). Qed.
Lemma lem7595385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595386 {A : Type'} : (term82 A) = (term83 A).
Proof. exact (MK_COMB (@lem7595385) (@lem7595378 A)). Qed.
Lemma lem7595387 {A : Type'} : (term111 A) = (term112 A).
Proof. exact (MK_COMB (@lem7595386 A) (@lem7595384 A)). Qed.
Lemma lem7595388 {A : Type'} : (term113 A) = (term111 A).
Proof. exact (@lem17362 (term1 A) (term30 A)). Qed.
Lemma lem7595389 {A : Type'} : (term113 A) = (term112 A).
Proof. exact (TRANS (@lem7595388 A) (@lem7595387 A)). Qed.
Lemma lem7595390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595391 {_100044 : Type'} : (term82 _100044) = (term83 _100044).
Proof. exact (MK_COMB (@lem7595390) (@lem7595347 _100044)). Qed.
Lemma lem7595392 {_100044 A : Type'} : (term114 _100044 A) = (term115 _100044 A).
Proof. exact (MK_COMB (@lem7595391 _100044) (@lem7595389 A)). Qed.
Lemma lem7595393 {_100044 A : Type'} : (term116 _100044 A) = (term114 _100044 A).
Proof. exact (@lem17362 (term1 _100044) (term31 A)). Qed.
Lemma lem7595394 {_100044 A : Type'} : (term116 _100044 A) = (term115 _100044 A).
Proof. exact (TRANS (@lem7595393 _100044 A) (@lem7595392 _100044 A)). Qed.
Lemma lem7595395 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595396 {A : Type'} (n : nat) : (term90 A n) = (term91 A n).
Proof. exact (MK_COMB (@lem7595395) (@lem7595316 A n)). Qed.
Lemma lem7595397 {_100044 A : Type'} (n : nat) : (term117 _100044 A n) = (term118 _100044 A n).
Proof. exact (MK_COMB (@lem7595396 A n) (@lem7595394 _100044 A)). Qed.
Lemma lem7595398 {_100044 A : Type'} (n : nat) : (term119 _100044 A n) = (term117 _100044 A n).
Proof. exact (@lem17362 (term0 A n) (term32 _100044 A)). Qed.
Lemma lem7595399 {_100044 A : Type'} (n : nat) : (term119 _100044 A n) = (term118 _100044 A n).
Proof. exact (TRANS (@lem7595398 _100044 A n) (@lem7595397 _100044 A n)). Qed.
Lemma lem7595400 (P : nat -> Prop) : (term95 P) = (term96 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7595401 {_100044 A : Type'} : (term120 _100044 A) = (term121 _100044 A).
Proof. exact (@lem7595400 (term34 _100044 A)). Qed.
Lemma lem7595402 {_100044 A : Type'} (n : nat) : (term122 _100044 A n) = (term33 _100044 A n).
Proof. exact (eq_refl (term122 _100044 A n)). Qed.
Lemma lem7595403 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7595404 {_100044 A : Type'} (n : nat) : (term123 _100044 A n) = (term119 _100044 A n).
Proof. exact (MK_COMB (@lem7595403) (@lem7595402 _100044 A n)). Qed.
Lemma lem7595405 {_100044 A : Type'} (n : nat) : (term123 _100044 A n) = (term118 _100044 A n).
Proof. exact (TRANS (@lem7595404 _100044 A n) (@lem7595399 _100044 A n)). Qed.
Lemma lem7595406 {_100044 A : Type'} : (term124 _100044 A) = (term125 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7595405 _100044 A n)). Qed.
Lemma lem7595407 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7595408 {_100044 A : Type'} : (term121 _100044 A) = (term126 _100044 A).
Proof. exact (MK_COMB (@lem7595407) (@lem7595406 _100044 A)). Qed.
Lemma lem7595409 {_100044 A : Type'} : (term120 _100044 A) = (term126 _100044 A).
Proof. exact (TRANS (@lem7595401 _100044 A) (@lem7595408 _100044 A)). Qed.
Lemma lem7595411 {A : Type'} : (term127 A) = (term127 A).
Proof. exact (eq_refl (term127 A)). Qed.
Lemma lem7595412 {_100044 A : Type'} : (term128 _100044 A) = (term129 _100044 A).
Proof. exact (MK_COMB (@lem7595411 A) (@lem7595409 _100044 A)). Qed.
Lemma lem7595413 {_100044 A : Type'} : (term130 _100044 A) = (term128 _100044 A).
Proof. exact (@lem17160 (@FINITE A (@UNIV A)) (term35 _100044 A)). Qed.
Lemma lem7595414 {_100044 A : Type'} : (term130 _100044 A) = (term129 _100044 A).
Proof. exact (TRANS (@lem7595413 _100044 A) (@lem7595412 _100044 A)). Qed.
Lemma lem7595415 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7595416 {_100044 A : Type'} : (term131 _100044 A) = (term132 _100044 A).
Proof. exact (MK_COMB (@lem7595415) (@lem7595308 _100044 A)). Qed.
Lemma lem7595417 {_100044 A : Type'} : (term133 _100044 A) = (term134 _100044 A).
Proof. exact (MK_COMB (@lem7595416 _100044 A) (@lem7595414 _100044 A)). Qed.
Lemma lem7595418 {_100044 A : Type'} : (term64 _100044 A) = (term133 _100044 A).
Proof. exact (@lem17045 (term59 _100044 A) (term57 _100044 A)). Qed.
Lemma lem7595419 {_100044 A : Type'} : (term64 _100044 A) = (term134 _100044 A).
Proof. exact (TRANS (@lem7595418 _100044 A) (@lem7595417 _100044 A)). Qed.
Lemma lem7595441 {A : Type'} (P : A -> Prop) (Q : Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem7595442 (P : nat -> Prop) (Q : Prop) : (term137 P Q) = (term138 P Q).
Proof. exact (@lem7595441 nat P Q). Qed.
Lemma lem7595443 {_100044 A : Type'} : (term139 _100044 A) = (term140 _100044 A).
Proof. exact (@lem7595442 (term141 A) (term88 _100044 A)). Qed.
Lemma lem7595444 {A : Type'} (n : nat) : (term142 A n) = (term66 A n).
Proof. exact (eq_refl (term142 A n)). Qed.
Lemma lem7595445 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595446 {A : Type'} (n : nat) : (term143 A n) = (term91 A n).
Proof. exact (MK_COMB (@lem7595445) (@lem7595444 A n)). Qed.
Lemma lem7595447 {_100044 A : Type'} : (term88 _100044 A) = (term88 _100044 A).
Proof. exact (eq_refl (term88 _100044 A)). Qed.
Lemma lem7595448 {_100044 A : Type'} (n : nat) : (term144 _100044 A n) = (term93 _100044 A n).
Proof. exact (MK_COMB (@lem7595446 A n) (@lem7595447 _100044 A)). Qed.
Lemma lem7595449 {_100044 A : Type'} : (term145 _100044 A) = (term102 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7595448 _100044 A n)). Qed.
Lemma lem7595450 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7595451 {_100044 A : Type'} : (term139 _100044 A) = (term103 _100044 A).
Proof. exact (MK_COMB (@lem7595450) (@lem7595449 _100044 A)). Qed.
Lemma lem7595452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7595453 {_100044 A : Type'} : (term146 _100044 A) = (term147 _100044 A).
Proof. exact (MK_COMB (@lem7595452) (@lem7595451 _100044 A)). Qed.
Lemma lem7595454 {A : Type'} (n : nat) : (term142 A n) = (term66 A n).
Proof. exact (eq_refl (term142 A n)). Qed.
Lemma lem7595455 {A : Type'} : (term148 A) = (term141 A).
Proof. exact (fun_ext (fun n : nat => @lem7595454 A n)). Qed.
Lemma lem7595456 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7595457 {A : Type'} : (term149 A) = (term150 A).
Proof. exact (MK_COMB (@lem7595456) (@lem7595455 A)). Qed.
Lemma lem7595458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595459 {A : Type'} : (term151 A) = (term152 A).
Proof. exact (MK_COMB (@lem7595458) (@lem7595457 A)). Qed.
Lemma lem7595460 {_100044 A : Type'} : (term88 _100044 A) = (term88 _100044 A).
Proof. exact (eq_refl (term88 _100044 A)). Qed.
Lemma lem7595461 {_100044 A : Type'} : (term140 _100044 A) = (term153 _100044 A).
Proof. exact (MK_COMB (@lem7595459 A) (@lem7595460 _100044 A)). Qed.
Lemma lem7595462 {_100044 A : Type'} : ((term139 _100044 A) = (term140 _100044 A)) = ((term103 _100044 A) = (term153 _100044 A)).
Proof. exact (MK_COMB (@lem7595453 _100044 A) (@lem7595461 _100044 A)). Qed.
Lemma lem7595463 {_100044 A : Type'} : (term103 _100044 A) = (term153 _100044 A).
Proof. exact (EQ_MP (@lem7595462 _100044 A) (@lem7595443 _100044 A)). Qed.
Lemma lem7595517 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7595518 (P : nat -> Prop) (Q : nat -> Prop) : (term156 P Q) = (term157 P Q).
Proof. exact (@lem7595517 nat P Q). Qed.
Lemma lem7595519 {_100044 : Type'} (s : _100044 -> Prop) : (term158 _100044 s) = (term159 _100044 s).
Proof. exact (@lem7595518 (term160 _100044 s) (term161 _100044 s)). Qed.
Lemma lem7595520 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term162 _100044 s n) = (term72 _100044 s n).
Proof. exact (eq_refl (term162 _100044 s n)). Qed.
Lemma lem7595521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595522 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term163 _100044 s n) = (term74 _100044 s n).
Proof. exact (MK_COMB (@lem7595521) (@lem7595520 _100044 s n)). Qed.
Lemma lem7595523 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term164 _100044 s n) = (term69 _100044 s n).
Proof. exact (eq_refl (term164 _100044 s n)). Qed.
Lemma lem7595524 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term165 _100044 s n) = (term76 _100044 s n).
Proof. exact (MK_COMB (@lem7595522 _100044 s n) (@lem7595523 _100044 s n)). Qed.
Lemma lem7595525 {_100044 : Type'} (s : _100044 -> Prop) : (term166 _100044 s) = (term77 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7595524 _100044 s n)). Qed.
Lemma lem7595526 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7595527 {_100044 : Type'} (s : _100044 -> Prop) : (term158 _100044 s) = (term78 _100044 s).
Proof. exact (MK_COMB (@lem7595526) (@lem7595525 _100044 s)). Qed.
Lemma lem7595528 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7595529 {_100044 : Type'} (s : _100044 -> Prop) : (term167 _100044 s) = (term168 _100044 s).
Proof. exact (MK_COMB (@lem7595528) (@lem7595527 _100044 s)). Qed.
Lemma lem7595530 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term162 _100044 s n) = (term72 _100044 s n).
Proof. exact (eq_refl (term162 _100044 s n)). Qed.
Lemma lem7595531 {_100044 : Type'} (s : _100044 -> Prop) : (term169 _100044 s) = (term160 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7595530 _100044 s n)). Qed.
Lemma lem7595532 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7595533 {_100044 : Type'} (s : _100044 -> Prop) : (term170 _100044 s) = (term171 _100044 s).
Proof. exact (MK_COMB (@lem7595532) (@lem7595531 _100044 s)). Qed.
Lemma lem7595534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595535 {_100044 : Type'} (s : _100044 -> Prop) : (term172 _100044 s) = (term173 _100044 s).
Proof. exact (MK_COMB (@lem7595534) (@lem7595533 _100044 s)). Qed.
Lemma lem7595536 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term164 _100044 s n) = (term69 _100044 s n).
Proof. exact (eq_refl (term164 _100044 s n)). Qed.
Lemma lem7595537 {_100044 : Type'} (s : _100044 -> Prop) : (term174 _100044 s) = (term161 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7595536 _100044 s n)). Qed.
Lemma lem7595538 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7595539 {_100044 : Type'} (s : _100044 -> Prop) : (term175 _100044 s) = (term176 _100044 s).
Proof. exact (MK_COMB (@lem7595538) (@lem7595537 _100044 s)). Qed.
Lemma lem7595540 {_100044 : Type'} (s : _100044 -> Prop) : (term159 _100044 s) = (term177 _100044 s).
Proof. exact (MK_COMB (@lem7595535 _100044 s) (@lem7595539 _100044 s)). Qed.
Lemma lem7595541 {_100044 : Type'} (s : _100044 -> Prop) : ((term158 _100044 s) = (term159 _100044 s)) = ((term78 _100044 s) = (term177 _100044 s)).
Proof. exact (MK_COMB (@lem7595529 _100044 s) (@lem7595540 _100044 s)). Qed.
Lemma lem7595542 {_100044 : Type'} (s : _100044 -> Prop) : (term78 _100044 s) = (term177 _100044 s).
Proof. exact (EQ_MP (@lem7595541 _100044 s) (@lem7595519 _100044 s)). Qed.
Lemma lem7595639 {_100044 : Type'} : (term79 _100044) = (term178 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7595542 _100044 s)). Qed.
Lemma lem7595640 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7595641 {_100044 : Type'} : (term80 _100044) = (term179 _100044).
Proof. exact (MK_COMB (@lem7595640 _100044) (@lem7595639 _100044)). Qed.
Lemma lem7595643 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7595644 {_100044 : Type'} (P : type686 _100044) (Q : type686 _100044) : (term180 _100044 P Q) = (term181 _100044 P Q).
Proof. exact (@lem7595643 (_100044 -> Prop) P Q). Qed.
Lemma lem7595645 {_100044 : Type'} : (term182 _100044) = (term183 _100044).
Proof. exact (@lem7595644 _100044 (term184 _100044) (term185 _100044)). Qed.
Lemma lem7595646 {_100044 : Type'} (s : _100044 -> Prop) : (term186 _100044 s) = (term171 _100044 s).
Proof. exact (eq_refl (term186 _100044 s)). Qed.
Lemma lem7595647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595648 {_100044 : Type'} (s : _100044 -> Prop) : (term187 _100044 s) = (term173 _100044 s).
Proof. exact (MK_COMB (@lem7595647) (@lem7595646 _100044 s)). Qed.
Lemma lem7595649 {_100044 : Type'} (s : _100044 -> Prop) : (term188 _100044 s) = (term176 _100044 s).
Proof. exact (eq_refl (term188 _100044 s)). Qed.
Lemma lem7595650 {_100044 : Type'} (s : _100044 -> Prop) : (term189 _100044 s) = (term177 _100044 s).
Proof. exact (MK_COMB (@lem7595648 _100044 s) (@lem7595649 _100044 s)). Qed.
Lemma lem7595651 {_100044 : Type'} : (term190 _100044) = (term178 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7595650 _100044 s)). Qed.
Lemma lem7595652 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7595653 {_100044 : Type'} : (term182 _100044) = (term179 _100044).
Proof. exact (MK_COMB (@lem7595652 _100044) (@lem7595651 _100044)). Qed.
Lemma lem7595654 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7595655 {_100044 : Type'} : (term191 _100044) = (term192 _100044).
Proof. exact (MK_COMB (@lem7595654) (@lem7595653 _100044)). Qed.
Lemma lem7595656 {_100044 : Type'} (s : _100044 -> Prop) : (term186 _100044 s) = (term171 _100044 s).
Proof. exact (eq_refl (term186 _100044 s)). Qed.
Lemma lem7595657 {_100044 : Type'} : (term193 _100044) = (term184 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7595656 _100044 s)). Qed.
Lemma lem7595658 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7595659 {_100044 : Type'} : (term194 _100044) = (term195 _100044).
Proof. exact (MK_COMB (@lem7595658 _100044) (@lem7595657 _100044)). Qed.
Lemma lem7595660 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595661 {_100044 : Type'} : (term196 _100044) = (term197 _100044).
Proof. exact (MK_COMB (@lem7595660) (@lem7595659 _100044)). Qed.
Lemma lem7595662 {_100044 : Type'} (s : _100044 -> Prop) : (term188 _100044 s) = (term176 _100044 s).
Proof. exact (eq_refl (term188 _100044 s)). Qed.
Lemma lem7595663 {_100044 : Type'} : (term198 _100044) = (term185 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7595662 _100044 s)). Qed.
Lemma lem7595664 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7595665 {_100044 : Type'} : (term199 _100044) = (term200 _100044).
Proof. exact (MK_COMB (@lem7595664 _100044) (@lem7595663 _100044)). Qed.
Lemma lem7595666 {_100044 : Type'} : (term183 _100044) = (term201 _100044).
Proof. exact (MK_COMB (@lem7595661 _100044) (@lem7595665 _100044)). Qed.
Lemma lem7595667 {_100044 : Type'} : ((term182 _100044) = (term183 _100044)) = ((term179 _100044) = (term201 _100044)).
Proof. exact (MK_COMB (@lem7595655 _100044) (@lem7595666 _100044)). Qed.
Lemma lem7595668 {_100044 : Type'} : (term179 _100044) = (term201 _100044).
Proof. exact (EQ_MP (@lem7595667 _100044) (@lem7595645 _100044)). Qed.
Lemma lem7595773 {_100044 : Type'} : (term80 _100044) = (term201 _100044).
Proof. exact (TRANS (@lem7595641 _100044) (@lem7595668 _100044)). Qed.
Lemma lem7595774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595775 {_100044 : Type'} : (term83 _100044) = (term202 _100044).
Proof. exact (MK_COMB (@lem7595774) (@lem7595773 _100044)). Qed.
Lemma lem7595781 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7595782 (P : nat -> Prop) (Q : nat -> Prop) : (term156 P Q) = (term157 P Q).
Proof. exact (@lem7595781 nat P Q). Qed.
Lemma lem7595783 {A : Type'} (s : A -> Prop) : (term158 A s) = (term159 A s).
Proof. exact (@lem7595782 (term160 A s) (term161 A s)). Qed.
Lemma lem7595784 {A : Type'} (s : A -> Prop) (n : nat) : (term162 A s n) = (term72 A s n).
Proof. exact (eq_refl (term162 A s n)). Qed.
Lemma lem7595785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595786 {A : Type'} (s : A -> Prop) (n : nat) : (term163 A s n) = (term74 A s n).
Proof. exact (MK_COMB (@lem7595785) (@lem7595784 A s n)). Qed.
Lemma lem7595787 {A : Type'} (s : A -> Prop) (n : nat) : (term164 A s n) = (term69 A s n).
Proof. exact (eq_refl (term164 A s n)). Qed.
Lemma lem7595788 {A : Type'} (s : A -> Prop) (n : nat) : (term165 A s n) = (term76 A s n).
Proof. exact (MK_COMB (@lem7595786 A s n) (@lem7595787 A s n)). Qed.
Lemma lem7595789 {A : Type'} (s : A -> Prop) : (term166 A s) = (term77 A s).
Proof. exact (fun_ext (fun n : nat => @lem7595788 A s n)). Qed.
Lemma lem7595790 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7595791 {A : Type'} (s : A -> Prop) : (term158 A s) = (term78 A s).
Proof. exact (MK_COMB (@lem7595790) (@lem7595789 A s)). Qed.
Lemma lem7595792 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7595793 {A : Type'} (s : A -> Prop) : (term167 A s) = (term168 A s).
Proof. exact (MK_COMB (@lem7595792) (@lem7595791 A s)). Qed.
Lemma lem7595794 {A : Type'} (s : A -> Prop) (n : nat) : (term162 A s n) = (term72 A s n).
Proof. exact (eq_refl (term162 A s n)). Qed.
Lemma lem7595795 {A : Type'} (s : A -> Prop) : (term169 A s) = (term160 A s).
Proof. exact (fun_ext (fun n : nat => @lem7595794 A s n)). Qed.
Lemma lem7595796 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7595797 {A : Type'} (s : A -> Prop) : (term170 A s) = (term171 A s).
Proof. exact (MK_COMB (@lem7595796) (@lem7595795 A s)). Qed.
Lemma lem7595798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595799 {A : Type'} (s : A -> Prop) : (term172 A s) = (term173 A s).
Proof. exact (MK_COMB (@lem7595798) (@lem7595797 A s)). Qed.
Lemma lem7595800 {A : Type'} (s : A -> Prop) (n : nat) : (term164 A s n) = (term69 A s n).
Proof. exact (eq_refl (term164 A s n)). Qed.
Lemma lem7595801 {A : Type'} (s : A -> Prop) : (term174 A s) = (term161 A s).
Proof. exact (fun_ext (fun n : nat => @lem7595800 A s n)). Qed.
Lemma lem7595802 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7595803 {A : Type'} (s : A -> Prop) : (term175 A s) = (term176 A s).
Proof. exact (MK_COMB (@lem7595802) (@lem7595801 A s)). Qed.
Lemma lem7595804 {A : Type'} (s : A -> Prop) : (term159 A s) = (term177 A s).
Proof. exact (MK_COMB (@lem7595799 A s) (@lem7595803 A s)). Qed.
Lemma lem7595805 {A : Type'} (s : A -> Prop) : ((term158 A s) = (term159 A s)) = ((term78 A s) = (term177 A s)).
Proof. exact (MK_COMB (@lem7595793 A s) (@lem7595804 A s)). Qed.
Lemma lem7595806 {A : Type'} (s : A -> Prop) : (term78 A s) = (term177 A s).
Proof. exact (EQ_MP (@lem7595805 A s) (@lem7595783 A s)). Qed.
Lemma lem7595903 {A : Type'} : (term79 A) = (term178 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7595806 A s)). Qed.
Lemma lem7595904 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7595905 {A : Type'} : (term80 A) = (term179 A).
Proof. exact (MK_COMB (@lem7595904 A) (@lem7595903 A)). Qed.
Lemma lem7595907 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7595908 {A : Type'} (P : type686 A) (Q : type686 A) : (term180 A P Q) = (term181 A P Q).
Proof. exact (@lem7595907 (A -> Prop) P Q). Qed.
Lemma lem7595909 {A : Type'} : (term182 A) = (term183 A).
Proof. exact (@lem7595908 A (term184 A) (term185 A)). Qed.
Lemma lem7595910 {A : Type'} (s : A -> Prop) : (term186 A s) = (term171 A s).
Proof. exact (eq_refl (term186 A s)). Qed.
Lemma lem7595911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595912 {A : Type'} (s : A -> Prop) : (term187 A s) = (term173 A s).
Proof. exact (MK_COMB (@lem7595911) (@lem7595910 A s)). Qed.
Lemma lem7595913 {A : Type'} (s : A -> Prop) : (term188 A s) = (term176 A s).
Proof. exact (eq_refl (term188 A s)). Qed.
Lemma lem7595914 {A : Type'} (s : A -> Prop) : (term189 A s) = (term177 A s).
Proof. exact (MK_COMB (@lem7595912 A s) (@lem7595913 A s)). Qed.
Lemma lem7595915 {A : Type'} : (term190 A) = (term178 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7595914 A s)). Qed.
Lemma lem7595916 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7595917 {A : Type'} : (term182 A) = (term179 A).
Proof. exact (MK_COMB (@lem7595916 A) (@lem7595915 A)). Qed.
Lemma lem7595918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7595919 {A : Type'} : (term191 A) = (term192 A).
Proof. exact (MK_COMB (@lem7595918) (@lem7595917 A)). Qed.
Lemma lem7595920 {A : Type'} (s : A -> Prop) : (term186 A s) = (term171 A s).
Proof. exact (eq_refl (term186 A s)). Qed.
Lemma lem7595921 {A : Type'} : (term193 A) = (term184 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7595920 A s)). Qed.
Lemma lem7595922 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7595923 {A : Type'} : (term194 A) = (term195 A).
Proof. exact (MK_COMB (@lem7595922 A) (@lem7595921 A)). Qed.
Lemma lem7595924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7595925 {A : Type'} : (term196 A) = (term197 A).
Proof. exact (MK_COMB (@lem7595924) (@lem7595923 A)). Qed.
Lemma lem7595926 {A : Type'} (s : A -> Prop) : (term188 A s) = (term176 A s).
Proof. exact (eq_refl (term188 A s)). Qed.
Lemma lem7595927 {A : Type'} : (term198 A) = (term185 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7595926 A s)). Qed.
Lemma lem7595928 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7595929 {A : Type'} : (term199 A) = (term200 A).
Proof. exact (MK_COMB (@lem7595928 A) (@lem7595927 A)). Qed.
Lemma lem7595930 {A : Type'} : (term183 A) = (term201 A).
Proof. exact (MK_COMB (@lem7595925 A) (@lem7595929 A)). Qed.
Lemma lem7595931 {A : Type'} : ((term182 A) = (term183 A)) = ((term179 A) = (term201 A)).
Proof. exact (MK_COMB (@lem7595919 A) (@lem7595930 A)). Qed.
Lemma lem7595932 {A : Type'} : (term179 A) = (term201 A).
Proof. exact (EQ_MP (@lem7595931 A) (@lem7595909 A)). Qed.
Lemma lem7596037 {A : Type'} : (term80 A) = (term201 A).
Proof. exact (TRANS (@lem7595905 A) (@lem7595932 A)). Qed.
Lemma lem7596038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596039 {A : Type'} : (term83 A) = (term202 A).
Proof. exact (MK_COMB (@lem7596038) (@lem7596037 A)). Qed.
Lemma lem7596044 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (eq_refl (term40 A)). Qed.
Lemma lem7596045 {A : Type'} : (term85 A) = (term203 A).
Proof. exact (MK_COMB (@lem7596039 A) (@lem7596044 A)). Qed.
Lemma lem7596046 {_100044 A : Type'} : (term88 _100044 A) = (term204 _100044 A).
Proof. exact (MK_COMB (@lem7595775 _100044) (@lem7596045 A)). Qed.
Lemma lem7596047 {A : Type'} : (term152 A) = (term152 A).
Proof. exact (eq_refl (term152 A)). Qed.
Lemma lem7596048 {_100044 A : Type'} : (term153 _100044 A) = (term205 _100044 A).
Proof. exact (MK_COMB (@lem7596047 A) (@lem7596046 _100044 A)). Qed.
Lemma lem7596049 {_100044 A : Type'} : (term103 _100044 A) = (term205 _100044 A).
Proof. exact (TRANS (@lem7595463 _100044 A) (@lem7596048 _100044 A)). Qed.
Lemma lem7596050 {A : Type'} : (term105 A) = (term105 A).
Proof. exact (eq_refl (term105 A)). Qed.
Lemma lem7596051 {_100044 A : Type'} : (term107 _100044 A) = (term206 _100044 A).
Proof. exact (MK_COMB (@lem7596050 A) (@lem7596049 _100044 A)). Qed.
Lemma lem7596052 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7596053 {_100044 A : Type'} : (term132 _100044 A) = (term207 _100044 A).
Proof. exact (MK_COMB (@lem7596052) (@lem7596051 _100044 A)). Qed.
Lemma lem7596075 {A : Type'} (P : A -> Prop) (Q : Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem7596076 (P : nat -> Prop) (Q : Prop) : (term137 P Q) = (term138 P Q).
Proof. exact (@lem7596075 nat P Q). Qed.
Lemma lem7596077 {_100044 A : Type'} : (term208 _100044 A) = (term209 _100044 A).
Proof. exact (@lem7596076 (term141 A) (term115 _100044 A)). Qed.
Lemma lem7596078 {A : Type'} (n : nat) : (term142 A n) = (term66 A n).
Proof. exact (eq_refl (term142 A n)). Qed.
Lemma lem7596079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596080 {A : Type'} (n : nat) : (term143 A n) = (term91 A n).
Proof. exact (MK_COMB (@lem7596079) (@lem7596078 A n)). Qed.
Lemma lem7596081 {_100044 A : Type'} : (term115 _100044 A) = (term115 _100044 A).
Proof. exact (eq_refl (term115 _100044 A)). Qed.
Lemma lem7596082 {_100044 A : Type'} (n : nat) : (term210 _100044 A n) = (term118 _100044 A n).
Proof. exact (MK_COMB (@lem7596080 A n) (@lem7596081 _100044 A)). Qed.
Lemma lem7596083 {_100044 A : Type'} : (term211 _100044 A) = (term125 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7596082 _100044 A n)). Qed.
Lemma lem7596084 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7596085 {_100044 A : Type'} : (term208 _100044 A) = (term126 _100044 A).
Proof. exact (MK_COMB (@lem7596084) (@lem7596083 _100044 A)). Qed.
Lemma lem7596086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7596087 {_100044 A : Type'} : (term212 _100044 A) = (term213 _100044 A).
Proof. exact (MK_COMB (@lem7596086) (@lem7596085 _100044 A)). Qed.
Lemma lem7596088 {A : Type'} (n : nat) : (term142 A n) = (term66 A n).
Proof. exact (eq_refl (term142 A n)). Qed.
Lemma lem7596089 {A : Type'} : (term148 A) = (term141 A).
Proof. exact (fun_ext (fun n : nat => @lem7596088 A n)). Qed.
Lemma lem7596090 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7596091 {A : Type'} : (term149 A) = (term150 A).
Proof. exact (MK_COMB (@lem7596090) (@lem7596089 A)). Qed.
Lemma lem7596092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596093 {A : Type'} : (term151 A) = (term152 A).
Proof. exact (MK_COMB (@lem7596092) (@lem7596091 A)). Qed.
Lemma lem7596094 {_100044 A : Type'} : (term115 _100044 A) = (term115 _100044 A).
Proof. exact (eq_refl (term115 _100044 A)). Qed.
Lemma lem7596095 {_100044 A : Type'} : (term209 _100044 A) = (term214 _100044 A).
Proof. exact (MK_COMB (@lem7596093 A) (@lem7596094 _100044 A)). Qed.
Lemma lem7596096 {_100044 A : Type'} : ((term208 _100044 A) = (term209 _100044 A)) = ((term126 _100044 A) = (term214 _100044 A)).
Proof. exact (MK_COMB (@lem7596087 _100044 A) (@lem7596095 _100044 A)). Qed.
Lemma lem7596097 {_100044 A : Type'} : (term126 _100044 A) = (term214 _100044 A).
Proof. exact (EQ_MP (@lem7596096 _100044 A) (@lem7596077 _100044 A)). Qed.
Lemma lem7596151 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7596152 (P : nat -> Prop) (Q : nat -> Prop) : (term156 P Q) = (term157 P Q).
Proof. exact (@lem7596151 nat P Q). Qed.
Lemma lem7596153 {_100044 : Type'} (s : _100044 -> Prop) : (term158 _100044 s) = (term159 _100044 s).
Proof. exact (@lem7596152 (term160 _100044 s) (term161 _100044 s)). Qed.
Lemma lem7596154 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term162 _100044 s n) = (term72 _100044 s n).
Proof. exact (eq_refl (term162 _100044 s n)). Qed.
Lemma lem7596155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596156 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term163 _100044 s n) = (term74 _100044 s n).
Proof. exact (MK_COMB (@lem7596155) (@lem7596154 _100044 s n)). Qed.
Lemma lem7596157 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term164 _100044 s n) = (term69 _100044 s n).
Proof. exact (eq_refl (term164 _100044 s n)). Qed.
Lemma lem7596158 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term165 _100044 s n) = (term76 _100044 s n).
Proof. exact (MK_COMB (@lem7596156 _100044 s n) (@lem7596157 _100044 s n)). Qed.
Lemma lem7596159 {_100044 : Type'} (s : _100044 -> Prop) : (term166 _100044 s) = (term77 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7596158 _100044 s n)). Qed.
Lemma lem7596160 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7596161 {_100044 : Type'} (s : _100044 -> Prop) : (term158 _100044 s) = (term78 _100044 s).
Proof. exact (MK_COMB (@lem7596160) (@lem7596159 _100044 s)). Qed.
Lemma lem7596162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7596163 {_100044 : Type'} (s : _100044 -> Prop) : (term167 _100044 s) = (term168 _100044 s).
Proof. exact (MK_COMB (@lem7596162) (@lem7596161 _100044 s)). Qed.
Lemma lem7596164 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term162 _100044 s n) = (term72 _100044 s n).
Proof. exact (eq_refl (term162 _100044 s n)). Qed.
Lemma lem7596165 {_100044 : Type'} (s : _100044 -> Prop) : (term169 _100044 s) = (term160 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7596164 _100044 s n)). Qed.
Lemma lem7596166 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7596167 {_100044 : Type'} (s : _100044 -> Prop) : (term170 _100044 s) = (term171 _100044 s).
Proof. exact (MK_COMB (@lem7596166) (@lem7596165 _100044 s)). Qed.
Lemma lem7596168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596169 {_100044 : Type'} (s : _100044 -> Prop) : (term172 _100044 s) = (term173 _100044 s).
Proof. exact (MK_COMB (@lem7596168) (@lem7596167 _100044 s)). Qed.
Lemma lem7596170 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term164 _100044 s n) = (term69 _100044 s n).
Proof. exact (eq_refl (term164 _100044 s n)). Qed.
Lemma lem7596171 {_100044 : Type'} (s : _100044 -> Prop) : (term174 _100044 s) = (term161 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7596170 _100044 s n)). Qed.
Lemma lem7596172 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7596173 {_100044 : Type'} (s : _100044 -> Prop) : (term175 _100044 s) = (term176 _100044 s).
Proof. exact (MK_COMB (@lem7596172) (@lem7596171 _100044 s)). Qed.
Lemma lem7596174 {_100044 : Type'} (s : _100044 -> Prop) : (term159 _100044 s) = (term177 _100044 s).
Proof. exact (MK_COMB (@lem7596169 _100044 s) (@lem7596173 _100044 s)). Qed.
Lemma lem7596175 {_100044 : Type'} (s : _100044 -> Prop) : ((term158 _100044 s) = (term159 _100044 s)) = ((term78 _100044 s) = (term177 _100044 s)).
Proof. exact (MK_COMB (@lem7596163 _100044 s) (@lem7596174 _100044 s)). Qed.
Lemma lem7596176 {_100044 : Type'} (s : _100044 -> Prop) : (term78 _100044 s) = (term177 _100044 s).
Proof. exact (EQ_MP (@lem7596175 _100044 s) (@lem7596153 _100044 s)). Qed.
Lemma lem7596273 {_100044 : Type'} : (term79 _100044) = (term178 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7596176 _100044 s)). Qed.
Lemma lem7596274 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7596275 {_100044 : Type'} : (term80 _100044) = (term179 _100044).
Proof. exact (MK_COMB (@lem7596274 _100044) (@lem7596273 _100044)). Qed.
Lemma lem7596277 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7596278 {_100044 : Type'} (P : type686 _100044) (Q : type686 _100044) : (term180 _100044 P Q) = (term181 _100044 P Q).
Proof. exact (@lem7596277 (_100044 -> Prop) P Q). Qed.
Lemma lem7596279 {_100044 : Type'} : (term182 _100044) = (term183 _100044).
Proof. exact (@lem7596278 _100044 (term184 _100044) (term185 _100044)). Qed.
Lemma lem7596280 {_100044 : Type'} (s : _100044 -> Prop) : (term186 _100044 s) = (term171 _100044 s).
Proof. exact (eq_refl (term186 _100044 s)). Qed.
Lemma lem7596281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596282 {_100044 : Type'} (s : _100044 -> Prop) : (term187 _100044 s) = (term173 _100044 s).
Proof. exact (MK_COMB (@lem7596281) (@lem7596280 _100044 s)). Qed.
Lemma lem7596283 {_100044 : Type'} (s : _100044 -> Prop) : (term188 _100044 s) = (term176 _100044 s).
Proof. exact (eq_refl (term188 _100044 s)). Qed.
Lemma lem7596284 {_100044 : Type'} (s : _100044 -> Prop) : (term189 _100044 s) = (term177 _100044 s).
Proof. exact (MK_COMB (@lem7596282 _100044 s) (@lem7596283 _100044 s)). Qed.
Lemma lem7596285 {_100044 : Type'} : (term190 _100044) = (term178 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7596284 _100044 s)). Qed.
Lemma lem7596286 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7596287 {_100044 : Type'} : (term182 _100044) = (term179 _100044).
Proof. exact (MK_COMB (@lem7596286 _100044) (@lem7596285 _100044)). Qed.
Lemma lem7596288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7596289 {_100044 : Type'} : (term191 _100044) = (term192 _100044).
Proof. exact (MK_COMB (@lem7596288) (@lem7596287 _100044)). Qed.
Lemma lem7596290 {_100044 : Type'} (s : _100044 -> Prop) : (term186 _100044 s) = (term171 _100044 s).
Proof. exact (eq_refl (term186 _100044 s)). Qed.
Lemma lem7596291 {_100044 : Type'} : (term193 _100044) = (term184 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7596290 _100044 s)). Qed.
Lemma lem7596292 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7596293 {_100044 : Type'} : (term194 _100044) = (term195 _100044).
Proof. exact (MK_COMB (@lem7596292 _100044) (@lem7596291 _100044)). Qed.
Lemma lem7596294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596295 {_100044 : Type'} : (term196 _100044) = (term197 _100044).
Proof. exact (MK_COMB (@lem7596294) (@lem7596293 _100044)). Qed.
Lemma lem7596296 {_100044 : Type'} (s : _100044 -> Prop) : (term188 _100044 s) = (term176 _100044 s).
Proof. exact (eq_refl (term188 _100044 s)). Qed.
Lemma lem7596297 {_100044 : Type'} : (term198 _100044) = (term185 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7596296 _100044 s)). Qed.
Lemma lem7596298 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7596299 {_100044 : Type'} : (term199 _100044) = (term200 _100044).
Proof. exact (MK_COMB (@lem7596298 _100044) (@lem7596297 _100044)). Qed.
Lemma lem7596300 {_100044 : Type'} : (term183 _100044) = (term201 _100044).
Proof. exact (MK_COMB (@lem7596295 _100044) (@lem7596299 _100044)). Qed.
Lemma lem7596301 {_100044 : Type'} : ((term182 _100044) = (term183 _100044)) = ((term179 _100044) = (term201 _100044)).
Proof. exact (MK_COMB (@lem7596289 _100044) (@lem7596300 _100044)). Qed.
Lemma lem7596302 {_100044 : Type'} : (term179 _100044) = (term201 _100044).
Proof. exact (EQ_MP (@lem7596301 _100044) (@lem7596279 _100044)). Qed.
Lemma lem7596407 {_100044 : Type'} : (term80 _100044) = (term201 _100044).
Proof. exact (TRANS (@lem7596275 _100044) (@lem7596302 _100044)). Qed.
Lemma lem7596408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596409 {_100044 : Type'} : (term83 _100044) = (term202 _100044).
Proof. exact (MK_COMB (@lem7596408) (@lem7596407 _100044)). Qed.
Lemma lem7596415 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7596416 (P : nat -> Prop) (Q : nat -> Prop) : (term156 P Q) = (term157 P Q).
Proof. exact (@lem7596415 nat P Q). Qed.
Lemma lem7596417 {A : Type'} (s : A -> Prop) : (term158 A s) = (term159 A s).
Proof. exact (@lem7596416 (term160 A s) (term161 A s)). Qed.
Lemma lem7596418 {A : Type'} (s : A -> Prop) (n : nat) : (term162 A s n) = (term72 A s n).
Proof. exact (eq_refl (term162 A s n)). Qed.
Lemma lem7596419 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596420 {A : Type'} (s : A -> Prop) (n : nat) : (term163 A s n) = (term74 A s n).
Proof. exact (MK_COMB (@lem7596419) (@lem7596418 A s n)). Qed.
Lemma lem7596421 {A : Type'} (s : A -> Prop) (n : nat) : (term164 A s n) = (term69 A s n).
Proof. exact (eq_refl (term164 A s n)). Qed.
Lemma lem7596422 {A : Type'} (s : A -> Prop) (n : nat) : (term165 A s n) = (term76 A s n).
Proof. exact (MK_COMB (@lem7596420 A s n) (@lem7596421 A s n)). Qed.
Lemma lem7596423 {A : Type'} (s : A -> Prop) : (term166 A s) = (term77 A s).
Proof. exact (fun_ext (fun n : nat => @lem7596422 A s n)). Qed.
Lemma lem7596424 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7596425 {A : Type'} (s : A -> Prop) : (term158 A s) = (term78 A s).
Proof. exact (MK_COMB (@lem7596424) (@lem7596423 A s)). Qed.
Lemma lem7596426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7596427 {A : Type'} (s : A -> Prop) : (term167 A s) = (term168 A s).
Proof. exact (MK_COMB (@lem7596426) (@lem7596425 A s)). Qed.
Lemma lem7596428 {A : Type'} (s : A -> Prop) (n : nat) : (term162 A s n) = (term72 A s n).
Proof. exact (eq_refl (term162 A s n)). Qed.
Lemma lem7596429 {A : Type'} (s : A -> Prop) : (term169 A s) = (term160 A s).
Proof. exact (fun_ext (fun n : nat => @lem7596428 A s n)). Qed.
Lemma lem7596430 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7596431 {A : Type'} (s : A -> Prop) : (term170 A s) = (term171 A s).
Proof. exact (MK_COMB (@lem7596430) (@lem7596429 A s)). Qed.
Lemma lem7596432 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596433 {A : Type'} (s : A -> Prop) : (term172 A s) = (term173 A s).
Proof. exact (MK_COMB (@lem7596432) (@lem7596431 A s)). Qed.
Lemma lem7596434 {A : Type'} (s : A -> Prop) (n : nat) : (term164 A s n) = (term69 A s n).
Proof. exact (eq_refl (term164 A s n)). Qed.
Lemma lem7596435 {A : Type'} (s : A -> Prop) : (term174 A s) = (term161 A s).
Proof. exact (fun_ext (fun n : nat => @lem7596434 A s n)). Qed.
Lemma lem7596436 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7596437 {A : Type'} (s : A -> Prop) : (term175 A s) = (term176 A s).
Proof. exact (MK_COMB (@lem7596436) (@lem7596435 A s)). Qed.
Lemma lem7596438 {A : Type'} (s : A -> Prop) : (term159 A s) = (term177 A s).
Proof. exact (MK_COMB (@lem7596433 A s) (@lem7596437 A s)). Qed.
Lemma lem7596439 {A : Type'} (s : A -> Prop) : ((term158 A s) = (term159 A s)) = ((term78 A s) = (term177 A s)).
Proof. exact (MK_COMB (@lem7596427 A s) (@lem7596438 A s)). Qed.
Lemma lem7596440 {A : Type'} (s : A -> Prop) : (term78 A s) = (term177 A s).
Proof. exact (EQ_MP (@lem7596439 A s) (@lem7596417 A s)). Qed.
Lemma lem7596537 {A : Type'} : (term79 A) = (term178 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7596440 A s)). Qed.
Lemma lem7596538 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7596539 {A : Type'} : (term80 A) = (term179 A).
Proof. exact (MK_COMB (@lem7596538 A) (@lem7596537 A)). Qed.
Lemma lem7596541 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7596542 {A : Type'} (P : type686 A) (Q : type686 A) : (term180 A P Q) = (term181 A P Q).
Proof. exact (@lem7596541 (A -> Prop) P Q). Qed.
Lemma lem7596543 {A : Type'} : (term182 A) = (term183 A).
Proof. exact (@lem7596542 A (term184 A) (term185 A)). Qed.
Lemma lem7596544 {A : Type'} (s : A -> Prop) : (term186 A s) = (term171 A s).
Proof. exact (eq_refl (term186 A s)). Qed.
Lemma lem7596545 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596546 {A : Type'} (s : A -> Prop) : (term187 A s) = (term173 A s).
Proof. exact (MK_COMB (@lem7596545) (@lem7596544 A s)). Qed.
Lemma lem7596547 {A : Type'} (s : A -> Prop) : (term188 A s) = (term176 A s).
Proof. exact (eq_refl (term188 A s)). Qed.
Lemma lem7596548 {A : Type'} (s : A -> Prop) : (term189 A s) = (term177 A s).
Proof. exact (MK_COMB (@lem7596546 A s) (@lem7596547 A s)). Qed.
Lemma lem7596549 {A : Type'} : (term190 A) = (term178 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7596548 A s)). Qed.
Lemma lem7596550 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7596551 {A : Type'} : (term182 A) = (term179 A).
Proof. exact (MK_COMB (@lem7596550 A) (@lem7596549 A)). Qed.
Lemma lem7596552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7596553 {A : Type'} : (term191 A) = (term192 A).
Proof. exact (MK_COMB (@lem7596552) (@lem7596551 A)). Qed.
Lemma lem7596554 {A : Type'} (s : A -> Prop) : (term186 A s) = (term171 A s).
Proof. exact (eq_refl (term186 A s)). Qed.
Lemma lem7596555 {A : Type'} : (term193 A) = (term184 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7596554 A s)). Qed.
Lemma lem7596556 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7596557 {A : Type'} : (term194 A) = (term195 A).
Proof. exact (MK_COMB (@lem7596556 A) (@lem7596555 A)). Qed.
Lemma lem7596558 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596559 {A : Type'} : (term196 A) = (term197 A).
Proof. exact (MK_COMB (@lem7596558) (@lem7596557 A)). Qed.
Lemma lem7596560 {A : Type'} (s : A -> Prop) : (term188 A s) = (term176 A s).
Proof. exact (eq_refl (term188 A s)). Qed.
Lemma lem7596561 {A : Type'} : (term198 A) = (term185 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7596560 A s)). Qed.
Lemma lem7596562 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7596563 {A : Type'} : (term199 A) = (term200 A).
Proof. exact (MK_COMB (@lem7596562 A) (@lem7596561 A)). Qed.
Lemma lem7596564 {A : Type'} : (term183 A) = (term201 A).
Proof. exact (MK_COMB (@lem7596559 A) (@lem7596563 A)). Qed.
Lemma lem7596565 {A : Type'} : ((term182 A) = (term183 A)) = ((term179 A) = (term201 A)).
Proof. exact (MK_COMB (@lem7596553 A) (@lem7596564 A)). Qed.
Lemma lem7596566 {A : Type'} : (term179 A) = (term201 A).
Proof. exact (EQ_MP (@lem7596565 A) (@lem7596543 A)). Qed.
Lemma lem7596671 {A : Type'} : (term80 A) = (term201 A).
Proof. exact (TRANS (@lem7596539 A) (@lem7596566 A)). Qed.
Lemma lem7596672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596673 {A : Type'} : (term83 A) = (term202 A).
Proof. exact (MK_COMB (@lem7596672) (@lem7596671 A)). Qed.
Lemma lem7596678 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (eq_refl (term29 A)). Qed.
Lemma lem7596679 {A : Type'} : (term112 A) = (term215 A).
Proof. exact (MK_COMB (@lem7596673 A) (@lem7596678 A)). Qed.
Lemma lem7596680 {_100044 A : Type'} : (term115 _100044 A) = (term216 _100044 A).
Proof. exact (MK_COMB (@lem7596409 _100044) (@lem7596679 A)). Qed.
Lemma lem7596681 {A : Type'} : (term152 A) = (term152 A).
Proof. exact (eq_refl (term152 A)). Qed.
Lemma lem7596682 {_100044 A : Type'} : (term214 _100044 A) = (term217 _100044 A).
Proof. exact (MK_COMB (@lem7596681 A) (@lem7596680 _100044 A)). Qed.
Lemma lem7596683 {_100044 A : Type'} : (term126 _100044 A) = (term217 _100044 A).
Proof. exact (TRANS (@lem7596097 _100044 A) (@lem7596682 _100044 A)). Qed.
Lemma lem7596684 {A : Type'} : (term127 A) = (term127 A).
Proof. exact (eq_refl (term127 A)). Qed.
Lemma lem7596685 {_100044 A : Type'} : (term129 _100044 A) = (term218 _100044 A).
Proof. exact (MK_COMB (@lem7596684 A) (@lem7596683 _100044 A)). Qed.
Lemma lem7596686 {_100044 A : Type'} : (term134 _100044 A) = (term219 _100044 A).
Proof. exact (MK_COMB (@lem7596053 _100044 A) (@lem7596685 _100044 A)). Qed.
Lemma lem7596688 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7596689 (P : nat -> Prop) (Q : Prop) : (term138 P Q) = (term137 P Q).
Proof. exact (@lem7596688 nat P Q). Qed.
Lemma lem7596690 {_100044 A : Type'} : (term220 _100044 A) = (term221 _100044 A).
Proof. exact (@lem7596689 (term141 A) (term204 _100044 A)). Qed.
Lemma lem7596691 {A : Type'} (n : nat) : (term142 A n) = (term66 A n).
Proof. exact (eq_refl (term142 A n)). Qed.
Lemma lem7596692 {A : Type'} : (term148 A) = (term141 A).
Proof. exact (fun_ext (fun n : nat => @lem7596691 A n)). Qed.
Lemma lem7596693 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7596694 {A : Type'} : (term149 A) = (term150 A).
Proof. exact (MK_COMB (@lem7596693) (@lem7596692 A)). Qed.
Lemma lem7596695 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596696 {A : Type'} : (term151 A) = (term152 A).
Proof. exact (MK_COMB (@lem7596695) (@lem7596694 A)). Qed.
Lemma lem7596697 {_100044 A : Type'} : (term204 _100044 A) = (term204 _100044 A).
Proof. exact (eq_refl (term204 _100044 A)). Qed.
Lemma lem7596698 {_100044 A : Type'} : (term220 _100044 A) = (term205 _100044 A).
Proof. exact (MK_COMB (@lem7596696 A) (@lem7596697 _100044 A)). Qed.
Lemma lem7596699 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7596700 {_100044 A : Type'} : (term222 _100044 A) = (term223 _100044 A).
Proof. exact (MK_COMB (@lem7596699) (@lem7596698 _100044 A)). Qed.
Lemma lem7596701 {A : Type'} (n : nat) : (term142 A n) = (term66 A n).
Proof. exact (eq_refl (term142 A n)). Qed.
Lemma lem7596702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596703 {A : Type'} (n : nat) : (term143 A n) = (term91 A n).
Proof. exact (MK_COMB (@lem7596702) (@lem7596701 A n)). Qed.
Lemma lem7596704 {_100044 A : Type'} : (term204 _100044 A) = (term204 _100044 A).
Proof. exact (eq_refl (term204 _100044 A)). Qed.
Lemma lem7596705 {_100044 A : Type'} (n : nat) : (term224 _100044 A n) = (term225 _100044 A n).
Proof. exact (MK_COMB (@lem7596703 A n) (@lem7596704 _100044 A)). Qed.
Lemma lem7596706 {_100044 A : Type'} : (term226 _100044 A) = (term227 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7596705 _100044 A n)). Qed.
Lemma lem7596707 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7596708 {_100044 A : Type'} : (term221 _100044 A) = (term228 _100044 A).
Proof. exact (MK_COMB (@lem7596707) (@lem7596706 _100044 A)). Qed.
Lemma lem7596709 {_100044 A : Type'} : ((term220 _100044 A) = (term221 _100044 A)) = ((term205 _100044 A) = (term228 _100044 A)).
Proof. exact (MK_COMB (@lem7596700 _100044 A) (@lem7596708 _100044 A)). Qed.
Lemma lem7596710 {_100044 A : Type'} : (term205 _100044 A) = (term228 _100044 A).
Proof. exact (EQ_MP (@lem7596709 _100044 A) (@lem7596690 _100044 A)). Qed.
Lemma lem7596711 {A : Type'} : (term105 A) = (term105 A).
Proof. exact (eq_refl (term105 A)). Qed.
Lemma lem7596712 {_100044 A : Type'} : (term206 _100044 A) = (term229 _100044 A).
Proof. exact (MK_COMB (@lem7596711 A) (@lem7596710 _100044 A)). Qed.
Lemma lem7596714 {A : Type'} (P : Prop) (Q : A -> Prop) : (term230 A P Q) = (term231 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7596715 (P : Prop) (Q : nat -> Prop) : (term232 P Q) = (term233 P Q).
Proof. exact (@lem7596714 nat P Q). Qed.
Lemma lem7596716 {_100044 A : Type'} : (term234 _100044 A) = (term235 _100044 A).
Proof. exact (@lem7596715 (@FINITE A (@UNIV A)) (term227 _100044 A)). Qed.
Lemma lem7596717 {_100044 A : Type'} (n : nat) : (term236 _100044 A n) = (term225 _100044 A n).
Proof. exact (eq_refl (term236 _100044 A n)). Qed.
Lemma lem7596718 {_100044 A : Type'} : (term237 _100044 A) = (term227 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7596717 _100044 A n)). Qed.
Lemma lem7596719 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7596720 {_100044 A : Type'} : (term238 _100044 A) = (term228 _100044 A).
Proof. exact (MK_COMB (@lem7596719) (@lem7596718 _100044 A)). Qed.
Lemma lem7596721 {A : Type'} : (term105 A) = (term105 A).
Proof. exact (eq_refl (term105 A)). Qed.
Lemma lem7596722 {_100044 A : Type'} : (term234 _100044 A) = (term229 _100044 A).
Proof. exact (MK_COMB (@lem7596721 A) (@lem7596720 _100044 A)). Qed.
Lemma lem7596723 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7596724 {_100044 A : Type'} : (term239 _100044 A) = (term240 _100044 A).
Proof. exact (MK_COMB (@lem7596723) (@lem7596722 _100044 A)). Qed.
Lemma lem7596725 {_100044 A : Type'} (n : nat) : (term236 _100044 A n) = (term225 _100044 A n).
Proof. exact (eq_refl (term236 _100044 A n)). Qed.
Lemma lem7596726 {A : Type'} : (term105 A) = (term105 A).
Proof. exact (eq_refl (term105 A)). Qed.
Lemma lem7596727 {_100044 A : Type'} (n : nat) : (term241 _100044 A n) = (term242 _100044 A n).
Proof. exact (MK_COMB (@lem7596726 A) (@lem7596725 _100044 A n)). Qed.
Lemma lem7596728 {_100044 A : Type'} : (term243 _100044 A) = (term244 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7596727 _100044 A n)). Qed.
Lemma lem7596729 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7596730 {_100044 A : Type'} : (term235 _100044 A) = (term245 _100044 A).
Proof. exact (MK_COMB (@lem7596729) (@lem7596728 _100044 A)). Qed.
Lemma lem7596731 {_100044 A : Type'} : ((term234 _100044 A) = (term235 _100044 A)) = ((term229 _100044 A) = (term245 _100044 A)).
Proof. exact (MK_COMB (@lem7596724 _100044 A) (@lem7596730 _100044 A)). Qed.
Lemma lem7596732 {_100044 A : Type'} : (term229 _100044 A) = (term245 _100044 A).
Proof. exact (EQ_MP (@lem7596731 _100044 A) (@lem7596716 _100044 A)). Qed.
Lemma lem7596733 {_100044 A : Type'} : (term206 _100044 A) = (term245 _100044 A).
Proof. exact (TRANS (@lem7596712 _100044 A) (@lem7596732 _100044 A)). Qed.
Lemma lem7596734 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7596735 {_100044 A : Type'} : (term207 _100044 A) = (term246 _100044 A).
Proof. exact (MK_COMB (@lem7596734) (@lem7596733 _100044 A)). Qed.
Lemma lem7596737 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7596738 (P : nat -> Prop) (Q : Prop) : (term138 P Q) = (term137 P Q).
Proof. exact (@lem7596737 nat P Q). Qed.
Lemma lem7596739 {_100044 A : Type'} : (term247 _100044 A) = (term248 _100044 A).
Proof. exact (@lem7596738 (term141 A) (term216 _100044 A)). Qed.
Lemma lem7596740 {A : Type'} (n : nat) : (term142 A n) = (term66 A n).
Proof. exact (eq_refl (term142 A n)). Qed.
Lemma lem7596741 {A : Type'} : (term148 A) = (term141 A).
Proof. exact (fun_ext (fun n : nat => @lem7596740 A n)). Qed.
Lemma lem7596742 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7596743 {A : Type'} : (term149 A) = (term150 A).
Proof. exact (MK_COMB (@lem7596742) (@lem7596741 A)). Qed.
Lemma lem7596744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596745 {A : Type'} : (term151 A) = (term152 A).
Proof. exact (MK_COMB (@lem7596744) (@lem7596743 A)). Qed.
Lemma lem7596746 {_100044 A : Type'} : (term216 _100044 A) = (term216 _100044 A).
Proof. exact (eq_refl (term216 _100044 A)). Qed.
Lemma lem7596747 {_100044 A : Type'} : (term247 _100044 A) = (term217 _100044 A).
Proof. exact (MK_COMB (@lem7596745 A) (@lem7596746 _100044 A)). Qed.
Lemma lem7596748 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7596749 {_100044 A : Type'} : (term249 _100044 A) = (term250 _100044 A).
Proof. exact (MK_COMB (@lem7596748) (@lem7596747 _100044 A)). Qed.
Lemma lem7596750 {A : Type'} (n : nat) : (term142 A n) = (term66 A n).
Proof. exact (eq_refl (term142 A n)). Qed.
Lemma lem7596751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596752 {A : Type'} (n : nat) : (term143 A n) = (term91 A n).
Proof. exact (MK_COMB (@lem7596751) (@lem7596750 A n)). Qed.
Lemma lem7596753 {_100044 A : Type'} : (term216 _100044 A) = (term216 _100044 A).
Proof. exact (eq_refl (term216 _100044 A)). Qed.
Lemma lem7596754 {_100044 A : Type'} (n : nat) : (term251 _100044 A n) = (term252 _100044 A n).
Proof. exact (MK_COMB (@lem7596752 A n) (@lem7596753 _100044 A)). Qed.
Lemma lem7596755 {_100044 A : Type'} : (term253 _100044 A) = (term254 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7596754 _100044 A n)). Qed.
Lemma lem7596756 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7596757 {_100044 A : Type'} : (term248 _100044 A) = (term255 _100044 A).
Proof. exact (MK_COMB (@lem7596756) (@lem7596755 _100044 A)). Qed.
Lemma lem7596758 {_100044 A : Type'} : ((term247 _100044 A) = (term248 _100044 A)) = ((term217 _100044 A) = (term255 _100044 A)).
Proof. exact (MK_COMB (@lem7596749 _100044 A) (@lem7596757 _100044 A)). Qed.
Lemma lem7596759 {_100044 A : Type'} : (term217 _100044 A) = (term255 _100044 A).
Proof. exact (EQ_MP (@lem7596758 _100044 A) (@lem7596739 _100044 A)). Qed.
Lemma lem7596760 {A : Type'} : (term127 A) = (term127 A).
Proof. exact (eq_refl (term127 A)). Qed.
Lemma lem7596761 {_100044 A : Type'} : (term218 _100044 A) = (term256 _100044 A).
Proof. exact (MK_COMB (@lem7596760 A) (@lem7596759 _100044 A)). Qed.
Lemma lem7596763 {A : Type'} (P : Prop) (Q : A -> Prop) : (term230 A P Q) = (term231 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7596764 (P : Prop) (Q : nat -> Prop) : (term232 P Q) = (term233 P Q).
Proof. exact (@lem7596763 nat P Q). Qed.
Lemma lem7596765 {_100044 A : Type'} : (term257 _100044 A) = (term258 _100044 A).
Proof. exact (@lem7596764 (term109 A) (term254 _100044 A)). Qed.
Lemma lem7596766 {_100044 A : Type'} (n : nat) : (term259 _100044 A n) = (term252 _100044 A n).
Proof. exact (eq_refl (term259 _100044 A n)). Qed.
Lemma lem7596767 {_100044 A : Type'} : (term260 _100044 A) = (term254 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7596766 _100044 A n)). Qed.
Lemma lem7596768 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7596769 {_100044 A : Type'} : (term261 _100044 A) = (term255 _100044 A).
Proof. exact (MK_COMB (@lem7596768) (@lem7596767 _100044 A)). Qed.
Lemma lem7596770 {A : Type'} : (term127 A) = (term127 A).
Proof. exact (eq_refl (term127 A)). Qed.
Lemma lem7596771 {_100044 A : Type'} : (term257 _100044 A) = (term256 _100044 A).
Proof. exact (MK_COMB (@lem7596770 A) (@lem7596769 _100044 A)). Qed.
Lemma lem7596772 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7596773 {_100044 A : Type'} : (term262 _100044 A) = (term263 _100044 A).
Proof. exact (MK_COMB (@lem7596772) (@lem7596771 _100044 A)). Qed.
Lemma lem7596774 {_100044 A : Type'} (n : nat) : (term259 _100044 A n) = (term252 _100044 A n).
Proof. exact (eq_refl (term259 _100044 A n)). Qed.
Lemma lem7596775 {A : Type'} : (term127 A) = (term127 A).
Proof. exact (eq_refl (term127 A)). Qed.
Lemma lem7596776 {_100044 A : Type'} (n : nat) : (term264 _100044 A n) = (term265 _100044 A n).
Proof. exact (MK_COMB (@lem7596775 A) (@lem7596774 _100044 A n)). Qed.
Lemma lem7596777 {_100044 A : Type'} : (term266 _100044 A) = (term267 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7596776 _100044 A n)). Qed.
Lemma lem7596778 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7596779 {_100044 A : Type'} : (term258 _100044 A) = (term268 _100044 A).
Proof. exact (MK_COMB (@lem7596778) (@lem7596777 _100044 A)). Qed.
Lemma lem7596780 {_100044 A : Type'} : ((term257 _100044 A) = (term258 _100044 A)) = ((term256 _100044 A) = (term268 _100044 A)).
Proof. exact (MK_COMB (@lem7596773 _100044 A) (@lem7596779 _100044 A)). Qed.
Lemma lem7596781 {_100044 A : Type'} : (term256 _100044 A) = (term268 _100044 A).
Proof. exact (EQ_MP (@lem7596780 _100044 A) (@lem7596765 _100044 A)). Qed.
Lemma lem7596782 {_100044 A : Type'} : (term218 _100044 A) = (term268 _100044 A).
Proof. exact (TRANS (@lem7596761 _100044 A) (@lem7596781 _100044 A)). Qed.
Lemma lem7596783 {_100044 A : Type'} : (term219 _100044 A) = (term269 _100044 A).
Proof. exact (MK_COMB (@lem7596735 _100044 A) (@lem7596782 _100044 A)). Qed.
Lemma lem7596785 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7596786 (P : nat -> Prop) (Q : nat -> Prop) : (term272 P Q) = (term273 P Q).
Proof. exact (@lem7596785 nat P Q). Qed.
Lemma lem7596787 {_100044 A : Type'} : (term274 _100044 A) = (term275 _100044 A).
Proof. exact (@lem7596786 (term244 _100044 A) (term267 _100044 A)). Qed.
Lemma lem7596788 {_100044 A : Type'} (n : nat) : (term276 _100044 A n) = (term242 _100044 A n).
Proof. exact (eq_refl (term276 _100044 A n)). Qed.
Lemma lem7596789 {_100044 A : Type'} : (term277 _100044 A) = (term244 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7596788 _100044 A n)). Qed.
Lemma lem7596790 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7596791 {_100044 A : Type'} : (term278 _100044 A) = (term245 _100044 A).
Proof. exact (MK_COMB (@lem7596790) (@lem7596789 _100044 A)). Qed.
Lemma lem7596792 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7596793 {_100044 A : Type'} : (term279 _100044 A) = (term246 _100044 A).
Proof. exact (MK_COMB (@lem7596792) (@lem7596791 _100044 A)). Qed.
Lemma lem7596794 {_100044 A : Type'} (n : nat) : (term280 _100044 A n) = (term265 _100044 A n).
Proof. exact (eq_refl (term280 _100044 A n)). Qed.
Lemma lem7596795 {_100044 A : Type'} : (term281 _100044 A) = (term267 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7596794 _100044 A n)). Qed.
Lemma lem7596796 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7596797 {_100044 A : Type'} : (term282 _100044 A) = (term268 _100044 A).
Proof. exact (MK_COMB (@lem7596796) (@lem7596795 _100044 A)). Qed.
Lemma lem7596798 {_100044 A : Type'} : (term274 _100044 A) = (term269 _100044 A).
Proof. exact (MK_COMB (@lem7596793 _100044 A) (@lem7596797 _100044 A)). Qed.
Lemma lem7596799 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7596800 {_100044 A : Type'} : (term283 _100044 A) = (term284 _100044 A).
Proof. exact (MK_COMB (@lem7596799) (@lem7596798 _100044 A)). Qed.
Lemma lem7596801 {_100044 A : Type'} (n : nat) : (term276 _100044 A n) = (term242 _100044 A n).
Proof. exact (eq_refl (term276 _100044 A n)). Qed.
Lemma lem7596802 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7596803 {_100044 A : Type'} (n : nat) : (term285 _100044 A n) = (term286 _100044 A n).
Proof. exact (MK_COMB (@lem7596802) (@lem7596801 _100044 A n)). Qed.
Lemma lem7596804 {_100044 A : Type'} (n : nat) : (term280 _100044 A n) = (term265 _100044 A n).
Proof. exact (eq_refl (term280 _100044 A n)). Qed.
Lemma lem7596805 {_100044 A : Type'} (n : nat) : (term287 _100044 A n) = (term288 _100044 A n).
Proof. exact (MK_COMB (@lem7596803 _100044 A n) (@lem7596804 _100044 A n)). Qed.
Lemma lem7596806 {_100044 A : Type'} : (term289 _100044 A) = (term290 _100044 A).
Proof. exact (fun_ext (fun n : nat => @lem7596805 _100044 A n)). Qed.
Lemma lem7596807 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7596808 {_100044 A : Type'} : (term275 _100044 A) = (term291 _100044 A).
Proof. exact (MK_COMB (@lem7596807) (@lem7596806 _100044 A)). Qed.
Lemma lem7596809 {_100044 A : Type'} : ((term274 _100044 A) = (term275 _100044 A)) = ((term269 _100044 A) = (term291 _100044 A)).
Proof. exact (MK_COMB (@lem7596800 _100044 A) (@lem7596808 _100044 A)). Qed.
Lemma lem7596810 {_100044 A : Type'} : (term269 _100044 A) = (term291 _100044 A).
Proof. exact (EQ_MP (@lem7596809 _100044 A) (@lem7596787 _100044 A)). Qed.
Lemma lem7596811 {_100044 A : Type'} : (term219 _100044 A) = (term291 _100044 A).
Proof. exact (TRANS (@lem7596783 _100044 A) (@lem7596810 _100044 A)). Qed.
Lemma lem7596812 {_100044 A : Type'} : (term134 _100044 A) = (term291 _100044 A).
Proof. exact (TRANS (@lem7596686 _100044 A) (@lem7596811 _100044 A)). Qed.
Lemma lem7596813 {_100044 A : Type'} : (term64 _100044 A) = (term291 _100044 A).
Proof. exact (TRANS (@lem7595419 _100044 A) (@lem7596812 _100044 A)). Qed.
Lemma lem7596814 {_100044 A : Type'} (h1 : term64 _100044 A) : term291 _100044 A.
Proof. exact (EQ_MP (@lem7596813 _100044 A) (@lem7595200 _100044 A h1)). Qed.
Lemma lem7596815 {_100044 A : Type'} (n : nat) (h1 : term288 _100044 A n) : term288 _100044 A n.
Proof. exact (h1). Qed.
Lemma lem7596826 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = term23) = ((@dimindex A s) = term23).
Proof. exact (eq_refl ((@dimindex A s) = term23)). Qed.
Lemma lem7596827 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7596826 A s)). Qed.
Lemma lem7596828 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7596829 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (MK_COMB (@lem7596828 A) (@lem7596827 A)). Qed.
Lemma lem7596852 {A : Type'} (s : A -> Prop) (n : nat) : (term69 A s n) = (term69 A s n).
Proof. exact (eq_refl (term69 A s n)). Qed.
Lemma lem7596853 {A : Type'} (s : A -> Prop) : (term161 A s) = (term161 A s).
Proof. exact (fun_ext (fun n : nat => @lem7596852 A s n)). Qed.
Lemma lem7596854 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7596855 {A : Type'} (s : A -> Prop) : (term176 A s) = (term176 A s).
Proof. exact (MK_COMB (@lem7596854) (@lem7596853 A s)). Qed.
Lemma lem7596856 {A : Type'} : (term185 A) = (term185 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7596855 A s)). Qed.
Lemma lem7596857 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7596858 {A : Type'} : (term200 A) = (term200 A).
Proof. exact (MK_COMB (@lem7596857 A) (@lem7596856 A)). Qed.
Lemma lem7596883 {A : Type'} (s : A -> Prop) (n : nat) : (term72 A s n) = (term72 A s n).
Proof. exact (eq_refl (term72 A s n)). Qed.
Lemma lem7596884 {A : Type'} (s : A -> Prop) : (term160 A s) = (term160 A s).
Proof. exact (fun_ext (fun n : nat => @lem7596883 A s n)). Qed.
Lemma lem7596885 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7596886 {A : Type'} (s : A -> Prop) : (term171 A s) = (term171 A s).
Proof. exact (MK_COMB (@lem7596885) (@lem7596884 A s)). Qed.
Lemma lem7596887 {A : Type'} : (term184 A) = (term184 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7596886 A s)). Qed.
Lemma lem7596888 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7596889 {A : Type'} : (term195 A) = (term195 A).
Proof. exact (MK_COMB (@lem7596888 A) (@lem7596887 A)). Qed.
Lemma lem7596890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596891 {A : Type'} : (term197 A) = (term197 A).
Proof. exact (MK_COMB (@lem7596890) (@lem7596889 A)). Qed.
Lemma lem7596892 {A : Type'} : (term201 A) = (term201 A).
Proof. exact (MK_COMB (@lem7596891 A) (@lem7596858 A)). Qed.
Lemma lem7596893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596894 {A : Type'} : (term202 A) = (term202 A).
Proof. exact (MK_COMB (@lem7596893) (@lem7596892 A)). Qed.
Lemma lem7596895 {A : Type'} : (term215 A) = (term215 A).
Proof. exact (MK_COMB (@lem7596894 A) (@lem7596829 A)). Qed.
Lemma lem7596918 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term69 _100044 s n) = (term69 _100044 s n).
Proof. exact (eq_refl (term69 _100044 s n)). Qed.
Lemma lem7596919 {_100044 : Type'} (s : _100044 -> Prop) : (term161 _100044 s) = (term161 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7596918 _100044 s n)). Qed.
Lemma lem7596920 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7596921 {_100044 : Type'} (s : _100044 -> Prop) : (term176 _100044 s) = (term176 _100044 s).
Proof. exact (MK_COMB (@lem7596920) (@lem7596919 _100044 s)). Qed.
Lemma lem7596922 {_100044 : Type'} : (term185 _100044) = (term185 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7596921 _100044 s)). Qed.
Lemma lem7596923 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7596924 {_100044 : Type'} : (term200 _100044) = (term200 _100044).
Proof. exact (MK_COMB (@lem7596923 _100044) (@lem7596922 _100044)). Qed.
Lemma lem7596949 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term72 _100044 s n) = (term72 _100044 s n).
Proof. exact (eq_refl (term72 _100044 s n)). Qed.
Lemma lem7596950 {_100044 : Type'} (s : _100044 -> Prop) : (term160 _100044 s) = (term160 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7596949 _100044 s n)). Qed.
Lemma lem7596951 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7596952 {_100044 : Type'} (s : _100044 -> Prop) : (term171 _100044 s) = (term171 _100044 s).
Proof. exact (MK_COMB (@lem7596951) (@lem7596950 _100044 s)). Qed.
Lemma lem7596953 {_100044 : Type'} : (term184 _100044) = (term184 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7596952 _100044 s)). Qed.
Lemma lem7596954 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7596955 {_100044 : Type'} : (term195 _100044) = (term195 _100044).
Proof. exact (MK_COMB (@lem7596954 _100044) (@lem7596953 _100044)). Qed.
Lemma lem7596956 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596957 {_100044 : Type'} : (term197 _100044) = (term197 _100044).
Proof. exact (MK_COMB (@lem7596956) (@lem7596955 _100044)). Qed.
Lemma lem7596958 {_100044 : Type'} : (term201 _100044) = (term201 _100044).
Proof. exact (MK_COMB (@lem7596957 _100044) (@lem7596924 _100044)). Qed.
Lemma lem7596959 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7596960 {_100044 : Type'} : (term202 _100044) = (term202 _100044).
Proof. exact (MK_COMB (@lem7596959) (@lem7596958 _100044)). Qed.
Lemma lem7596961 {_100044 A : Type'} : (term216 _100044 A) = (term216 _100044 A).
Proof. exact (MK_COMB (@lem7596960 _100044) (@lem7596895 A)). Qed.
Lemma lem7596980 {A : Type'} (n : nat) : (term91 A n) = (term91 A n).
Proof. exact (eq_refl (term91 A n)). Qed.
Lemma lem7596981 {_100044 A : Type'} (n : nat) : (term252 _100044 A n) = (term252 _100044 A n).
Proof. exact (MK_COMB (@lem7596980 A n) (@lem7596961 _100044 A)). Qed.
Lemma lem7596988 {A : Type'} : (term127 A) = (term127 A).
Proof. exact (eq_refl (term127 A)). Qed.
Lemma lem7596989 {_100044 A : Type'} (n : nat) : (term265 _100044 A n) = (term265 _100044 A n).
Proof. exact (MK_COMB (@lem7596988 A) (@lem7596981 _100044 A n)). Qed.
Lemma lem7596998 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (@CARD A (@UNIV A))) = ((@dimindex A s) = (@CARD A (@UNIV A))).
Proof. exact (eq_refl ((@dimindex A s) = (@CARD A (@UNIV A)))). Qed.
Lemma lem7596999 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7596998 A s)). Qed.
Lemma lem7597000 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7597001 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (MK_COMB (@lem7597000 A) (@lem7596999 A)). Qed.
Lemma lem7597024 {A : Type'} (s : A -> Prop) (n : nat) : (term69 A s n) = (term69 A s n).
Proof. exact (eq_refl (term69 A s n)). Qed.
Lemma lem7597025 {A : Type'} (s : A -> Prop) : (term161 A s) = (term161 A s).
Proof. exact (fun_ext (fun n : nat => @lem7597024 A s n)). Qed.
Lemma lem7597026 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7597027 {A : Type'} (s : A -> Prop) : (term176 A s) = (term176 A s).
Proof. exact (MK_COMB (@lem7597026) (@lem7597025 A s)). Qed.
Lemma lem7597028 {A : Type'} : (term185 A) = (term185 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7597027 A s)). Qed.
Lemma lem7597029 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7597030 {A : Type'} : (term200 A) = (term200 A).
Proof. exact (MK_COMB (@lem7597029 A) (@lem7597028 A)). Qed.
Lemma lem7597055 {A : Type'} (s : A -> Prop) (n : nat) : (term72 A s n) = (term72 A s n).
Proof. exact (eq_refl (term72 A s n)). Qed.
Lemma lem7597056 {A : Type'} (s : A -> Prop) : (term160 A s) = (term160 A s).
Proof. exact (fun_ext (fun n : nat => @lem7597055 A s n)). Qed.
Lemma lem7597057 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7597058 {A : Type'} (s : A -> Prop) : (term171 A s) = (term171 A s).
Proof. exact (MK_COMB (@lem7597057) (@lem7597056 A s)). Qed.
Lemma lem7597059 {A : Type'} : (term184 A) = (term184 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7597058 A s)). Qed.
Lemma lem7597060 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7597061 {A : Type'} : (term195 A) = (term195 A).
Proof. exact (MK_COMB (@lem7597060 A) (@lem7597059 A)). Qed.
Lemma lem7597062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7597063 {A : Type'} : (term197 A) = (term197 A).
Proof. exact (MK_COMB (@lem7597062) (@lem7597061 A)). Qed.
Lemma lem7597064 {A : Type'} : (term201 A) = (term201 A).
Proof. exact (MK_COMB (@lem7597063 A) (@lem7597030 A)). Qed.
Lemma lem7597065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7597066 {A : Type'} : (term202 A) = (term202 A).
Proof. exact (MK_COMB (@lem7597065) (@lem7597064 A)). Qed.
Lemma lem7597067 {A : Type'} : (term203 A) = (term203 A).
Proof. exact (MK_COMB (@lem7597066 A) (@lem7597001 A)). Qed.
Lemma lem7597090 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term69 _100044 s n) = (term69 _100044 s n).
Proof. exact (eq_refl (term69 _100044 s n)). Qed.
Lemma lem7597091 {_100044 : Type'} (s : _100044 -> Prop) : (term161 _100044 s) = (term161 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7597090 _100044 s n)). Qed.
Lemma lem7597092 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7597093 {_100044 : Type'} (s : _100044 -> Prop) : (term176 _100044 s) = (term176 _100044 s).
Proof. exact (MK_COMB (@lem7597092) (@lem7597091 _100044 s)). Qed.
Lemma lem7597094 {_100044 : Type'} : (term185 _100044) = (term185 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7597093 _100044 s)). Qed.
Lemma lem7597095 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7597096 {_100044 : Type'} : (term200 _100044) = (term200 _100044).
Proof. exact (MK_COMB (@lem7597095 _100044) (@lem7597094 _100044)). Qed.
Lemma lem7597121 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term72 _100044 s n) = (term72 _100044 s n).
Proof. exact (eq_refl (term72 _100044 s n)). Qed.
Lemma lem7597122 {_100044 : Type'} (s : _100044 -> Prop) : (term160 _100044 s) = (term160 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7597121 _100044 s n)). Qed.
Lemma lem7597123 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7597124 {_100044 : Type'} (s : _100044 -> Prop) : (term171 _100044 s) = (term171 _100044 s).
Proof. exact (MK_COMB (@lem7597123) (@lem7597122 _100044 s)). Qed.
Lemma lem7597125 {_100044 : Type'} : (term184 _100044) = (term184 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7597124 _100044 s)). Qed.
Lemma lem7597126 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7597127 {_100044 : Type'} : (term195 _100044) = (term195 _100044).
Proof. exact (MK_COMB (@lem7597126 _100044) (@lem7597125 _100044)). Qed.
Lemma lem7597128 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7597129 {_100044 : Type'} : (term197 _100044) = (term197 _100044).
Proof. exact (MK_COMB (@lem7597128) (@lem7597127 _100044)). Qed.
Lemma lem7597130 {_100044 : Type'} : (term201 _100044) = (term201 _100044).
Proof. exact (MK_COMB (@lem7597129 _100044) (@lem7597096 _100044)). Qed.
Lemma lem7597131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7597132 {_100044 : Type'} : (term202 _100044) = (term202 _100044).
Proof. exact (MK_COMB (@lem7597131) (@lem7597130 _100044)). Qed.
Lemma lem7597133 {_100044 A : Type'} : (term204 _100044 A) = (term204 _100044 A).
Proof. exact (MK_COMB (@lem7597132 _100044) (@lem7597067 A)). Qed.
Lemma lem7597152 {A : Type'} (n : nat) : (term91 A n) = (term91 A n).
Proof. exact (eq_refl (term91 A n)). Qed.
Lemma lem7597153 {_100044 A : Type'} (n : nat) : (term225 _100044 A n) = (term225 _100044 A n).
Proof. exact (MK_COMB (@lem7597152 A n) (@lem7597133 _100044 A)). Qed.
Lemma lem7597158 {A : Type'} : (term105 A) = (term105 A).
Proof. exact (eq_refl (term105 A)). Qed.
Lemma lem7597159 {_100044 A : Type'} (n : nat) : (term242 _100044 A n) = (term242 _100044 A n).
Proof. exact (MK_COMB (@lem7597158 A) (@lem7597153 _100044 A n)). Qed.
Lemma lem7597160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7597161 {_100044 A : Type'} (n : nat) : (term286 _100044 A n) = (term286 _100044 A n).
Proof. exact (MK_COMB (@lem7597160) (@lem7597159 _100044 A n)). Qed.
Lemma lem7597162 {_100044 A : Type'} (n : nat) : (term288 _100044 A n) = (term288 _100044 A n).
Proof. exact (MK_COMB (@lem7597161 _100044 A n) (@lem7596989 _100044 A n)). Qed.
Lemma lem7597163 {_100044 A : Type'} (n : nat) (h1 : term288 _100044 A n) : term288 _100044 A n.
Proof. exact (EQ_MP (@lem7597162 _100044 A n) (@lem7596815 _100044 A n h1)). Qed.
Lemma lem7597164 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term242 _100044 A n.
Proof. exact (h1). Qed.
Lemma lem7597165 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : term265 _100044 A n.
Proof. exact (h1). Qed.
Lemma lem7597166 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term225 _100044 A n.
Proof. exact (proj2 (@lem7597164 _100044 A n h1)). Qed.
Lemma lem7597168 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term204 _100044 A.
Proof. exact (proj2 (@lem7597166 _100044 A n h1)). Qed.
Lemma lem7597169 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term66 A n.
Proof. exact (proj1 (@lem7597166 _100044 A n h1)). Qed.
Lemma lem7597170 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term203 A.
Proof. exact (proj2 (@lem7597168 _100044 A n h1)). Qed.
Lemma lem7597172 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term40 A.
Proof. exact (proj2 (@lem7597170 _100044 A n h1)). Qed.
Lemma lem7597173 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term201 A.
Proof. exact (proj1 (@lem7597170 _100044 A n h1)). Qed.
Lemma lem7597174 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term200 A.
Proof. exact (proj2 (@lem7597173 _100044 A n h1)). Qed.
Lemma lem7597180 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : term252 _100044 A n.
Proof. exact (proj2 (@lem7597165 _100044 A n h1)). Qed.
Lemma lem7597182 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : term216 _100044 A.
Proof. exact (proj2 (@lem7597180 _100044 A n h1)). Qed.
Lemma lem7597183 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : term66 A n.
Proof. exact (proj1 (@lem7597180 _100044 A n h1)). Qed.
Lemma lem7597184 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : term215 A.
Proof. exact (proj2 (@lem7597182 _100044 A n h1)). Qed.
Lemma lem7597187 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : term201 A.
Proof. exact (proj1 (@lem7597184 _100044 A n h1)). Qed.
Lemma lem7597188 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : term200 A.
Proof. exact (proj2 (@lem7597187 _100044 A n h1)). Qed.
Lemma lem7597199 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (@CARD A (@UNIV A))) = ((@dimindex A s) = (@CARD A (@UNIV A))).
Proof. exact (eq_refl ((@dimindex A s) = (@CARD A (@UNIV A)))). Qed.
Lemma lem7597200 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7597199 A s)). Qed.
Lemma lem7597201 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7597203 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (MK_COMB (@lem7597201 A) (@lem7597200 A)). Qed.
Lemma lem7597204 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term40 A.
Proof. exact (EQ_MP (@lem7597203 A) (@lem7597172 _100044 A n h1)). Qed.
Lemma lem7597244 {A : Type'} (s : A -> Prop) (n : nat) : (term69 A s n) = (term292 A s n).
Proof. exact (@lem19490 (@FINITE A s) (term293 A s n) ((@CARD A s) = n)). Qed.
Lemma lem7597245 {A : Type'} (s : A -> Prop) : (term161 A s) = (term294 A s).
Proof. exact (fun_ext (fun n : nat => @lem7597244 A s n)). Qed.
Lemma lem7597246 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7597247 {A : Type'} (s : A -> Prop) : (term176 A s) = (term295 A s).
Proof. exact (MK_COMB (@lem7597246) (@lem7597245 A s)). Qed.
Lemma lem7597248 {A : Type'} : (term185 A) = (term296 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7597247 A s)). Qed.
Lemma lem7597249 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7597251 {A : Type'} : (term200 A) = (term297 A).
Proof. exact (MK_COMB (@lem7597249 A) (@lem7597248 A)). Qed.
Lemma lem7597252 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term297 A.
Proof. exact (EQ_MP (@lem7597251 A) (@lem7597174 _100044 A n h1)). Qed.
Lemma lem7597359 {A : Type'} (s : A -> Prop) (n : nat) : (term69 A s n) = (term292 A s n).
Proof. exact (@lem19490 (@FINITE A s) (term293 A s n) ((@CARD A s) = n)). Qed.
Lemma lem7597360 {A : Type'} (s : A -> Prop) : (term161 A s) = (term294 A s).
Proof. exact (fun_ext (fun n : nat => @lem7597359 A s n)). Qed.
Lemma lem7597361 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7597362 {A : Type'} (s : A -> Prop) : (term176 A s) = (term295 A s).
Proof. exact (MK_COMB (@lem7597361) (@lem7597360 A s)). Qed.
Lemma lem7597363 {A : Type'} : (term185 A) = (term296 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7597362 A s)). Qed.
Lemma lem7597364 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7597366 {A : Type'} : (term200 A) = (term297 A).
Proof. exact (MK_COMB (@lem7597364 A) (@lem7597363 A)). Qed.
Lemma lem7597367 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : term297 A.
Proof. exact (EQ_MP (@lem7597366 A) (@lem7597188 _100044 A n h1)). Qed.
Lemma lem7597424 {_100044 A : Type'} (_97608 : A -> Prop) (n : nat) (h1 : term242 _100044 A n) : term298 A _97608.
Proof. exact (@lem7597204 _100044 A n h1 _97608). Qed.
Lemma lem7597425 {A : Type'} (_97608 : A -> Prop) : (term298 A _97608) = ((@dimindex A _97608) = (@CARD A (@UNIV A))).
Proof. exact (eq_refl (term298 A _97608)). Qed.
Lemma lem7597433 {_100044 A : Type'} (_97611 : A -> Prop) (n : nat) (h1 : term242 _100044 A n) : term299 A _97611.
Proof. exact (@lem7597252 _100044 A n h1 _97611). Qed.
Lemma lem7597434 {A : Type'} (_97611 : A -> Prop) : (term299 A _97611) = (term295 A _97611).
Proof. exact (eq_refl (term299 A _97611)). Qed.
Lemma lem7597435 {_100044 A : Type'} (_97611 : A -> Prop) (n : nat) (h1 : term242 _100044 A n) : term295 A _97611.
Proof. exact (EQ_MP (@lem7597434 A _97611) (@lem7597433 _100044 A _97611 n h1)). Qed.
Lemma lem7597436 {_100044 A : Type'} (_97611 : A -> Prop) (_97612 : nat) (n : nat) (h1 : term242 _100044 A n) : term300 A _97611 _97612.
Proof. exact (@lem7597435 _100044 A _97611 n h1 _97612). Qed.
Lemma lem7597437 {A : Type'} (_97611 : A -> Prop) (_97612 : nat) : (term300 A _97611 _97612) = (term292 A _97611 _97612).
Proof. exact (eq_refl (term300 A _97611 _97612)). Qed.
Lemma lem7597438 {_100044 A : Type'} (_97611 : A -> Prop) (_97612 : nat) (n : nat) (h1 : term242 _100044 A n) : term292 A _97611 _97612.
Proof. exact (EQ_MP (@lem7597437 A _97611 _97612) (@lem7597436 _100044 A _97611 _97612 n h1)). Qed.
Lemma lem7597460 {_100044 A : Type'} (_97620 : A -> Prop) (n : nat) (h1 : term265 _100044 A n) : term299 A _97620.
Proof. exact (@lem7597367 _100044 A n h1 _97620). Qed.
Lemma lem7597461 {A : Type'} (_97620 : A -> Prop) : (term299 A _97620) = (term295 A _97620).
Proof. exact (eq_refl (term299 A _97620)). Qed.
Lemma lem7597462 {_100044 A : Type'} (_97620 : A -> Prop) (n : nat) (h1 : term265 _100044 A n) : term295 A _97620.
Proof. exact (EQ_MP (@lem7597461 A _97620) (@lem7597460 _100044 A _97620 n h1)). Qed.
Lemma lem7597463 {_100044 A : Type'} (_97620 : A -> Prop) (_97621 : nat) (n : nat) (h1 : term265 _100044 A n) : term300 A _97620 _97621.
Proof. exact (@lem7597462 _100044 A _97620 n h1 _97621). Qed.
Lemma lem7597464 {A : Type'} (_97620 : A -> Prop) (_97621 : nat) : (term300 A _97620 _97621) = (term292 A _97620 _97621).
Proof. exact (eq_refl (term300 A _97620 _97621)). Qed.
Lemma lem7597465 {_100044 A : Type'} (_97620 : A -> Prop) (_97621 : nat) (n : nat) (h1 : term265 _100044 A n) : term292 A _97620 _97621.
Proof. exact (EQ_MP (@lem7597464 A _97620 _97621) (@lem7597463 _100044 A _97620 _97621 n h1)). Qed.
Lemma lem7597513 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term301 A n.
Proof. exact (proj2 (@lem7597169 _100044 A n h1)). Qed.
Lemma lem7597537 {_100044 A : Type'} (_97611 : A -> Prop) (_97612 : nat) (n : nat) (h1 : term242 _100044 A n) : term302 A _97611 _97612.
Proof. exact (proj2 (@lem7597438 _100044 A _97611 _97612 n h1)). Qed.
Lemma lem7597539 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : term109 A.
Proof. exact (proj1 (@lem7597165 _100044 A n h1)). Qed.
Lemma lem7597583 {_100044 A : Type'} (_97621 : nat) (_97620 : A -> Prop) (n : nat) (h1 : term265 _100044 A n) : term303 A _97621 _97620.
Proof. exact (proj1 (@lem7597465 _100044 A _97620 _97621 n h1)). Qed.
Lemma lem7597677 (x : nat) (y : nat) (z : nat) : term304 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem7597683 {_100044 A : Type'} (_97608 : A -> Prop) (n : nat) (h1 : term242 _100044 A n) : (@dimindex A _97608) = (@CARD A (@UNIV A)).
Proof. exact (EQ_MP (@lem7597425 A _97608) (@lem7597424 _100044 A _97608 n h1)). Qed.
Lemma lem7597684 {_100044 A : Type'} (_97608 : A -> Prop) (n : nat) (h1 : term242 _100044 A n) : (@dimindex A _97608) = (@CARD A (@UNIV A)).
Proof. exact (@lem7597683 _100044 A _97608 n h1). Qed.
Lemma lem7597685 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : (@dimindex A (@UNIV A)) = (@CARD A (@UNIV A)).
Proof. exact (@lem7597684 _100044 A (@UNIV A) n h1). Qed.
Lemma lem7597686 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term305 A.
Proof. exact (fun h0 : term306 A => @lem7597685 _100044 A n h1). Qed.
Lemma lem7597688 (p : Prop) : (term307 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7597689 {A : Type'} : (term305 A) = ((@dimindex A (@UNIV A)) = (@CARD A (@UNIV A))).
Proof. exact (@lem7597688 ((@dimindex A (@UNIV A)) = (@CARD A (@UNIV A)))). Qed.
Lemma lem7597690 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : (@dimindex A (@UNIV A)) = (@CARD A (@UNIV A)).
Proof. exact (EQ_MP (@lem7597689 A) (@lem7597686 _100044 A n h1)). Qed.
Lemma lem7597692 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem7597693 {A : Type'} : (@dimindex A (@UNIV A)) = (@dimindex A (@UNIV A)).
Proof. exact (@lem7597692 (@dimindex A (@UNIV A))). Qed.
Lemma lem7597694 {A : Type'} : term308 A.
Proof. exact (fun h0 : term309 A => @lem7597693 A). Qed.
Lemma lem7597696 (p : Prop) : (term307 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7597697 {A : Type'} : (term308 A) = ((@dimindex A (@UNIV A)) = (@dimindex A (@UNIV A))).
Proof. exact (@lem7597696 ((@dimindex A (@UNIV A)) = (@dimindex A (@UNIV A)))). Qed.
Lemma lem7597698 {A : Type'} : (@dimindex A (@UNIV A)) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7597697 A) (@lem7597694 A)). Qed.
Lemma lem7597716 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7597717 (y : nat) (x : nat) (z : nat) : (term310 x y z) = (term311 y x z).
Proof. exact (@lem7597716 (y = z) (term312 x z)). Qed.
Lemma lem7597727 (x : nat) (y : nat) : (term313 x y) = (term313 x y).
Proof. exact (eq_refl (term313 x y)). Qed.
Lemma lem7597728 (y : nat) (x : nat) (z : nat) : (term304 x y z) = (term314 y x z).
Proof. exact (MK_COMB (@lem7597727 x y) (@lem7597717 y x z)). Qed.
Lemma lem7597732 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7597733 (y : nat) (x : nat) (z : nat) : (term314 y x z) = (term316 y x z).
Proof. exact (@lem7597732 (y = z) (term312 x y) (term312 x z)). Qed.
Lemma lem7597755 (y : nat) (x : nat) (z : nat) : (term304 x y z) = (term316 y x z).
Proof. exact (TRANS (@lem7597728 y x z) (@lem7597733 y x z)). Qed.
Lemma lem7597756 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7597757 (y : nat) (x : nat) (z : nat) : (term317 x y z) = (term318 y x z).
Proof. exact (MK_COMB (@lem7597756) (@lem7597755 y x z)). Qed.
Lemma lem7597779 (y : nat) (x : nat) (z : nat) : (term316 y x z) = (term316 y x z).
Proof. exact (eq_refl (term316 y x z)). Qed.
Lemma lem7597780 (y : nat) (x : nat) (z : nat) : ((term304 x y z) = (term316 y x z)) = ((term316 y x z) = (term316 y x z)).
Proof. exact (MK_COMB (@lem7597757 y x z) (@lem7597779 y x z)). Qed.
Lemma lem7597782 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7597783 (x : Prop) : (x = x) = True.
Proof. exact (@lem7597782 Prop x). Qed.
Lemma lem7597784 (y : nat) (x : nat) (z : nat) : ((term316 y x z) = (term316 y x z)) = True.
Proof. exact (@lem7597783 (term316 y x z)). Qed.
Lemma lem7597785 (y : nat) (x : nat) (z : nat) : ((term304 x y z) = (term316 y x z)) = True.
Proof. exact (TRANS (@lem7597780 y x z) (@lem7597784 y x z)). Qed.
Lemma lem7597786 (y : nat) (x : nat) (z : nat) : True = ((term304 x y z) = (term316 y x z)).
Proof. exact (SYM (@lem7597785 y x z)). Qed.
Lemma lem7597787 (y : nat) (x : nat) (z : nat) : (term304 x y z) = (term316 y x z).
Proof. exact (EQ_MP (@lem7597786 y x z) (@lem0)). Qed.
Lemma lem7597788 (y : nat) (x : nat) (z : nat) : term316 y x z.
Proof. exact (EQ_MP (@lem7597787 y x z) (@lem7597677 x y z)). Qed.
Lemma lem7597790 (b : Prop) (a : Prop) : (a \/ b) = (term319 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7597791 (x : nat) (y : nat) (z : nat) : (term316 y x z) = (term320 x y z).
Proof. exact (@lem7597790 (term321 y x z) (y = z)). Qed.
Lemma lem7597793 (a : Prop) (b : Prop) : (term322 a b) = (term323 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7597794 (y : nat) (x : nat) (z : nat) : (term324 y x z) = (term325 y x z).
Proof. exact (@lem7597793 (term312 x y) (term312 x z)). Qed.
Lemma lem7597796 (a : Prop) : (term326 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7597797 (x : nat) (y : nat) : (term327 x y) = (x = y).
Proof. exact (@lem7597796 (x = y)). Qed.
Lemma lem7597798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7597799 (x : nat) (y : nat) : (term328 x y) = (term329 x y).
Proof. exact (MK_COMB (@lem7597798) (@lem7597797 x y)). Qed.
Lemma lem7597801 (a : Prop) : (term326 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7597802 (x : nat) (z : nat) : (term327 x z) = (x = z).
Proof. exact (@lem7597801 (x = z)). Qed.
Lemma lem7597803 (y : nat) (x : nat) (z : nat) : (term325 y x z) = (term330 y x z).
Proof. exact (MK_COMB (@lem7597799 x y) (@lem7597802 x z)). Qed.
Lemma lem7597804 (y : nat) (x : nat) (z : nat) : (term324 y x z) = (term330 y x z).
Proof. exact (TRANS (@lem7597794 y x z) (@lem7597803 y x z)). Qed.
Lemma lem7597805 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7597806 (y : nat) (x : nat) (z : nat) : (term331 y x z) = (term332 y x z).
Proof. exact (MK_COMB (@lem7597805) (@lem7597804 y x z)). Qed.
Lemma lem7597807 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7597808 (x : nat) (y : nat) (z : nat) : (term320 x y z) = (term333 x y z).
Proof. exact (MK_COMB (@lem7597806 y x z) (@lem7597807 y z)). Qed.
Lemma lem7597809 (x : nat) (y : nat) (z : nat) : (term316 y x z) = (term333 x y z).
Proof. exact (TRANS (@lem7597791 x y z) (@lem7597808 x y z)). Qed.
Lemma lem7597811 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term334 A.
Proof. exact (conj (@lem7597690 _100044 A n h1) (@lem7597698 A)). Qed.
Lemma lem7597813 (x : nat) (y : nat) (z : nat) : term333 x y z.
Proof. exact (EQ_MP (@lem7597809 x y z) (@lem7597788 y x z)). Qed.
Lemma lem7597814 {A : Type'} : term335 A.
Proof. exact (@lem7597813 (@dimindex A (@UNIV A)) (@CARD A (@UNIV A)) (@dimindex A (@UNIV A))). Qed.
Lemma lem7597817 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : (@CARD A (@UNIV A)) = (@dimindex A (@UNIV A)).
Proof. exact (@lem7597814 A (@lem7597811 _100044 A n h1)). Qed.
Lemma lem7597818 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term336 A.
Proof. exact (fun h0 : term337 A => @lem7597817 _100044 A n h1). Qed.
Lemma lem7597820 (p : Prop) : (term307 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7597821 {A : Type'} : (term336 A) = ((@CARD A (@UNIV A)) = (@dimindex A (@UNIV A))).
Proof. exact (@lem7597820 ((@CARD A (@UNIV A)) = (@dimindex A (@UNIV A)))). Qed.
Lemma lem7597822 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : (@CARD A (@UNIV A)) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7597821 A) (@lem7597818 _100044 A n h1)). Qed.
Lemma lem7597824 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : @HAS_SIZE A (@UNIV A) n.
Proof. exact (proj1 (@lem7597169 _100044 A n h1)). Qed.
Lemma lem7597825 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term338 A n.
Proof. exact (fun h0 : term339 A n => @lem7597824 _100044 A n h1). Qed.
Lemma lem7597827 (p : Prop) : (term307 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7597828 {A : Type'} (n : nat) : (term338 A n) = (@HAS_SIZE A (@UNIV A) n).
Proof. exact (@lem7597827 (@HAS_SIZE A (@UNIV A) n)). Qed.
Lemma lem7597829 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : @HAS_SIZE A (@UNIV A) n.
Proof. exact (EQ_MP (@lem7597828 A n) (@lem7597825 _100044 A n h1)). Qed.
Lemma lem7597835 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7597836 {A : Type'} (_97611 : A -> Prop) (_97612 : nat) : (term302 A _97611 _97612) = (term340 A _97611 _97612).
Proof. exact (@lem7597835 ((@CARD A _97611) = _97612) (term293 A _97611 _97612)). Qed.
Lemma lem7597844 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7597845 {A : Type'} (_97611 : A -> Prop) (_97612 : nat) : (term341 A _97611 _97612) = (term342 A _97611 _97612).
Proof. exact (MK_COMB (@lem7597844) (@lem7597836 A _97611 _97612)). Qed.
Lemma lem7597853 {A : Type'} (_97611 : A -> Prop) (_97612 : nat) : (term340 A _97611 _97612) = (term340 A _97611 _97612).
Proof. exact (eq_refl (term340 A _97611 _97612)). Qed.
Lemma lem7597854 {A : Type'} (_97611 : A -> Prop) (_97612 : nat) : ((term302 A _97611 _97612) = (term340 A _97611 _97612)) = ((term340 A _97611 _97612) = (term340 A _97611 _97612)).
Proof. exact (MK_COMB (@lem7597845 A _97611 _97612) (@lem7597853 A _97611 _97612)). Qed.
Lemma lem7597856 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7597857 (x : Prop) : (x = x) = True.
Proof. exact (@lem7597856 Prop x). Qed.
Lemma lem7597858 {A : Type'} (_97611 : A -> Prop) (_97612 : nat) : ((term340 A _97611 _97612) = (term340 A _97611 _97612)) = True.
Proof. exact (@lem7597857 (term340 A _97611 _97612)). Qed.
Lemma lem7597859 {A : Type'} (_97611 : A -> Prop) (_97612 : nat) : ((term302 A _97611 _97612) = (term340 A _97611 _97612)) = True.
Proof. exact (TRANS (@lem7597854 A _97611 _97612) (@lem7597858 A _97611 _97612)). Qed.
Lemma lem7597860 {A : Type'} (_97611 : A -> Prop) (_97612 : nat) : True = ((term302 A _97611 _97612) = (term340 A _97611 _97612)).
Proof. exact (SYM (@lem7597859 A _97611 _97612)). Qed.
Lemma lem7597861 {A : Type'} (_97611 : A -> Prop) (_97612 : nat) : (term302 A _97611 _97612) = (term340 A _97611 _97612).
Proof. exact (EQ_MP (@lem7597860 A _97611 _97612) (@lem0)). Qed.
Lemma lem7597862 {_100044 A : Type'} (_97611 : A -> Prop) (_97612 : nat) (n : nat) (h1 : term242 _100044 A n) : term340 A _97611 _97612.
Proof. exact (EQ_MP (@lem7597861 A _97611 _97612) (@lem7597537 _100044 A _97611 _97612 n h1)). Qed.
Lemma lem7597864 (b : Prop) (a : Prop) : (a \/ b) = (term319 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7597865 {A : Type'} (_97611 : A -> Prop) (_97612 : nat) : (term340 A _97611 _97612) = (term343 A _97611 _97612).
Proof. exact (@lem7597864 (term293 A _97611 _97612) ((@CARD A _97611) = _97612)). Qed.
Lemma lem7597867 (a : Prop) : (term326 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7597868 {A : Type'} (_97611 : A -> Prop) (_97612 : nat) : (term344 A _97611 _97612) = (@HAS_SIZE A _97611 _97612).
Proof. exact (@lem7597867 (@HAS_SIZE A _97611 _97612)). Qed.
Lemma lem7597869 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7597870 {A : Type'} (_97611 : A -> Prop) (_97612 : nat) : (term345 A _97611 _97612) = (term346 A _97611 _97612).
Proof. exact (MK_COMB (@lem7597869) (@lem7597868 A _97611 _97612)). Qed.
Lemma lem7597871 {A : Type'} (_97611 : A -> Prop) (_97612 : nat) : ((@CARD A _97611) = _97612) = ((@CARD A _97611) = _97612).
Proof. exact (eq_refl ((@CARD A _97611) = _97612)). Qed.
Lemma lem7597872 {A : Type'} (_97611 : A -> Prop) (_97612 : nat) : (term343 A _97611 _97612) = (term347 A _97611 _97612).
Proof. exact (MK_COMB (@lem7597870 A _97611 _97612) (@lem7597871 A _97611 _97612)). Qed.
Lemma lem7597873 {A : Type'} (_97611 : A -> Prop) (_97612 : nat) : (term340 A _97611 _97612) = (term347 A _97611 _97612).
Proof. exact (TRANS (@lem7597865 A _97611 _97612) (@lem7597872 A _97611 _97612)). Qed.
Lemma lem7597876 {_100044 A : Type'} (_97611 : A -> Prop) (_97612 : nat) (n : nat) (h1 : term242 _100044 A n) : term347 A _97611 _97612.
Proof. exact (EQ_MP (@lem7597873 A _97611 _97612) (@lem7597862 _100044 A _97611 _97612 n h1)). Qed.
Lemma lem7597877 {_100044 A : Type'} (_97611 : A -> Prop) (_97612 : nat) (n : nat) (h1 : term242 _100044 A n) : term347 A _97611 _97612.
Proof. exact (@lem7597876 _100044 A _97611 _97612 n h1). Qed.
Lemma lem7597878 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term348 A n.
Proof. exact (@lem7597877 _100044 A (@UNIV A) n n h1). Qed.
Lemma lem7597881 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : (@CARD A (@UNIV A)) = n.
Proof. exact (@lem7597878 _100044 A n h1 (@lem7597829 _100044 A n h1)). Qed.
Lemma lem7597882 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term349 A n.
Proof. exact (fun h0 : term350 A n => @lem7597881 _100044 A n h1). Qed.
Lemma lem7597884 (p : Prop) : (term307 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7597885 {A : Type'} (n : nat) : (term349 A n) = ((@CARD A (@UNIV A)) = n).
Proof. exact (@lem7597884 ((@CARD A (@UNIV A)) = n)). Qed.
Lemma lem7597886 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : (@CARD A (@UNIV A)) = n.
Proof. exact (EQ_MP (@lem7597885 A n) (@lem7597882 _100044 A n h1)). Qed.
Lemma lem7597887 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term351 A n.
Proof. exact (conj (@lem7597822 _100044 A n h1) (@lem7597886 _100044 A n h1)). Qed.
Lemma lem7597889 (x : nat) (y : nat) (z : nat) : term333 x y z.
Proof. exact (EQ_MP (@lem7597809 x y z) (@lem7597788 y x z)). Qed.
Lemma lem7597890 {A : Type'} (n : nat) : term352 A n.
Proof. exact (@lem7597889 (@CARD A (@UNIV A)) (@dimindex A (@UNIV A)) n). Qed.
Lemma lem7597893 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : (@dimindex A (@UNIV A)) = n.
Proof. exact (@lem7597890 A n (@lem7597887 _100044 A n h1)). Qed.
Lemma lem7597894 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term353 A n.
Proof. exact (fun h0 : term301 A n => @lem7597893 _100044 A n h1). Qed.
Lemma lem7597896 (p : Prop) : (term307 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7597897 {A : Type'} (n : nat) : (term353 A n) = ((@dimindex A (@UNIV A)) = n).
Proof. exact (@lem7597896 ((@dimindex A (@UNIV A)) = n)). Qed.
Lemma lem7597898 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : (@dimindex A (@UNIV A)) = n.
Proof. exact (EQ_MP (@lem7597897 A n) (@lem7597894 _100044 A n h1)). Qed.
Lemma lem7597901 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7597903 {A : Type'} (n : nat) : (term301 A n) = (term354 A n).
Proof. exact (@lem7597901 ((@dimindex A (@UNIV A)) = n)). Qed.
Lemma lem7597906 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term354 A n.
Proof. exact (EQ_MP (@lem7597903 A n) (@lem7597513 _100044 A n h1)). Qed.
Lemma lem7597909 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : False.
Proof. exact (@lem7597906 _100044 A n h1 (@lem7597898 _100044 A n h1)). Qed.
Lemma lem7597910 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : term355.
Proof. exact (fun h0 : ~ False => @lem7597909 _100044 A n h1). Qed.
Lemma lem7597912 (p : Prop) : (term307 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7597913 : term355 = False.
Proof. exact (@lem7597912 False). Qed.
Lemma lem7597914 {_100044 A : Type'} (n : nat) (h1 : term242 _100044 A n) : False.
Proof. exact (EQ_MP (@lem7597913) (@lem7597910 _100044 A n h1)). Qed.
Lemma lem7598024 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : @HAS_SIZE A (@UNIV A) n.
Proof. exact (proj1 (@lem7597183 _100044 A n h1)). Qed.
Lemma lem7598025 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : term338 A n.
Proof. exact (fun h0 : term339 A n => @lem7598024 _100044 A n h1). Qed.
Lemma lem7598027 (p : Prop) : (term307 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7598028 {A : Type'} (n : nat) : (term338 A n) = (@HAS_SIZE A (@UNIV A) n).
Proof. exact (@lem7598027 (@HAS_SIZE A (@UNIV A) n)). Qed.
Lemma lem7598029 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : @HAS_SIZE A (@UNIV A) n.
Proof. exact (EQ_MP (@lem7598028 A n) (@lem7598025 _100044 A n h1)). Qed.
Lemma lem7598035 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7598036 {A : Type'} (_97620 : A -> Prop) (_97621 : nat) : (term303 A _97621 _97620) = (term356 A _97620 _97621).
Proof. exact (@lem7598035 (@FINITE A _97620) (term293 A _97620 _97621)). Qed.
Lemma lem7598042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7598043 {A : Type'} (_97620 : A -> Prop) (_97621 : nat) : (term357 A _97621 _97620) = (term358 A _97620 _97621).
Proof. exact (MK_COMB (@lem7598042) (@lem7598036 A _97620 _97621)). Qed.
Lemma lem7598049 {A : Type'} (_97620 : A -> Prop) (_97621 : nat) : (term356 A _97620 _97621) = (term356 A _97620 _97621).
Proof. exact (eq_refl (term356 A _97620 _97621)). Qed.
Lemma lem7598050 {A : Type'} (_97620 : A -> Prop) (_97621 : nat) : ((term303 A _97621 _97620) = (term356 A _97620 _97621)) = ((term356 A _97620 _97621) = (term356 A _97620 _97621)).
Proof. exact (MK_COMB (@lem7598043 A _97620 _97621) (@lem7598049 A _97620 _97621)). Qed.
Lemma lem7598052 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7598053 (x : Prop) : (x = x) = True.
Proof. exact (@lem7598052 Prop x). Qed.
Lemma lem7598054 {A : Type'} (_97620 : A -> Prop) (_97621 : nat) : ((term356 A _97620 _97621) = (term356 A _97620 _97621)) = True.
Proof. exact (@lem7598053 (term356 A _97620 _97621)). Qed.
Lemma lem7598055 {A : Type'} (_97620 : A -> Prop) (_97621 : nat) : ((term303 A _97621 _97620) = (term356 A _97620 _97621)) = True.
Proof. exact (TRANS (@lem7598050 A _97620 _97621) (@lem7598054 A _97620 _97621)). Qed.
Lemma lem7598056 {A : Type'} (_97620 : A -> Prop) (_97621 : nat) : True = ((term303 A _97621 _97620) = (term356 A _97620 _97621)).
Proof. exact (SYM (@lem7598055 A _97620 _97621)). Qed.
Lemma lem7598057 {A : Type'} (_97620 : A -> Prop) (_97621 : nat) : (term303 A _97621 _97620) = (term356 A _97620 _97621).
Proof. exact (EQ_MP (@lem7598056 A _97620 _97621) (@lem0)). Qed.
Lemma lem7598058 {_100044 A : Type'} (_97620 : A -> Prop) (_97621 : nat) (n : nat) (h1 : term265 _100044 A n) : term356 A _97620 _97621.
Proof. exact (EQ_MP (@lem7598057 A _97620 _97621) (@lem7597583 _100044 A _97621 _97620 n h1)). Qed.
Lemma lem7598060 (b : Prop) (a : Prop) : (a \/ b) = (term319 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7598061 {A : Type'} (_97621 : nat) (_97620 : A -> Prop) : (term356 A _97620 _97621) = (term359 A _97621 _97620).
Proof. exact (@lem7598060 (term293 A _97620 _97621) (@FINITE A _97620)). Qed.
Lemma lem7598063 (a : Prop) : (term326 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7598064 {A : Type'} (_97620 : A -> Prop) (_97621 : nat) : (term344 A _97620 _97621) = (@HAS_SIZE A _97620 _97621).
Proof. exact (@lem7598063 (@HAS_SIZE A _97620 _97621)). Qed.
Lemma lem7598065 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598066 {A : Type'} (_97620 : A -> Prop) (_97621 : nat) : (term345 A _97620 _97621) = (term346 A _97620 _97621).
Proof. exact (MK_COMB (@lem7598065) (@lem7598064 A _97620 _97621)). Qed.
Lemma lem7598067 {A : Type'} (_97620 : A -> Prop) : (@FINITE A _97620) = (@FINITE A _97620).
Proof. exact (eq_refl (@FINITE A _97620)). Qed.
Lemma lem7598068 {A : Type'} (_97621 : nat) (_97620 : A -> Prop) : (term359 A _97621 _97620) = (term360 A _97621 _97620).
Proof. exact (MK_COMB (@lem7598066 A _97620 _97621) (@lem7598067 A _97620)). Qed.
Lemma lem7598069 {A : Type'} (_97621 : nat) (_97620 : A -> Prop) : (term356 A _97620 _97621) = (term360 A _97621 _97620).
Proof. exact (TRANS (@lem7598061 A _97621 _97620) (@lem7598068 A _97621 _97620)). Qed.
Lemma lem7598072 {_100044 A : Type'} (_97621 : nat) (_97620 : A -> Prop) (n : nat) (h1 : term265 _100044 A n) : term360 A _97621 _97620.
Proof. exact (EQ_MP (@lem7598069 A _97621 _97620) (@lem7598058 _100044 A _97620 _97621 n h1)). Qed.
Lemma lem7598073 {_100044 A : Type'} (_97621 : nat) (_97620 : A -> Prop) (n : nat) (h1 : term265 _100044 A n) : term360 A _97621 _97620.
Proof. exact (@lem7598072 _100044 A _97621 _97620 n h1). Qed.
Lemma lem7598074 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : term361 A n.
Proof. exact (@lem7598073 _100044 A n (@UNIV A) n h1). Qed.
Lemma lem7598077 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : @FINITE A (@UNIV A).
Proof. exact (@lem7598074 _100044 A n h1 (@lem7598029 _100044 A n h1)). Qed.
Lemma lem7598078 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : term362 A.
Proof. exact (fun h0 : term109 A => @lem7598077 _100044 A n h1). Qed.
Lemma lem7598080 (p : Prop) : (term307 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7598081 {A : Type'} : (term362 A) = (@FINITE A (@UNIV A)).
Proof. exact (@lem7598080 (@FINITE A (@UNIV A))). Qed.
Lemma lem7598082 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : @FINITE A (@UNIV A).
Proof. exact (EQ_MP (@lem7598081 A) (@lem7598078 _100044 A n h1)). Qed.
Lemma lem7598085 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7598087 {A : Type'} : (term109 A) = (term363 A).
Proof. exact (@lem7598085 (@FINITE A (@UNIV A))). Qed.
Lemma lem7598090 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : term363 A.
Proof. exact (EQ_MP (@lem7598087 A) (@lem7597539 _100044 A n h1)). Qed.
Lemma lem7598093 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : False.
Proof. exact (@lem7598090 _100044 A n h1 (@lem7598082 _100044 A n h1)). Qed.
Lemma lem7598094 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : term355.
Proof. exact (fun h0 : ~ False => @lem7598093 _100044 A n h1). Qed.
Lemma lem7598096 (p : Prop) : (term307 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7598097 : term355 = False.
Proof. exact (@lem7598096 False). Qed.
Lemma lem7598098 {_100044 A : Type'} (n : nat) (h1 : term265 _100044 A n) : False.
Proof. exact (EQ_MP (@lem7598097) (@lem7598094 _100044 A n h1)). Qed.
Lemma lem7598099 {_100044 A : Type'} (n : nat) (h1 : term288 _100044 A n) : False.
Proof. exact (or_elim (@lem7597163 _100044 A n h1) (fun h0 : term242 _100044 A n => @lem7597914 _100044 A n h0) (fun h0 : term265 _100044 A n => @lem7598098 _100044 A n h0)). Qed.
Lemma lem7598100 {_100044 A : Type'} (n : nat) (h1 : term288 _100044 A n) : (term288 _100044 A n) = False.
Proof. exact (prop_ext (fun h2 : term288 _100044 A n => @lem7598099 _100044 A n h1) (fun h2 : False => @lem7597163 _100044 A n h1)). Qed.
Lemma lem7598101 {_100044 A : Type'} (n : nat) (h1 : term288 _100044 A n) : False.
Proof. exact (EQ_MP (@lem7598100 _100044 A n h1) (@lem7597163 _100044 A n h1)). Qed.
Lemma lem7598102 {_100044 A : Type'} (h1 : term64 _100044 A) : False.
Proof. exact (ex_elim (@lem7596814 _100044 A h1) (fun n : nat => fun h0 : term290 _100044 A n => @lem7598101 _100044 A n h0)). Qed.
Lemma lem7598103 {_100044 A : Type'} (h1 : term64 _100044 A) : (term64 _100044 A) = False.
Proof. exact (prop_ext (fun h2 : term64 _100044 A => @lem7598102 _100044 A h1) (fun h2 : False => @lem7595200 _100044 A h1)). Qed.
Lemma lem7598104 {_100044 A : Type'} (h1 : term64 _100044 A) : False.
Proof. exact (EQ_MP (@lem7598103 _100044 A h1) (@lem7595200 _100044 A h1)). Qed.
Lemma lem7598105 {_100044 A : Type'} : term63 _100044 A.
Proof. exact (fun h0 : term64 _100044 A => @lem7598104 _100044 A h0). Qed.
Lemma lem7598106 {_100044 A : Type'} : term51 _100044 A.
Proof. exact (EQ_MP (@lem7595199 _100044 A) (@lem7598105 _100044 A)). Qed.
Lemma lem7598107 {_100044 A : Type'} : term18 _100044 A.
Proof. exact (EQ_MP (@lem7595195 _100044 A) (@lem7598106 _100044 A)). Qed.
Lemma lem7598108 {_100044 A : Type'} (n : nat) : term364 _100044 A n.
Proof. exact (@lem7598107 _100044 A n). Qed.
Lemma lem7598109 {_100044 A : Type'} (n : nat) : (term364 _100044 A n) = (term2 _100044 A n).
Proof. exact (eq_refl (term364 _100044 A n)). Qed.
Lemma lem7598110 {_100044 A : Type'} (n : nat) : term2 _100044 A n.
Proof. exact (EQ_MP (@lem7598109 _100044 A n) (@lem7598108 _100044 A n)). Qed.
Lemma lem7598112 {_100044 A : Type'} (n : nat) : term2 _100044 A n.
Proof. exact (@lem7594724 _100044 A n (@lem7598110 _100044 A n)). Qed.
Lemma lem7598113 {_100044 A : Type'} (n : nat) (h1 : term0 A n) : term12 _100044 A.
Proof. exact (@lem7598112 _100044 A n (@lem7594703 A n h1)). Qed.
Lemma lem7598114 {A : Type'} (n : nat) (h1 : term0 A n) : term10 A.
Proof. exact (@lem7598113 Prop A n h1 (@lem3863773 Prop)). Qed.
Lemma lem7598115 {A : Type'} (n : nat) (h1 : term0 A n) : term6 A.
Proof. exact (@lem7598114 A n h1 (@lem7594706 A)). Qed.
Lemma lem7598116 {A : Type'} (n : nat) (h1 : term0 A n) : False.
Proof. exact (@lem7598115 A n h1 (@lem7590231 A)). Qed.
Lemma lem7598117 {A : Type'} (n : nat) (h1 : term0 A n) : (term0 A n) = False.
Proof. exact (prop_ext (fun h2 : term0 A n => @lem7598116 A n h1) (fun h2 : False => @lem7594703 A n h1)). Qed.
Lemma lem7598118 {A : Type'} (n : nat) (h1 : term0 A n) : False.
Proof. exact (EQ_MP (@lem7598117 A n h1) (@lem7594703 A n h1)). Qed.
Lemma lem7598119 {A : Type'} (n : nat) : term365 A n.
Proof. exact (fun h0 : term0 A n => @lem7598118 A n h0). Qed.
