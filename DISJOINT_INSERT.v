Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJOINT_INSERT_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211738_spec.
Require Import thm3211739_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3284794 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem3284795 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3284794 A s t). Qed.
Lemma lem3284796 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term0 A x s t) = ((term1 A x s t) = (@EMPTY A)).
Proof. exact (@lem3284795 A (@INSERT A x s) t). Qed.
Lemma lem3284800 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3284801 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (@lem3284800 A s t). Qed.
Lemma lem3284802 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term1 A x s t) = (@EMPTY A)) = (term3 A x s t).
Proof. exact (@lem3284801 A (term1 A x s t) (@EMPTY A)). Qed.
Lemma lem3284807 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term0 A x s t) = (term3 A x s t).
Proof. exact (TRANS (@lem3284796 A x s t) (@lem3284802 A x s t)). Qed.
Lemma lem3284812 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3284813 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term4 A x s t) = (term5 A x s t).
Proof. exact (MK_COMB (@lem3284812) (@lem3284807 A x s t)). Qed.
Lemma lem3284817 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem3284818 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3284817 A s t). Qed.
Lemma lem3284822 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3284823 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (@lem3284822 A s t). Qed.
Lemma lem3284824 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@INTER A s t) = (@EMPTY A)) = (term6 A s t).
Proof. exact (@lem3284823 A (@INTER A s t) (@EMPTY A)). Qed.
Lemma lem3284829 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = (term6 A s t).
Proof. exact (TRANS (@lem3284818 A s t) (@lem3284824 A s t)). Qed.
Lemma lem3284834 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3284835 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = (term8 A s t).
Proof. exact (MK_COMB (@lem3284834) (@lem3284829 A s t)). Qed.
Lemma lem3284836 {A : Type'} (x : A) (t : A -> Prop) : (term9 A x t) = (term9 A x t).
Proof. exact (eq_refl (term9 A x t)). Qed.
Lemma lem3284837 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A s x t) = (term11 A s x t).
Proof. exact (MK_COMB (@lem3284835 A s t) (@lem3284836 A x t)). Qed.
Lemma lem3284840 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term0 A x s t) = (term10 A s x t)) = ((term3 A x s t) = (term11 A s x t)).
Proof. exact (MK_COMB (@lem3284813 A x s t) (@lem3284837 A s x t)). Qed.
Lemma lem3284845 {A : Type'} (s : A -> Prop) (x : A) : (term12 A s x) = (term13 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3284840 A s x t)). Qed.
Lemma lem3284846 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3284847 {A : Type'} (s : A -> Prop) (x : A) : (term14 A s x) = (term15 A s x).
Proof. exact (MK_COMB (@lem3284846 A) (@lem3284845 A s x)). Qed.
Lemma lem3284852 {A : Type'} (x : A) : (term16 A x) = (term17 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3284847 A s x)). Qed.
Lemma lem3284853 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3284854 {A : Type'} (x : A) : (term18 A x) = (term19 A x).
Proof. exact (MK_COMB (@lem3284853 A) (@lem3284852 A x)). Qed.
Lemma lem3284859 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (fun_ext (fun x : A => @lem3284854 A x)). Qed.
Lemma lem3284860 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3284861 {A : Type'} : (term22 A) = (term23 A).
Proof. exact (MK_COMB (@lem3284860 A) (@lem3284859 A)). Qed.
Lemma lem3284866 {A : Type'} : (term23 A) = (term22 A).
Proof. exact (SYM (@lem3284861 A)). Qed.
Lemma lem3284888 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term24 A x s t) = (term25 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3284889 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term24 A x s t) = (term25 A s x t).
Proof. exact (@lem3284888 A s x t). Qed.
Lemma lem3284890 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term26 A x' x s t) = (term27 A x s x' t).
Proof. exact (@lem3284889 A (@INSERT A x s) x' t). Qed.
Lemma lem3284894 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term28 A x y s) = (term29 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3284895 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term28 A x y s) = (term29 A y x s).
Proof. exact (@lem3284894 A y x s). Qed.
Lemma lem3284896 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term28 A x' x s) = (term29 A x x' s).
Proof. exact (@lem3284895 A x x' s). Qed.
Lemma lem3284902 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3284903 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3284902 A P x). Qed.
Lemma lem3284904 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3284903 A s x'). Qed.
Lemma lem3284905 {A : Type'} (x' : A) (x : A) : (term30 A x' x) = (term30 A x' x).
Proof. exact (eq_refl (term30 A x' x)). Qed.
Lemma lem3284906 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term29 A x x' s) = (term31 A x s x').
Proof. exact (MK_COMB (@lem3284905 A x' x) (@lem3284904 A s x')). Qed.
Lemma lem3284909 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term28 A x' x s) = (term31 A x s x').
Proof. exact (TRANS (@lem3284896 A x x' s) (@lem3284906 A x s x')). Qed.
Lemma lem3284910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3284911 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term32 A x' x s) = (term33 A x s x').
Proof. exact (MK_COMB (@lem3284910) (@lem3284909 A x s x')). Qed.
Lemma lem3284913 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3284914 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3284913 A P x). Qed.
Lemma lem3284915 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3284914 A t x'). Qed.
Lemma lem3284916 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term27 A x s x' t) = (term34 A x s t x').
Proof. exact (MK_COMB (@lem3284911 A x s x') (@lem3284915 A t x')). Qed.
Lemma lem3284919 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term26 A x' x s t) = (term34 A x s t x').
Proof. exact (TRANS (@lem3284890 A x s x' t) (@lem3284916 A x s t x')). Qed.
Lemma lem3284920 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3284921 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term35 A x' x s t) = (term36 A x s t x').
Proof. exact (MK_COMB (@lem3284920) (@lem3284919 A x s t x')). Qed.
Lemma lem3284923 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3284924 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3284923 A x). Qed.
Lemma lem3284925 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem3284924 A x'). Qed.
Lemma lem3284926 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term26 A x' x s t) = (@IN A x' (@EMPTY A))) = ((term34 A x s t x') = False).
Proof. exact (MK_COMB (@lem3284921 A x s t x') (@lem3284925 A x')). Qed.
Lemma lem3284928 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3284929 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term34 A x s t x') = False) = (term37 A x s t x').
Proof. exact (@lem3284928 (term34 A x s t x')). Qed.
Lemma lem3284936 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term26 A x' x s t) = (@IN A x' (@EMPTY A))) = (term37 A x s t x').
Proof. exact (TRANS (@lem3284926 A x s t x') (@lem3284929 A x s t x')). Qed.
Lemma lem3284937 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term38 A x s t) = (term39 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3284936 A x s t x')). Qed.
Lemma lem3284938 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3284939 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term3 A x s t) = (term40 A x s t).
Proof. exact (MK_COMB (@lem3284938 A) (@lem3284937 A x s t)). Qed.
Lemma lem3284944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3284945 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term5 A x s t) = (term41 A x s t).
Proof. exact (MK_COMB (@lem3284944) (@lem3284939 A x s t)). Qed.
Lemma lem3284955 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term24 A x s t) = (term25 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3284956 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term24 A x s t) = (term25 A s x t).
Proof. exact (@lem3284955 A s x t). Qed.
Lemma lem3284960 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3284961 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3284960 A P x). Qed.
Lemma lem3284962 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3284961 A s x). Qed.
Lemma lem3284963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3284964 {A : Type'} (s : A -> Prop) (x : A) : (term42 A x s) = (term43 A s x).
Proof. exact (MK_COMB (@lem3284963) (@lem3284962 A s x)). Qed.
Lemma lem3284966 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3284967 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3284966 A P x). Qed.
Lemma lem3284968 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3284967 A t x). Qed.
Lemma lem3284969 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term25 A s x t) = (term44 A s t x).
Proof. exact (MK_COMB (@lem3284964 A s x) (@lem3284968 A t x)). Qed.
Lemma lem3284972 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term24 A x s t) = (term44 A s t x).
Proof. exact (TRANS (@lem3284956 A s x t) (@lem3284969 A s t x)). Qed.
Lemma lem3284973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3284974 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term45 A x s t) = (term46 A s t x).
Proof. exact (MK_COMB (@lem3284973) (@lem3284972 A s t x)). Qed.
Lemma lem3284976 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3284977 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3284976 A x). Qed.
Lemma lem3284978 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term24 A x s t) = (@IN A x (@EMPTY A))) = ((term44 A s t x) = False).
Proof. exact (MK_COMB (@lem3284974 A s t x) (@lem3284977 A x)). Qed.
Lemma lem3284980 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3284981 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term44 A s t x) = False) = (term47 A s t x).
Proof. exact (@lem3284980 (term44 A s t x)). Qed.
Lemma lem3284984 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term24 A x s t) = (@IN A x (@EMPTY A))) = (term47 A s t x).
Proof. exact (TRANS (@lem3284978 A s t x) (@lem3284981 A s t x)). Qed.
Lemma lem3284985 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term48 A s t) = (term49 A s t).
Proof. exact (fun_ext (fun x : A => @lem3284984 A s t x)). Qed.
Lemma lem3284986 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3284987 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term6 A s t) = (term50 A s t).
Proof. exact (MK_COMB (@lem3284986 A) (@lem3284985 A s t)). Qed.
Lemma lem3284992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3284993 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term8 A s t) = (term51 A s t).
Proof. exact (MK_COMB (@lem3284992) (@lem3284987 A s t)). Qed.
Lemma lem3284995 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3284996 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3284995 A P x). Qed.
Lemma lem3284997 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3284996 A t x). Qed.
Lemma lem3284998 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3284999 {A : Type'} (t : A -> Prop) (x : A) : (term9 A x t) = (term52 A t x).
Proof. exact (MK_COMB (@lem3284998) (@lem3284997 A t x)). Qed.
Lemma lem3285000 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term11 A s x t) = (term53 A s t x).
Proof. exact (MK_COMB (@lem3284993 A s t) (@lem3284999 A t x)). Qed.
Lemma lem3285003 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term3 A x s t) = (term11 A s x t)) = ((term40 A x s t) = (term53 A s t x)).
Proof. exact (MK_COMB (@lem3284945 A x s t) (@lem3285000 A s t x)). Qed.
Lemma lem3285006 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = (term54 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3285003 A s t x)). Qed.
Lemma lem3285007 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3285008 {A : Type'} (s : A -> Prop) (x : A) : (term15 A s x) = (term55 A s x).
Proof. exact (MK_COMB (@lem3285007 A) (@lem3285006 A s x)). Qed.
Lemma lem3285013 {A : Type'} (x : A) : (term17 A x) = (term56 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3285008 A s x)). Qed.
Lemma lem3285014 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3285015 {A : Type'} (x : A) : (term19 A x) = (term57 A x).
Proof. exact (MK_COMB (@lem3285014 A) (@lem3285013 A x)). Qed.
Lemma lem3285020 {A : Type'} : (term21 A) = (term58 A).
Proof. exact (fun_ext (fun x : A => @lem3285015 A x)). Qed.
Lemma lem3285021 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3285022 {A : Type'} : (term23 A) = (term59 A).
Proof. exact (MK_COMB (@lem3285021 A) (@lem3285020 A)). Qed.
Lemma lem3285027 {A : Type'} : (term59 A) = (term23 A).
Proof. exact (SYM (@lem3285022 A)). Qed.
Lemma lem3285029 (p : Prop) : p = (term60 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3285030 {A : Type'} : (term59 A) = (term61 A).
Proof. exact (@lem3285029 (term59 A)). Qed.
Lemma lem3285031 {A : Type'} : (term61 A) = (term59 A).
Proof. exact (SYM (@lem3285030 A)). Qed.
Lemma lem3285032 {A : Type'} (h1 : term62 A) : term62 A.
Proof. exact (h1). Qed.
Lemma lem3285035 {A : Type'} (h1 : term61 A) : term61 A.
Proof. exact (h1). Qed.
Lemma lem3285036 {A : Type'} : term63 A.
Proof. exact (fun h0 : term61 A => @lem3285035 A h0). Qed.
Lemma lem3285037 {A : Type'} (h1 : term63 A) : term63 A.
Proof. exact (h1). Qed.
Lemma lem3285038 {A : Type'} (h1 : term61 A) : term61 A.
Proof. exact (h1). Qed.
Lemma lem3285039 {A : Type'} (h1 : term61 A) (h2 : term63 A) : term61 A.
Proof. exact (@lem3285037 A h2 (@lem3285038 A h1)). Qed.
Lemma lem3285040 {A : Type'} (h1 : term61 A) : term64 A.
Proof. exact (fun h0 : term63 A => @lem3285039 A h1 h0). Qed.
Lemma lem3285041 {A : Type'} (h1 : term63 A) : term63 A.
Proof. exact (h1). Qed.
Lemma lem3285042 {A : Type'} (h1 : term61 A) (h2 : term63 A) : term61 A.
Proof. exact (@lem3285040 A h1 (@lem3285041 A h2)). Qed.
Lemma lem3285043 {A : Type'} (h1 : term63 A) : term63 A.
Proof. exact (fun h0 : term61 A => @lem3285042 A h0 h1). Qed.
Lemma lem3285044 {A : Type'} : term65 A.
Proof. exact (fun h0 : term63 A => @lem3285043 A h0). Qed.
Lemma lem3285047 {A : Type'} : term63 A.
Proof. exact (@lem3285044 A (@lem3285036 A)). Qed.
Lemma lem3285048 {A : Type'} : term63 A.
Proof. exact (@lem3285047 A). Qed.
Lemma lem3285050 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3285051 {A : Type'} : (term61 A) = (term66 A).
Proof. exact (@lem3285050 (term62 A)). Qed.
Lemma lem3285053 (t : Prop) : (term67 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3285054 {A : Type'} : (term66 A) = (term59 A).
Proof. exact (@lem3285053 (term59 A)). Qed.
Lemma lem3285087 {A : Type'} : (term61 A) = (term59 A).
Proof. exact (TRANS (@lem3285051 A) (@lem3285054 A)). Qed.
Lemma lem3285090 {A : Type'} (t : A -> Prop) (x : A) : (term52 A t x) = (term52 A t x).
Proof. exact (eq_refl (term52 A t x)). Qed.
Lemma lem3285097 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term47 A s t x) = (term47 A s t x).
Proof. exact (eq_refl (term47 A s t x)). Qed.
Lemma lem3285098 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term49 A s t) = (term49 A s t).
Proof. exact (fun_ext (fun x : A => @lem3285097 A s t x)). Qed.
Lemma lem3285099 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3285100 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term50 A s t).
Proof. exact (MK_COMB (@lem3285099 A) (@lem3285098 A s t)). Qed.
Lemma lem3285101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3285102 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term51 A s t) = (term51 A s t).
Proof. exact (MK_COMB (@lem3285101) (@lem3285100 A s t)). Qed.
Lemma lem3285103 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term53 A s t x) = (term53 A s t x).
Proof. exact (MK_COMB (@lem3285102 A s t) (@lem3285090 A t x)). Qed.
Lemma lem3285114 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term37 A x s t x') = (term37 A x s t x').
Proof. exact (eq_refl (term37 A x s t x')). Qed.
Lemma lem3285115 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term39 A x s t) = (term39 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3285114 A x s t x')). Qed.
Lemma lem3285116 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3285117 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term40 A x s t) = (term40 A x s t).
Proof. exact (MK_COMB (@lem3285116 A) (@lem3285115 A x s t)). Qed.
Lemma lem3285118 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3285119 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term41 A x s t) = (term41 A x s t).
Proof. exact (MK_COMB (@lem3285118) (@lem3285117 A x s t)). Qed.
Lemma lem3285120 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term40 A x s t) = (term53 A s t x)) = ((term40 A x s t) = (term53 A s t x)).
Proof. exact (MK_COMB (@lem3285119 A x s t) (@lem3285103 A s t x)). Qed.
Lemma lem3285121 {A : Type'} (s : A -> Prop) (x : A) : (term54 A s x) = (term54 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3285120 A s t x)). Qed.
Lemma lem3285122 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3285123 {A : Type'} (s : A -> Prop) (x : A) : (term55 A s x) = (term55 A s x).
Proof. exact (MK_COMB (@lem3285122 A) (@lem3285121 A s x)). Qed.
Lemma lem3285124 {A : Type'} (x : A) : (term56 A x) = (term56 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3285123 A s x)). Qed.
Lemma lem3285125 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3285126 {A : Type'} (x : A) : (term57 A x) = (term57 A x).
Proof. exact (MK_COMB (@lem3285125 A) (@lem3285124 A x)). Qed.
Lemma lem3285127 {A : Type'} : (term58 A) = (term58 A).
Proof. exact (fun_ext (fun x : A => @lem3285126 A x)). Qed.
Lemma lem3285128 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3285129 {A : Type'} : (term59 A) = (term59 A).
Proof. exact (MK_COMB (@lem3285128 A) (@lem3285127 A)). Qed.
Lemma lem3285170 {A : Type'} : (term61 A) = (term59 A).
Proof. exact (TRANS (@lem3285087 A) (@lem3285129 A)). Qed.
Lemma lem3285171 {A : Type'} : (term59 A) = (term61 A).
Proof. exact (SYM (@lem3285170 A)). Qed.
Lemma lem3285173 (p : Prop) : p = (term60 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3285174 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term40 A x s t) = (term53 A s t x)) = (term68 A s t x).
Proof. exact (@lem3285173 ((term40 A x s t) = (term53 A s t x))). Qed.
Lemma lem3285175 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term68 A s t x) = ((term40 A x s t) = (term53 A s t x)).
Proof. exact (SYM (@lem3285174 A s t x)). Qed.
Lemma lem3285176 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term69 A s t x) : term69 A s t x.
Proof. exact (h1). Qed.
Lemma lem3285185 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term70 A x s x') = (term71 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3285189 {A : Type'} (t : A -> Prop) (x' : A) : (term52 A t x') = (term52 A t x').
Proof. exact (eq_refl (term52 A t x')). Qed.
Lemma lem3285191 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3285192 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term72 A x s x') = (term73 A x s x').
Proof. exact (MK_COMB (@lem3285191) (@lem3285185 A x s x')). Qed.
Lemma lem3285193 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term74 A x s t x') = (term75 A x s t x').
Proof. exact (MK_COMB (@lem3285192 A x s x') (@lem3285189 A t x')). Qed.
Lemma lem3285194 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term37 A x s t x') = (term74 A x s t x').
Proof. exact (@lem17045 (term31 A x s x') (t x')). Qed.
Lemma lem3285195 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term37 A x s t x') = (term75 A x s t x').
Proof. exact (TRANS (@lem3285194 A x s t x') (@lem3285193 A x s t x')). Qed.
Lemma lem3285200 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term76 A x s t x') = (term34 A x s t x').
Proof. exact (@lem16933 (term34 A x s t x')). Qed.
Lemma lem3285201 {A : Type'} (P : A -> Prop) : (term77 A P) = (term78 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3285202 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term79 A x s t) = (term80 A x s t).
Proof. exact (@lem3285201 A (term39 A x s t)). Qed.
Lemma lem3285203 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term81 A x s t x') = (term37 A x s t x').
Proof. exact (eq_refl (term81 A x s t x')). Qed.
Lemma lem3285204 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3285205 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term82 A x s t x') = (term76 A x s t x').
Proof. exact (MK_COMB (@lem3285204) (@lem3285203 A x s t x')). Qed.
Lemma lem3285206 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term82 A x s t x') = (term34 A x s t x').
Proof. exact (TRANS (@lem3285205 A x s t x') (@lem3285200 A x s t x')). Qed.
Lemma lem3285207 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term83 A x s t) = (term84 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3285206 A x s t x')). Qed.
Lemma lem3285208 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3285209 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term80 A x s t) = (term85 A x s t).
Proof. exact (MK_COMB (@lem3285208 A) (@lem3285207 A x s t)). Qed.
Lemma lem3285210 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term79 A x s t) = (term85 A x s t).
Proof. exact (TRANS (@lem3285202 A x s t) (@lem3285209 A x s t)). Qed.
Lemma lem3285211 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term39 A x s t) = (term86 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3285195 A x s t x')). Qed.
Lemma lem3285212 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3285213 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term40 A x s t) = (term87 A x s t).
Proof. exact (MK_COMB (@lem3285212 A) (@lem3285211 A x s t)). Qed.
Lemma lem3285222 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term47 A s t x) = (term88 A s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem3285227 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term89 A s t x) = (term44 A s t x).
Proof. exact (@lem16933 (term44 A s t x)). Qed.
Lemma lem3285228 {A : Type'} (P : A -> Prop) : (term77 A P) = (term78 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3285229 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term90 A s t) = (term91 A s t).
Proof. exact (@lem3285228 A (term49 A s t)). Qed.
Lemma lem3285230 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term92 A s t x) = (term47 A s t x).
Proof. exact (eq_refl (term92 A s t x)). Qed.
Lemma lem3285231 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3285232 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term93 A s t x) = (term89 A s t x).
Proof. exact (MK_COMB (@lem3285231) (@lem3285230 A s t x)). Qed.
Lemma lem3285233 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term93 A s t x) = (term44 A s t x).
Proof. exact (TRANS (@lem3285232 A s t x) (@lem3285227 A s t x)). Qed.
Lemma lem3285234 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term94 A s t) = (term95 A s t).
Proof. exact (fun_ext (fun x : A => @lem3285233 A s t x)). Qed.
Lemma lem3285235 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3285236 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term91 A s t) = (term96 A s t).
Proof. exact (MK_COMB (@lem3285235 A) (@lem3285234 A s t)). Qed.
Lemma lem3285237 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term90 A s t) = (term96 A s t).
Proof. exact (TRANS (@lem3285229 A s t) (@lem3285236 A s t)). Qed.
Lemma lem3285238 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term49 A s t) = (term97 A s t).
Proof. exact (fun_ext (fun x : A => @lem3285222 A s t x)). Qed.
Lemma lem3285239 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3285240 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term98 A s t).
Proof. exact (MK_COMB (@lem3285239 A) (@lem3285238 A s t)). Qed.
Lemma lem3285241 {A : Type'} (t : A -> Prop) (x : A) : (term52 A t x) = (term52 A t x).
Proof. exact (eq_refl (term52 A t x)). Qed.
Lemma lem3285244 {A : Type'} (t : A -> Prop) (x : A) : (term99 A t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3285245 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3285246 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term100 A s t) = (term101 A s t).
Proof. exact (MK_COMB (@lem3285245) (@lem3285237 A s t)). Qed.
Lemma lem3285247 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term102 A s t x) = (term103 A s t x).
Proof. exact (MK_COMB (@lem3285246 A s t) (@lem3285244 A t x)). Qed.
Lemma lem3285248 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term104 A s t x) = (term102 A s t x).
Proof. exact (@lem17045 (term50 A s t) (term52 A t x)). Qed.
Lemma lem3285249 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term104 A s t x) = (term103 A s t x).
Proof. exact (TRANS (@lem3285248 A s t x) (@lem3285247 A s t x)). Qed.
Lemma lem3285250 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3285251 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term51 A s t) = (term105 A s t).
Proof. exact (MK_COMB (@lem3285250) (@lem3285240 A s t)). Qed.
Lemma lem3285252 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term53 A s t x) = (term106 A s t x).
Proof. exact (MK_COMB (@lem3285251 A s t) (@lem3285241 A t x)). Qed.
Lemma lem3285253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3285254 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term107 A x s t) = (term108 A x s t).
Proof. exact (MK_COMB (@lem3285253) (@lem3285210 A x s t)). Qed.
Lemma lem3285255 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term109 A s t x) = (term110 A s t x).
Proof. exact (MK_COMB (@lem3285254 A x s t) (@lem3285252 A s t x)). Qed.
Lemma lem3285256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3285257 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term111 A x s t) = (term112 A x s t).
Proof. exact (MK_COMB (@lem3285256) (@lem3285213 A x s t)). Qed.
Lemma lem3285258 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term113 A s t x) = (term114 A s t x).
Proof. exact (MK_COMB (@lem3285257 A x s t) (@lem3285249 A s t x)). Qed.
Lemma lem3285259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3285260 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term115 A s t x) = (term116 A s t x).
Proof. exact (MK_COMB (@lem3285259) (@lem3285258 A s t x)). Qed.
Lemma lem3285261 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term117 A s t x) = (term118 A s t x).
Proof. exact (MK_COMB (@lem3285260 A s t x) (@lem3285255 A s t x)). Qed.
Lemma lem3285262 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term69 A s t x) = (term117 A s t x).
Proof. exact (@lem17646 (term40 A x s t) (term53 A s t x)). Qed.
Lemma lem3285263 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term69 A s t x) = (term118 A s t x).
Proof. exact (TRANS (@lem3285262 A s t x) (@lem3285261 A s t x)). Qed.
Lemma lem3285406 {A : Type'} (P : A -> Prop) (Q : Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3285407 {A : Type'} (P : A -> Prop) (Q : Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (@lem3285406 A P Q). Qed.
Lemma lem3285408 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term121 A s t x) = (term122 A s t x).
Proof. exact (@lem3285407 A (term95 A s t) (t x)). Qed.
Lemma lem3285409 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term123 A s t x) = (term44 A s t x).
Proof. exact (eq_refl (term123 A s t x)). Qed.
Lemma lem3285410 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term124 A s t) = (term95 A s t).
Proof. exact (fun_ext (fun x : A => @lem3285409 A s t x)). Qed.
Lemma lem3285411 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3285412 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term125 A s t) = (term96 A s t).
Proof. exact (MK_COMB (@lem3285411 A) (@lem3285410 A s t)). Qed.
Lemma lem3285413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3285414 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term126 A s t) = (term101 A s t).
Proof. exact (MK_COMB (@lem3285413) (@lem3285412 A s t)). Qed.
Lemma lem3285415 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3285416 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term121 A s t x) = (term103 A s t x).
Proof. exact (MK_COMB (@lem3285414 A s t) (@lem3285415 A t x)). Qed.
Lemma lem3285417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3285418 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term127 A s t x) = (term128 A s t x).
Proof. exact (MK_COMB (@lem3285417) (@lem3285416 A s t x)). Qed.
Lemma lem3285419 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term123 A s t x') = (term44 A s t x').
Proof. exact (eq_refl (term123 A s t x')). Qed.
Lemma lem3285420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3285421 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term129 A s t x') = (term130 A s t x').
Proof. exact (MK_COMB (@lem3285420) (@lem3285419 A s t x')). Qed.
Lemma lem3285422 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3285423 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) : (term131 A s x' t x) = (term132 A s x' t x).
Proof. exact (MK_COMB (@lem3285421 A s t x') (@lem3285422 A t x)). Qed.
Lemma lem3285424 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term133 A s t x) = (term134 A s t x).
Proof. exact (fun_ext (fun x' : A => @lem3285423 A s x' t x)). Qed.
Lemma lem3285425 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3285426 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term122 A s t x) = (term135 A s t x).
Proof. exact (MK_COMB (@lem3285425 A) (@lem3285424 A s t x)). Qed.
Lemma lem3285427 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term121 A s t x) = (term122 A s t x)) = ((term103 A s t x) = (term135 A s t x)).
Proof. exact (MK_COMB (@lem3285418 A s t x) (@lem3285426 A s t x)). Qed.
Lemma lem3285428 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term103 A s t x) = (term135 A s t x).
Proof. exact (EQ_MP (@lem3285427 A s t x) (@lem3285408 A s t x)). Qed.
Lemma lem3285429 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term112 A x s t) = (term112 A x s t).
Proof. exact (eq_refl (term112 A x s t)). Qed.
Lemma lem3285430 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term114 A s t x) = (term136 A s t x).
Proof. exact (MK_COMB (@lem3285429 A x s t) (@lem3285428 A s t x)). Qed.
Lemma lem3285432 {A : Type'} (P : Prop) (Q : A -> Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3285433 {A : Type'} (P : Prop) (Q : A -> Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (@lem3285432 A P Q). Qed.
Lemma lem3285434 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term139 A s t x) = (term140 A s t x).
Proof. exact (@lem3285433 A (term87 A x s t) (term134 A s t x)). Qed.
Lemma lem3285435 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) : (term141 A s t x x') = (term132 A s x' t x).
Proof. exact (eq_refl (term141 A s t x x')). Qed.
Lemma lem3285436 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term142 A s t x) = (term134 A s t x).
Proof. exact (fun_ext (fun x' : A => @lem3285435 A s x' t x)). Qed.
Lemma lem3285437 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3285438 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term143 A s t x) = (term135 A s t x).
Proof. exact (MK_COMB (@lem3285437 A) (@lem3285436 A s t x)). Qed.
Lemma lem3285439 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term112 A x s t) = (term112 A x s t).
Proof. exact (eq_refl (term112 A x s t)). Qed.
Lemma lem3285440 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term139 A s t x) = (term136 A s t x).
Proof. exact (MK_COMB (@lem3285439 A x s t) (@lem3285438 A s t x)). Qed.
Lemma lem3285441 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3285442 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term144 A s t x) = (term145 A s t x).
Proof. exact (MK_COMB (@lem3285441) (@lem3285440 A s t x)). Qed.
Lemma lem3285443 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) : (term141 A s t x x') = (term132 A s x' t x).
Proof. exact (eq_refl (term141 A s t x x')). Qed.
Lemma lem3285444 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term112 A x s t) = (term112 A x s t).
Proof. exact (eq_refl (term112 A x s t)). Qed.
Lemma lem3285445 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) : (term146 A s t x x') = (term147 A s x' t x).
Proof. exact (MK_COMB (@lem3285444 A x s t) (@lem3285443 A s x' t x)). Qed.
Lemma lem3285446 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term148 A s t x) = (term149 A s t x).
Proof. exact (fun_ext (fun x' : A => @lem3285445 A s x' t x)). Qed.
Lemma lem3285447 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3285448 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term140 A s t x) = (term150 A s t x).
Proof. exact (MK_COMB (@lem3285447 A) (@lem3285446 A s t x)). Qed.
Lemma lem3285449 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term139 A s t x) = (term140 A s t x)) = ((term136 A s t x) = (term150 A s t x)).
Proof. exact (MK_COMB (@lem3285442 A s t x) (@lem3285448 A s t x)). Qed.
Lemma lem3285450 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term136 A s t x) = (term150 A s t x).
Proof. exact (EQ_MP (@lem3285449 A s t x) (@lem3285434 A s t x)). Qed.
Lemma lem3285451 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term114 A s t x) = (term150 A s t x).
Proof. exact (TRANS (@lem3285430 A s t x) (@lem3285450 A s t x)). Qed.
Lemma lem3285452 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3285453 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term116 A s t x) = (term151 A s t x).
Proof. exact (MK_COMB (@lem3285452) (@lem3285451 A s t x)). Qed.
Lemma lem3285455 {A : Type'} (P : A -> Prop) (Q : Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3285456 {A : Type'} (P : A -> Prop) (Q : Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (@lem3285455 A P Q). Qed.
Lemma lem3285457 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term154 A s t x) = (term155 A s t x).
Proof. exact (@lem3285456 A (term84 A x s t) (term106 A s t x)). Qed.
Lemma lem3285458 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term156 A x s t x') = (term34 A x s t x').
Proof. exact (eq_refl (term156 A x s t x')). Qed.
Lemma lem3285459 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term157 A x s t) = (term84 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3285458 A x s t x')). Qed.
Lemma lem3285460 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3285461 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term158 A x s t) = (term85 A x s t).
Proof. exact (MK_COMB (@lem3285460 A) (@lem3285459 A x s t)). Qed.
Lemma lem3285462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3285463 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term159 A x s t) = (term108 A x s t).
Proof. exact (MK_COMB (@lem3285462) (@lem3285461 A x s t)). Qed.
Lemma lem3285464 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term106 A s t x) = (term106 A s t x).
Proof. exact (eq_refl (term106 A s t x)). Qed.
Lemma lem3285465 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term154 A s t x) = (term110 A s t x).
Proof. exact (MK_COMB (@lem3285463 A x s t) (@lem3285464 A s t x)). Qed.
Lemma lem3285466 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3285467 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term160 A s t x) = (term161 A s t x).
Proof. exact (MK_COMB (@lem3285466) (@lem3285465 A s t x)). Qed.
Lemma lem3285468 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term156 A x s t x') = (term34 A x s t x').
Proof. exact (eq_refl (term156 A x s t x')). Qed.
Lemma lem3285469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3285470 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term162 A x s t x') = (term163 A x s t x').
Proof. exact (MK_COMB (@lem3285469) (@lem3285468 A x s t x')). Qed.
Lemma lem3285471 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term106 A s t x) = (term106 A s t x).
Proof. exact (eq_refl (term106 A s t x)). Qed.
Lemma lem3285472 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term164 A x' s t x) = (term165 A x' s t x).
Proof. exact (MK_COMB (@lem3285470 A x s t x') (@lem3285471 A s t x)). Qed.
Lemma lem3285473 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term166 A s t x) = (term167 A s t x).
Proof. exact (fun_ext (fun x' : A => @lem3285472 A x' s t x)). Qed.
Lemma lem3285474 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3285475 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term155 A s t x) = (term168 A s t x).
Proof. exact (MK_COMB (@lem3285474 A) (@lem3285473 A s t x)). Qed.
Lemma lem3285476 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term154 A s t x) = (term155 A s t x)) = ((term110 A s t x) = (term168 A s t x)).
Proof. exact (MK_COMB (@lem3285467 A s t x) (@lem3285475 A s t x)). Qed.
Lemma lem3285477 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term110 A s t x) = (term168 A s t x).
Proof. exact (EQ_MP (@lem3285476 A s t x) (@lem3285457 A s t x)). Qed.
Lemma lem3285478 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term118 A s t x) = (term169 A s t x).
Proof. exact (MK_COMB (@lem3285453 A s t x) (@lem3285477 A s t x)). Qed.
Lemma lem3285480 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term170 A P Q) = (term171 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3285481 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term170 A P Q) = (term171 A P Q).
Proof. exact (@lem3285480 A P Q). Qed.
Lemma lem3285482 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term172 A s t x) = (term173 A s t x).
Proof. exact (@lem3285481 A (term149 A s t x) (term167 A s t x)). Qed.
Lemma lem3285483 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) : (term174 A s t x x') = (term147 A s x' t x).
Proof. exact (eq_refl (term174 A s t x x')). Qed.
Lemma lem3285484 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term175 A s t x) = (term149 A s t x).
Proof. exact (fun_ext (fun x' : A => @lem3285483 A s x' t x)). Qed.
Lemma lem3285485 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3285486 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term176 A s t x) = (term150 A s t x).
Proof. exact (MK_COMB (@lem3285485 A) (@lem3285484 A s t x)). Qed.
Lemma lem3285487 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3285488 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term177 A s t x) = (term151 A s t x).
Proof. exact (MK_COMB (@lem3285487) (@lem3285486 A s t x)). Qed.
Lemma lem3285489 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term178 A s t x x') = (term165 A x' s t x).
Proof. exact (eq_refl (term178 A s t x x')). Qed.
Lemma lem3285490 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term179 A s t x) = (term167 A s t x).
Proof. exact (fun_ext (fun x' : A => @lem3285489 A x' s t x)). Qed.
Lemma lem3285491 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3285492 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term180 A s t x) = (term168 A s t x).
Proof. exact (MK_COMB (@lem3285491 A) (@lem3285490 A s t x)). Qed.
Lemma lem3285493 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term172 A s t x) = (term169 A s t x).
Proof. exact (MK_COMB (@lem3285488 A s t x) (@lem3285492 A s t x)). Qed.
Lemma lem3285494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3285495 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term181 A s t x) = (term182 A s t x).
Proof. exact (MK_COMB (@lem3285494) (@lem3285493 A s t x)). Qed.
Lemma lem3285496 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) : (term174 A s t x x') = (term147 A s x' t x).
Proof. exact (eq_refl (term174 A s t x x')). Qed.
Lemma lem3285497 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3285498 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) : (term183 A s t x x') = (term184 A s x' t x).
Proof. exact (MK_COMB (@lem3285497) (@lem3285496 A s x' t x)). Qed.
Lemma lem3285499 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term178 A s t x x') = (term165 A x' s t x).
Proof. exact (eq_refl (term178 A s t x x')). Qed.
Lemma lem3285500 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term185 A s t x x') = (term186 A x' s t x).
Proof. exact (MK_COMB (@lem3285498 A s x' t x) (@lem3285499 A x' s t x)). Qed.
Lemma lem3285501 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term187 A s t x) = (term188 A s t x).
Proof. exact (fun_ext (fun x' : A => @lem3285500 A x' s t x)). Qed.
Lemma lem3285502 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3285503 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term173 A s t x) = (term189 A s t x).
Proof. exact (MK_COMB (@lem3285502 A) (@lem3285501 A s t x)). Qed.
Lemma lem3285504 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term172 A s t x) = (term173 A s t x)) = ((term169 A s t x) = (term189 A s t x)).
Proof. exact (MK_COMB (@lem3285495 A s t x) (@lem3285503 A s t x)). Qed.
Lemma lem3285505 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term169 A s t x) = (term189 A s t x).
Proof. exact (EQ_MP (@lem3285504 A s t x) (@lem3285482 A s t x)). Qed.
Lemma lem3285507 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term118 A s t x) = (term189 A s t x).
Proof. exact (TRANS (@lem3285478 A s t x) (@lem3285505 A s t x)). Qed.
Lemma lem3285508 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term69 A s t x) = (term189 A s t x).
Proof. exact (TRANS (@lem3285263 A s t x) (@lem3285507 A s t x)). Qed.
Lemma lem3285509 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term69 A s t x) : term189 A s t x.
Proof. exact (EQ_MP (@lem3285508 A s t x) (@lem3285176 A s t x h1)). Qed.
Lemma lem3285510 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A x' s t x) : term186 A x' s t x.
Proof. exact (h1). Qed.
Lemma lem3285515 {A : Type'} (t : A -> Prop) (x : A) : (term52 A t x) = (term52 A t x).
Proof. exact (eq_refl (term52 A t x)). Qed.
Lemma lem3285528 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term88 A s t x) = (term88 A s t x).
Proof. exact (eq_refl (term88 A s t x)). Qed.
Lemma lem3285529 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term97 A s t) = (term97 A s t).
Proof. exact (fun_ext (fun x : A => @lem3285528 A s t x)). Qed.
Lemma lem3285530 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3285531 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term98 A s t) = (term98 A s t).
Proof. exact (MK_COMB (@lem3285530 A) (@lem3285529 A s t)). Qed.
Lemma lem3285532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3285533 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term105 A s t) = (term105 A s t).
Proof. exact (MK_COMB (@lem3285532) (@lem3285531 A s t)). Qed.
Lemma lem3285534 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term106 A s t x) = (term106 A s t x).
Proof. exact (MK_COMB (@lem3285533 A s t) (@lem3285515 A t x)). Qed.
Lemma lem3285553 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term163 A x s t x') = (term163 A x s t x').
Proof. exact (eq_refl (term163 A x s t x')). Qed.
Lemma lem3285554 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term165 A x' s t x) = (term165 A x' s t x).
Proof. exact (MK_COMB (@lem3285553 A x s t x') (@lem3285534 A s t x)). Qed.
Lemma lem3285569 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) : (term132 A s x' t x) = (term132 A s x' t x).
Proof. exact (eq_refl (term132 A s x' t x)). Qed.
Lemma lem3285592 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term75 A x s t x') = (term75 A x s t x').
Proof. exact (eq_refl (term75 A x s t x')). Qed.
Lemma lem3285593 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term86 A x s t) = (term86 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3285592 A x s t x')). Qed.
Lemma lem3285594 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3285595 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term87 A x s t) = (term87 A x s t).
Proof. exact (MK_COMB (@lem3285594 A) (@lem3285593 A x s t)). Qed.
Lemma lem3285596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3285597 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term112 A x s t) = (term112 A x s t).
Proof. exact (MK_COMB (@lem3285596) (@lem3285595 A x s t)). Qed.
Lemma lem3285598 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) : (term147 A s x' t x) = (term147 A s x' t x).
Proof. exact (MK_COMB (@lem3285597 A x s t) (@lem3285569 A s x' t x)). Qed.
Lemma lem3285599 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3285600 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) : (term184 A s x' t x) = (term184 A s x' t x).
Proof. exact (MK_COMB (@lem3285599) (@lem3285598 A s x' t x)). Qed.
Lemma lem3285601 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term186 A x' s t x) = (term186 A x' s t x).
Proof. exact (MK_COMB (@lem3285600 A s x' t x) (@lem3285554 A x' s t x)). Qed.
Lemma lem3285602 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A x' s t x) : term186 A x' s t x.
Proof. exact (EQ_MP (@lem3285601 A x' s t x) (@lem3285510 A x' s t x h1)). Qed.
Lemma lem3285603 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term147 A s x' t x.
Proof. exact (h1). Qed.
Lemma lem3285604 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : term165 A x' s t x.
Proof. exact (h1). Qed.
Lemma lem3285605 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term132 A s x' t x.
Proof. exact (proj2 (@lem3285603 A s x' t x h1)). Qed.
Lemma lem3285606 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term87 A x s t.
Proof. exact (proj1 (@lem3285603 A s x' t x h1)). Qed.
Lemma lem3285607 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term44 A s t x') : term44 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3285611 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : term106 A s t x.
Proof. exact (proj2 (@lem3285604 A x' s t x h1)). Qed.
Lemma lem3285612 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : term34 A x s t x'.
Proof. exact (proj1 (@lem3285604 A x' s t x h1)). Qed.
Lemma lem3285614 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : term98 A s t.
Proof. exact (proj1 (@lem3285611 A x' s t x h1)). Qed.
Lemma lem3285616 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : term31 A x s x'.
Proof. exact (proj1 (@lem3285612 A x' s t x h1)). Qed.
Lemma lem3285636 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term75 A x s t x') = (term190 A x s t x').
Proof. exact (@lem19699 (term191 A x' x) (term52 A s x') (term52 A t x')). Qed.
Lemma lem3285637 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term86 A x s t) = (term192 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3285636 A x s t x')). Qed.
Lemma lem3285638 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3285640 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term87 A x s t) = (term193 A x s t).
Proof. exact (MK_COMB (@lem3285638 A) (@lem3285637 A x s t)). Qed.
Lemma lem3285641 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term193 A x s t.
Proof. exact (EQ_MP (@lem3285640 A x s t) (@lem3285606 A s x' t x h1)). Qed.
Lemma lem3285667 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term75 A x s t x') = (term190 A x s t x').
Proof. exact (@lem19699 (term191 A x' x) (term52 A s x') (term52 A t x')). Qed.
Lemma lem3285668 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term86 A x s t) = (term192 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3285667 A x s t x')). Qed.
Lemma lem3285669 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3285671 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term87 A x s t) = (term193 A x s t).
Proof. exact (MK_COMB (@lem3285669 A) (@lem3285668 A x s t)). Qed.
Lemma lem3285672 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term193 A x s t.
Proof. exact (EQ_MP (@lem3285671 A x s t) (@lem3285606 A s x' t x h1)). Qed.
Lemma lem3285676 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3285701 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3285709 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term88 A s t x) = (term88 A s t x).
Proof. exact (eq_refl (term88 A s t x)). Qed.
Lemma lem3285710 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term97 A s t) = (term97 A s t).
Proof. exact (fun_ext (fun x : A => @lem3285709 A s t x)). Qed.
Lemma lem3285711 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3285713 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term98 A s t) = (term98 A s t).
Proof. exact (MK_COMB (@lem3285711 A) (@lem3285710 A s t)). Qed.
Lemma lem3285714 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : term98 A s t.
Proof. exact (EQ_MP (@lem3285713 A s t) (@lem3285614 A x' s t x h1)). Qed.
Lemma lem3285726 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3285727 {A : Type'} (_33774 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term194 A x s t _33774.
Proof. exact (@lem3285641 A s x' t x h1 _33774). Qed.
Lemma lem3285728 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_33774 : A) : (term194 A x s t _33774) = (term190 A x s t _33774).
Proof. exact (eq_refl (term194 A x s t _33774)). Qed.
Lemma lem3285729 {A : Type'} (_33774 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term190 A x s t _33774.
Proof. exact (EQ_MP (@lem3285728 A x s t _33774) (@lem3285727 A _33774 s x' t x h1)). Qed.
Lemma lem3285730 {A : Type'} (_33775 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term194 A x s t _33775.
Proof. exact (@lem3285672 A s x' t x h1 _33775). Qed.
Lemma lem3285731 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_33775 : A) : (term194 A x s t _33775) = (term190 A x s t _33775).
Proof. exact (eq_refl (term194 A x s t _33775)). Qed.
Lemma lem3285732 {A : Type'} (_33775 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term190 A x s t _33775.
Proof. exact (EQ_MP (@lem3285731 A x s t _33775) (@lem3285730 A _33775 s x' t x h1)). Qed.
Lemma lem3285736 {A : Type'} (_33777 : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : term195 A s t _33777.
Proof. exact (@lem3285714 A x' s t x h1 _33777). Qed.
Lemma lem3285737 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33777 : A) : (term195 A s t _33777) = (term88 A s t _33777).
Proof. exact (eq_refl (term195 A s t _33777)). Qed.
Lemma lem3285758 {A : Type'} (_33774 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term88 A s t _33774.
Proof. exact (proj2 (@lem3285729 A _33774 s x' t x h1)). Qed.
Lemma lem3285760 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3285766 {A : Type'} (_33775 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term196 A x t _33775.
Proof. exact (proj1 (@lem3285732 A _33775 s x' t x h1)). Qed.
Lemma lem3285782 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : t x'.
Proof. exact (proj2 (@lem3285612 A x' s t x h1)). Qed.
Lemma lem3285784 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3285790 {A : Type'} (_33777 : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : term88 A s t _33777.
Proof. exact (EQ_MP (@lem3285737 A s t _33777) (@lem3285736 A _33777 x' s t x h1)). Qed.
Lemma lem3285796 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3285838 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : term52 A t x.
Proof. exact (proj2 (@lem3285611 A x' s t x h1)). Qed.
Lemma lem3285839 {A : Type'} (t : A -> Prop) : (term197 A t) = (term197 A t).
Proof. exact (eq_refl (term197 A t)). Qed.
Lemma lem3285840 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term198 A t x') = (term198 A t x).
Proof. exact (MK_COMB (@lem3285839 A t) (@lem3285784 A x' x h1)). Qed.
Lemma lem3285841 {A : Type'} (t : A -> Prop) (x : A) : (term198 A t x) = (t x).
Proof. exact (eq_refl (term198 A t x)). Qed.
Lemma lem3285842 {A : Type'} (t : A -> Prop) (x' : A) : (term199 A t x') = (term199 A t x').
Proof. exact (eq_refl (term199 A t x')). Qed.
Lemma lem3285843 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term198 A t x') = (term198 A t x)) = ((term198 A t x') = (t x)).
Proof. exact (MK_COMB (@lem3285842 A t x') (@lem3285841 A t x)). Qed.
Lemma lem3285844 {A : Type'} (t : A -> Prop) (x' : A) : (term198 A t x') = (t x').
Proof. exact (eq_refl (term198 A t x')). Qed.
Lemma lem3285845 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3285846 {A : Type'} (t : A -> Prop) (x' : A) : (term199 A t x') = (term200 A t x').
Proof. exact (MK_COMB (@lem3285845) (@lem3285844 A t x')). Qed.
Lemma lem3285847 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3285848 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term198 A t x') = (t x)) = ((t x') = (t x)).
Proof. exact (MK_COMB (@lem3285846 A t x') (@lem3285847 A t x)). Qed.
Lemma lem3285849 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term198 A t x') = (term198 A t x)) = ((t x') = (t x)).
Proof. exact (TRANS (@lem3285843 A x' t x) (@lem3285848 A x' t x)). Qed.
Lemma lem3285850 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (t x') = (t x).
Proof. exact (EQ_MP (@lem3285849 A x' t x) (@lem3285840 A t x' x h1)). Qed.
Lemma lem3285879 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term44 A s t x') : s x'.
Proof. exact (proj1 (@lem3285607 A s t x' h1)). Qed.
Lemma lem3285880 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term44 A s t x') : term201 A s x'.
Proof. exact (fun h0 : term52 A s x' => @lem3285879 A s t x' h1). Qed.
Lemma lem3285882 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3285883 {A : Type'} (s : A -> Prop) (x' : A) : (term201 A s x') = (s x').
Proof. exact (@lem3285882 (s x')). Qed.
Lemma lem3285884 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term44 A s t x') : s x'.
Proof. exact (EQ_MP (@lem3285883 A s x') (@lem3285880 A s t x' h1)). Qed.
Lemma lem3285886 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term44 A s t x') : t x'.
Proof. exact (proj2 (@lem3285607 A s t x' h1)). Qed.
Lemma lem3285887 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term44 A s t x') : term201 A t x'.
Proof. exact (fun h0 : term52 A t x' => @lem3285886 A s t x' h1). Qed.
Lemma lem3285889 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3285890 {A : Type'} (t : A -> Prop) (x' : A) : (term201 A t x') = (t x').
Proof. exact (@lem3285889 (t x')). Qed.
Lemma lem3285891 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term44 A s t x') : t x'.
Proof. exact (EQ_MP (@lem3285890 A t x') (@lem3285887 A s t x' h1)). Qed.
Lemma lem3285893 (a : Prop) (b : Prop) : (term203 a b) = (term204 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3285894 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33774 : A) : (term88 A s t _33774) = (term47 A s t _33774).
Proof. exact (@lem3285893 (s _33774) (t _33774)). Qed.
Lemma lem3285896 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3285897 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33774 : A) : (term47 A s t _33774) = (term205 A s t _33774).
Proof. exact (@lem3285896 (term44 A s t _33774)). Qed.
Lemma lem3285898 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33774 : A) : (term88 A s t _33774) = (term205 A s t _33774).
Proof. exact (TRANS (@lem3285894 A s t _33774) (@lem3285897 A s t _33774)). Qed.
Lemma lem3285900 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term44 A s t x') : term44 A s t x'.
Proof. exact (conj (@lem3285884 A s t x' h1) (@lem3285891 A s t x' h1)). Qed.
Lemma lem3285902 {A : Type'} (_33774 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term205 A s t _33774.
Proof. exact (EQ_MP (@lem3285898 A s t _33774) (@lem3285758 A _33774 s x' t x h1)). Qed.
Lemma lem3285903 {A : Type'} (_33774 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term205 A s t _33774.
Proof. exact (@lem3285902 A _33774 s x' t x h1). Qed.
Lemma lem3285904 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term205 A s t x'.
Proof. exact (@lem3285903 A x' s x' t x h1). Qed.
Lemma lem3285907 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term147 A s x' t x) (h2 : term44 A s t x') : False.
Proof. exact (@lem3285904 A s x' t x h1 (@lem3285900 A s t x' h2)). Qed.
Lemma lem3285908 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term147 A s x' t x) (h2 : term44 A s t x') : term206.
Proof. exact (fun h0 : ~ False => @lem3285907 A x s t x' h1 h2). Qed.
Lemma lem3285910 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3285911 : term206 = False.
Proof. exact (@lem3285910 False). Qed.
Lemma lem3285912 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term147 A s x' t x) (h2 : term44 A s t x') : False.
Proof. exact (EQ_MP (@lem3285911) (@lem3285908 A x s t x' h1 h2)). Qed.
Lemma lem3285940 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3285941 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3285940 A x). Qed.
Lemma lem3285942 {A : Type'} (x : A) : term207 A x.
Proof. exact (fun h0 : term208 A x => @lem3285941 A x). Qed.
Lemma lem3285944 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3285945 {A : Type'} (x : A) : (term207 A x) = (x = x).
Proof. exact (@lem3285944 (x = x)). Qed.
Lemma lem3285946 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3285945 A x) (@lem3285942 A x)). Qed.
Lemma lem3285948 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3285949 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term201 A t x.
Proof. exact (fun h0 : term52 A t x => @lem3285948 A t x h1). Qed.
Lemma lem3285951 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3285952 {A : Type'} (t : A -> Prop) (x : A) : (term201 A t x) = (t x).
Proof. exact (@lem3285951 (t x)). Qed.
Lemma lem3285953 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3285952 A t x) (@lem3285949 A t x h1)). Qed.
Lemma lem3285955 (a : Prop) (b : Prop) : (term203 a b) = (term204 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3285956 {A : Type'} (x : A) (t : A -> Prop) (_33775 : A) : (term196 A x t _33775) = (term209 A x t _33775).
Proof. exact (@lem3285955 (_33775 = x) (t _33775)). Qed.
Lemma lem3285958 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3285959 {A : Type'} (x : A) (t : A -> Prop) (_33775 : A) : (term209 A x t _33775) = (term210 A x t _33775).
Proof. exact (@lem3285958 (term211 A x t _33775)). Qed.
Lemma lem3285960 {A : Type'} (x : A) (t : A -> Prop) (_33775 : A) : (term196 A x t _33775) = (term210 A x t _33775).
Proof. exact (TRANS (@lem3285956 A x t _33775) (@lem3285959 A x t _33775)). Qed.
Lemma lem3285962 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term212 A t x.
Proof. exact (conj (@lem3285946 A x) (@lem3285953 A t x h1)). Qed.
Lemma lem3285964 {A : Type'} (_33775 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term210 A x t _33775.
Proof. exact (EQ_MP (@lem3285960 A x t _33775) (@lem3285766 A _33775 s x' t x h1)). Qed.
Lemma lem3285965 {A : Type'} (_33775 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term210 A x t _33775.
Proof. exact (@lem3285964 A _33775 s x' t x h1). Qed.
Lemma lem3285966 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : term213 A t x.
Proof. exact (@lem3285965 A x s x' t x h1). Qed.
Lemma lem3285969 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term147 A s x' t x) : False.
Proof. exact (@lem3285966 A s x' t x h2 (@lem3285962 A t x h1)). Qed.
Lemma lem3285970 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term147 A s x' t x) : term206.
Proof. exact (fun h0 : ~ False => @lem3285969 A s x' t x h1 h2). Qed.
Lemma lem3285972 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3285973 : term206 = False.
Proof. exact (@lem3285972 False). Qed.
Lemma lem3285974 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term147 A s x' t x) : False.
Proof. exact (EQ_MP (@lem3285973) (@lem3285970 A s x' t x h1 h2)). Qed.
Lemma lem3285976 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term165 A x' s t x) (h2 : x' = x) : t x.
Proof. exact (EQ_MP (@lem3285850 A t x' x h2) (@lem3285782 A x' s t x h1)). Qed.
Lemma lem3285977 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term165 A x' s t x) (h2 : x' = x) : term201 A t x.
Proof. exact (fun h0 : term52 A t x => @lem3285976 A s t x' x h1 h2). Qed.
Lemma lem3285979 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3285980 {A : Type'} (t : A -> Prop) (x : A) : (term201 A t x) = (t x).
Proof. exact (@lem3285979 (t x)). Qed.
Lemma lem3285981 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term165 A x' s t x) (h2 : x' = x) : t x.
Proof. exact (EQ_MP (@lem3285980 A t x) (@lem3285977 A s t x' x h1 h2)). Qed.
Lemma lem3285984 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3285986 {A : Type'} (t : A -> Prop) (x : A) : (term52 A t x) = (term214 A t x).
Proof. exact (@lem3285984 (t x)). Qed.
Lemma lem3285989 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : term214 A t x.
Proof. exact (EQ_MP (@lem3285986 A t x) (@lem3285838 A x' s t x h1)). Qed.
Lemma lem3285992 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term165 A x' s t x) (h2 : x' = x) : False.
Proof. exact (@lem3285989 A x' s t x h1 (@lem3285981 A s t x' x h1 h2)). Qed.
Lemma lem3285993 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term165 A x' s t x) (h2 : x' = x) : term206.
Proof. exact (fun h0 : ~ False => @lem3285992 A s t x' x h1 h2). Qed.
Lemma lem3285995 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3285996 : term206 = False.
Proof. exact (@lem3285995 False). Qed.
Lemma lem3285999 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3286000 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term201 A s x'.
Proof. exact (fun h0 : term52 A s x' => @lem3285999 A s x' h1). Qed.
Lemma lem3286002 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3286003 {A : Type'} (s : A -> Prop) (x' : A) : (term201 A s x') = (s x').
Proof. exact (@lem3286002 (s x')). Qed.
Lemma lem3286004 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3286003 A s x') (@lem3286000 A s x' h1)). Qed.
Lemma lem3286006 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : t x'.
Proof. exact (proj2 (@lem3285612 A x' s t x h1)). Qed.
Lemma lem3286007 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : term201 A t x'.
Proof. exact (fun h0 : term52 A t x' => @lem3286006 A x' s t x h1). Qed.
Lemma lem3286009 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3286010 {A : Type'} (t : A -> Prop) (x' : A) : (term201 A t x') = (t x').
Proof. exact (@lem3286009 (t x')). Qed.
Lemma lem3286011 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : t x'.
Proof. exact (EQ_MP (@lem3286010 A t x') (@lem3286007 A x' s t x h1)). Qed.
Lemma lem3286013 (a : Prop) (b : Prop) : (term203 a b) = (term204 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3286014 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33777 : A) : (term88 A s t _33777) = (term47 A s t _33777).
Proof. exact (@lem3286013 (s _33777) (t _33777)). Qed.
Lemma lem3286016 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3286017 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33777 : A) : (term47 A s t _33777) = (term205 A s t _33777).
Proof. exact (@lem3286016 (term44 A s t _33777)). Qed.
Lemma lem3286018 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33777 : A) : (term88 A s t _33777) = (term205 A s t _33777).
Proof. exact (TRANS (@lem3286014 A s t _33777) (@lem3286017 A s t _33777)). Qed.
Lemma lem3286020 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x') (h2 : term165 A x' s t x) : term44 A s t x'.
Proof. exact (conj (@lem3286004 A s x' h1) (@lem3286011 A x' s t x h2)). Qed.
Lemma lem3286022 {A : Type'} (_33777 : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : term205 A s t _33777.
Proof. exact (EQ_MP (@lem3286018 A s t _33777) (@lem3285790 A _33777 x' s t x h1)). Qed.
Lemma lem3286023 {A : Type'} (_33777 : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : term205 A s t _33777.
Proof. exact (@lem3286022 A _33777 x' s t x h1). Qed.
Lemma lem3286024 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : term205 A s t x'.
Proof. exact (@lem3286023 A x' x' s t x h1). Qed.
Lemma lem3286027 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x') (h2 : term165 A x' s t x) : False.
Proof. exact (@lem3286024 A x' s t x h2 (@lem3286020 A x' s t x h1 h2)). Qed.
Lemma lem3286028 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x') (h2 : term165 A x' s t x) : term206.
Proof. exact (fun h0 : ~ False => @lem3286027 A x' s t x h1 h2). Qed.
Lemma lem3286030 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3286031 : term206 = False.
Proof. exact (@lem3286030 False). Qed.
Lemma lem3286032 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x') (h2 : term165 A x' s t x) : False.
Proof. exact (EQ_MP (@lem3286031) (@lem3286028 A x' s t x h1 h2)). Qed.
Lemma lem3286033 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term165 A x' s t x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3285996) (@lem3285993 A s t x' x h1 h2)). Qed.
Lemma lem3286034 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x') (h2 : term165 A x' s t x) : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3286032 A x' s t x h1 h2) (fun h3 : False => @lem3285796 A s x' h1)). Qed.
Lemma lem3286035 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x') (h2 : term165 A x' s t x) : False.
Proof. exact (EQ_MP (@lem3286034 A x' s t x h1 h2) (@lem3285796 A s x' h1)). Qed.
Lemma lem3286036 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term165 A x' s t x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3286033 A s t x' x h1 h2) (fun h3 : False => @lem3285784 A x' x h2)). Qed.
Lemma lem3286037 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term165 A x' s t x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3286036 A s t x' x h1 h2) (@lem3285784 A x' x h2)). Qed.
Lemma lem3286038 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term147 A s x' t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3285974 A s x' t x h1 h2) (fun h3 : False => @lem3285760 A t x h1)). Qed.
Lemma lem3286039 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term147 A s x' t x) : False.
Proof. exact (EQ_MP (@lem3286038 A s x' t x h1 h2) (@lem3285760 A t x h1)). Qed.
Lemma lem3286040 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x') (h2 : term165 A x' s t x) : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3286035 A x' s t x h1 h2) (fun h3 : False => @lem3285726 A s x' h1)). Qed.
Lemma lem3286041 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x') (h2 : term165 A x' s t x) : False.
Proof. exact (EQ_MP (@lem3286040 A x' s t x h1 h2) (@lem3285726 A s x' h1)). Qed.
Lemma lem3286042 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term165 A x' s t x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3286037 A s t x' x h1 h2) (fun h3 : False => @lem3285701 A x' x h2)). Qed.
Lemma lem3286043 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term165 A x' s t x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3286042 A s t x' x h1 h2) (@lem3285701 A x' x h2)). Qed.
Lemma lem3286044 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term147 A s x' t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3286039 A s x' t x h1 h2) (fun h3 : False => @lem3285676 A t x h1)). Qed.
Lemma lem3286045 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term147 A s x' t x) : False.
Proof. exact (EQ_MP (@lem3286044 A s x' t x h1 h2) (@lem3285676 A t x h1)). Qed.
Lemma lem3286046 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x') (h2 : term165 A x' s t x) : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3286041 A x' s t x h1 h2) (fun h3 : False => @lem3285726 A s x' h1)). Qed.
Lemma lem3286047 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x') (h2 : term165 A x' s t x) : False.
Proof. exact (EQ_MP (@lem3286046 A x' s t x h1 h2) (@lem3285726 A s x' h1)). Qed.
Lemma lem3286048 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term165 A x' s t x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3286043 A s t x' x h1 h2) (fun h3 : False => @lem3285701 A x' x h2)). Qed.
Lemma lem3286049 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term165 A x' s t x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3286048 A s t x' x h1 h2) (@lem3285701 A x' x h2)). Qed.
Lemma lem3286050 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term147 A s x' t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3286045 A s x' t x h1 h2) (fun h3 : False => @lem3285676 A t x h1)). Qed.
Lemma lem3286051 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term147 A s x' t x) : False.
Proof. exact (EQ_MP (@lem3286050 A s x' t x h1 h2) (@lem3285676 A t x h1)). Qed.
Lemma lem3286052 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term165 A x' s t x) : False.
Proof. exact (or_elim (@lem3285616 A x' s t x h1) (fun h0 : x' = x => @lem3286049 A s t x' x h1 h0) (fun h0 : s x' => @lem3286047 A x' s t x h0 h1)). Qed.
Lemma lem3286053 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term147 A s x' t x) : False.
Proof. exact (or_elim (@lem3285605 A s x' t x h1) (fun h0 : term44 A s t x' => @lem3285912 A x s t x' h1 h0) (fun h0 : t x => @lem3286051 A s x' t x h0 h1)). Qed.
Lemma lem3286054 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A x' s t x) : False.
Proof. exact (or_elim (@lem3285602 A x' s t x h1) (fun h0 : term147 A s x' t x => @lem3286053 A s x' t x h0) (fun h0 : term165 A x' s t x => @lem3286052 A x' s t x h0)). Qed.
Lemma lem3286055 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A x' s t x) : (term186 A x' s t x) = False.
Proof. exact (prop_ext (fun h2 : term186 A x' s t x => @lem3286054 A x' s t x h1) (fun h2 : False => @lem3285602 A x' s t x h1)). Qed.
Lemma lem3286056 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A x' s t x) : False.
Proof. exact (EQ_MP (@lem3286055 A x' s t x h1) (@lem3285602 A x' s t x h1)). Qed.
Lemma lem3286057 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term69 A s t x) : False.
Proof. exact (ex_elim (@lem3285509 A s t x h1) (fun x' : A => fun h0 : term188 A s t x x' => @lem3286056 A x' s t x h0)). Qed.
Lemma lem3286058 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term69 A s t x) : (term69 A s t x) = False.
Proof. exact (prop_ext (fun h2 : term69 A s t x => @lem3286057 A s t x h1) (fun h2 : False => @lem3285176 A s t x h1)). Qed.
Lemma lem3286059 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term69 A s t x) : False.
Proof. exact (EQ_MP (@lem3286058 A s t x h1) (@lem3285176 A s t x h1)). Qed.
Lemma lem3286060 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term68 A s t x.
Proof. exact (fun h0 : term69 A s t x => @lem3286059 A s t x h0). Qed.
Lemma lem3286061 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term40 A x s t) = (term53 A s t x).
Proof. exact (EQ_MP (@lem3285175 A s t x) (@lem3286060 A s t x)). Qed.
Lemma lem3286066 {A : Type'} (s : A -> Prop) (x : A) : term55 A s x.
Proof. exact (fun t : A -> Prop => @lem3286061 A s t x). Qed.
Lemma lem3286071 {A : Type'} (x : A) : term57 A x.
Proof. exact (fun s : A -> Prop => @lem3286066 A s x). Qed.
Lemma lem3286076 {A : Type'} : term59 A.
Proof. exact (fun x : A => @lem3286071 A x). Qed.
Lemma lem3286077 {A : Type'} : term61 A.
Proof. exact (EQ_MP (@lem3285171 A) (@lem3286076 A)). Qed.
Lemma lem3286079 {A : Type'} : term61 A.
Proof. exact (@lem3285048 A (@lem3286077 A)). Qed.
Lemma lem3286080 {A : Type'} (h1 : term62 A) : False.
Proof. exact (@lem3286079 A (@lem3285032 A h1)). Qed.
Lemma lem3286081 {A : Type'} (h1 : term62 A) : (term62 A) = False.
Proof. exact (prop_ext (fun h2 : term62 A => @lem3286080 A h1) (fun h2 : False => @lem3285032 A h1)). Qed.
Lemma lem3286082 {A : Type'} (h1 : term62 A) : False.
Proof. exact (EQ_MP (@lem3286081 A h1) (@lem3285032 A h1)). Qed.
Lemma lem3286083 {A : Type'} : term61 A.
Proof. exact (fun h0 : term62 A => @lem3286082 A h0). Qed.
Lemma lem3286084 {A : Type'} : term59 A.
Proof. exact (EQ_MP (@lem3285031 A) (@lem3286083 A)). Qed.
Lemma lem3286085 {A : Type'} : term23 A.
Proof. exact (EQ_MP (@lem3285027 A) (@lem3286084 A)). Qed.
Lemma lem3286086 {A : Type'} : term22 A.
Proof. exact (EQ_MP (@lem3284866 A) (@lem3286085 A)). Qed.
