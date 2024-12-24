Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_WF_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import LT_spec.
Require Import num_INDUCTION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16464_spec.
Require Import thm16474_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Require Import thm89994_spec.
Lemma lem112851 : term0.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem112852 (m : nat) : term1 m.
Proof. exact (@lem112851 m). Qed.
Lemma lem112853 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem112854 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem112853 m) (@lem112852 m)). Qed.
Lemma lem112855 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem112854 m n). Qed.
Lemma lem112856 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem112858 : term6.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem112859 (m : nat) : term7 m.
Proof. exact (@lem112858 m). Qed.
Lemma lem112860 (m : nat) : (term7 m) = ((term8 m) = False).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem112862 (P : nat -> Prop) : term9 P.
Proof. exact (@lem75586 (term10 P)). Qed.
Lemma lem112863 (P : nat -> Prop) : (term9 P) = (term11 P).
Proof. exact (eq_refl (term9 P)). Qed.
Lemma lem112864 (P : nat -> Prop) : term11 P.
Proof. exact (EQ_MP (@lem112863 P) (@lem112862 P)). Qed.
Lemma lem112872 {A B : Type'} (f : A -> B) (y : A) : (term12 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem112873 (f : nat -> Prop) (y : nat) : (term13 f y) = (f y).
Proof. exact (@lem112872 nat Prop f y). Qed.
Lemma lem112874 (P : nat -> Prop) : (term14 P) = (term15 P).
Proof. exact (@lem112873 (term10 P) (NUMERAL 0)). Qed.
Lemma lem112875 (n : nat) (P : nat -> Prop) : (term16 P n) = (term17 n P).
Proof. exact (eq_refl (term16 P n)). Qed.
Lemma lem112876 (P : nat -> Prop) : (term18 P) = (term10 P).
Proof. exact (fun_ext (fun n : nat => @lem112875 n P)). Qed.
Lemma lem112877 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem112878 (P : nat -> Prop) : (term14 P) = (term15 P).
Proof. exact (MK_COMB (@lem112876 P) (@lem112877)). Qed.
Lemma lem112879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem112880 (P : nat -> Prop) : (term19 P) = (term20 P).
Proof. exact (MK_COMB (@lem112879) (@lem112878 P)). Qed.
Lemma lem112881 (P : nat -> Prop) : (term15 P) = (term21 P).
Proof. exact (eq_refl (term15 P)). Qed.
Lemma lem112882 (P : nat -> Prop) : ((term14 P) = (term15 P)) = ((term15 P) = (term21 P)).
Proof. exact (MK_COMB (@lem112880 P) (@lem112881 P)). Qed.
Lemma lem112883 (P : nat -> Prop) : (term15 P) = (term21 P).
Proof. exact (EQ_MP (@lem112882 P) (@lem112874 P)). Qed.
Lemma lem112891 (m : nat) : (term8 m) = False.
Proof. exact (EQ_MP (@lem112860 m) (@lem112859 m)). Qed.
Lemma lem112892 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem112893 (m : nat) : (term22 m) = (imp False).
Proof. exact (MK_COMB (@lem112892) (@lem112891 m)). Qed.
Lemma lem112894 (P : nat -> Prop) (m : nat) : (P m) = (P m).
Proof. exact (eq_refl (P m)). Qed.
Lemma lem112895 (P : nat -> Prop) (m : nat) : (term23 P m) = (term24 P m).
Proof. exact (MK_COMB (@lem112893 m) (@lem112894 P m)). Qed.
Lemma lem112897 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem112898 (P : nat -> Prop) (m : nat) : (term24 P m) = True.
Proof. exact (@lem112897 (P m)). Qed.
Lemma lem112899 (P : nat -> Prop) (m : nat) : (term23 P m) = True.
Proof. exact (TRANS (@lem112895 P m) (@lem112898 P m)). Qed.
Lemma lem112900 (P : nat -> Prop) : (term25 P) = term26.
Proof. exact (fun_ext (fun m : nat => @lem112899 P m)). Qed.
Lemma lem112901 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem112902 (P : nat -> Prop) : (term21 P) = term27.
Proof. exact (MK_COMB (@lem112901) (@lem112900 P)). Qed.
Lemma lem112904 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem112905 (t : Prop) : (term29 t) = t.
Proof. exact (@lem112904 nat t). Qed.
Lemma lem112906 : term27 = True.
Proof. exact (@lem112905 True). Qed.
Lemma lem112907 (P : nat -> Prop) : (term21 P) = True.
Proof. exact (TRANS (@lem112902 P) (@lem112906)). Qed.
Lemma lem112908 (P : nat -> Prop) : (term15 P) = True.
Proof. exact (TRANS (@lem112883 P) (@lem112907 P)). Qed.
Lemma lem112909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem112910 (P : nat -> Prop) : (term30 P) = (and True).
Proof. exact (MK_COMB (@lem112909) (@lem112908 P)). Qed.
Lemma lem112918 {A B : Type'} (f : A -> B) (y : A) : (term12 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem112919 (f : nat -> Prop) (y : nat) : (term13 f y) = (f y).
Proof. exact (@lem112918 nat Prop f y). Qed.
Lemma lem112920 (P : nat -> Prop) (n : nat) : (term31 P n) = (term16 P n).
Proof. exact (@lem112919 (term10 P) n). Qed.
Lemma lem112921 (n : nat) (P : nat -> Prop) : (term16 P n) = (term17 n P).
Proof. exact (eq_refl (term16 P n)). Qed.
Lemma lem112922 (P : nat -> Prop) : (term18 P) = (term10 P).
Proof. exact (fun_ext (fun n : nat => @lem112921 n P)). Qed.
Lemma lem112923 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem112924 (P : nat -> Prop) (n : nat) : (term31 P n) = (term16 P n).
Proof. exact (MK_COMB (@lem112922 P) (@lem112923 n)). Qed.
Lemma lem112925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem112926 (P : nat -> Prop) (n : nat) : (term32 P n) = (term33 P n).
Proof. exact (MK_COMB (@lem112925) (@lem112924 P n)). Qed.
Lemma lem112927 (n : nat) (P : nat -> Prop) : (term16 P n) = (term17 n P).
Proof. exact (eq_refl (term16 P n)). Qed.
Lemma lem112928 (n : nat) (P : nat -> Prop) : ((term31 P n) = (term16 P n)) = ((term16 P n) = (term17 n P)).
Proof. exact (MK_COMB (@lem112926 P n) (@lem112927 n P)). Qed.
Lemma lem112929 (n : nat) (P : nat -> Prop) : (term16 P n) = (term17 n P).
Proof. exact (EQ_MP (@lem112928 n P) (@lem112920 P n)). Qed.
Lemma lem112936 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem112937 (n : nat) (P : nat -> Prop) : (term34 P n) = (term35 n P).
Proof. exact (MK_COMB (@lem112936) (@lem112929 n P)). Qed.
Lemma lem112939 {A B : Type'} (f : A -> B) (y : A) : (term12 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem112940 (f : nat -> Prop) (y : nat) : (term13 f y) = (f y).
Proof. exact (@lem112939 nat Prop f y). Qed.
Lemma lem112941 (P : nat -> Prop) (n : nat) : (term36 P n) = (term37 P n).
Proof. exact (@lem112940 (term10 P) (S n)). Qed.
Lemma lem112942 (n : nat) (P : nat -> Prop) : (term16 P n) = (term17 n P).
Proof. exact (eq_refl (term16 P n)). Qed.
Lemma lem112943 (P : nat -> Prop) : (term18 P) = (term10 P).
Proof. exact (fun_ext (fun n : nat => @lem112942 n P)). Qed.
Lemma lem112944 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem112945 (P : nat -> Prop) (n : nat) : (term36 P n) = (term37 P n).
Proof. exact (MK_COMB (@lem112943 P) (@lem112944 n)). Qed.
Lemma lem112946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem112947 (P : nat -> Prop) (n : nat) : (term38 P n) = (term39 P n).
Proof. exact (MK_COMB (@lem112946) (@lem112945 P n)). Qed.
Lemma lem112948 (n : nat) (P : nat -> Prop) : (term37 P n) = (term40 n P).
Proof. exact (eq_refl (term37 P n)). Qed.
Lemma lem112949 (n : nat) (P : nat -> Prop) : ((term36 P n) = (term37 P n)) = ((term37 P n) = (term40 n P)).
Proof. exact (MK_COMB (@lem112947 P n) (@lem112948 n P)). Qed.
Lemma lem112950 (n : nat) (P : nat -> Prop) : (term37 P n) = (term40 n P).
Proof. exact (EQ_MP (@lem112949 n P) (@lem112941 P n)). Qed.
Lemma lem112958 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem112856 m n) (@lem112855 m n)). Qed.
Lemma lem112963 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem112964 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (MK_COMB (@lem112963) (@lem112958 m n)). Qed.
Lemma lem112965 (P : nat -> Prop) (m : nat) : (P m) = (P m).
Proof. exact (eq_refl (P m)). Qed.
Lemma lem112966 (n : nat) (P : nat -> Prop) (m : nat) : (term43 n P m) = (term44 n P m).
Proof. exact (MK_COMB (@lem112964 m n) (@lem112965 P m)). Qed.
Lemma lem112969 (n : nat) (P : nat -> Prop) : (term45 n P) = (term46 n P).
Proof. exact (fun_ext (fun m : nat => @lem112966 n P m)). Qed.
Lemma lem112970 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem112971 (n : nat) (P : nat -> Prop) : (term40 n P) = (term47 n P).
Proof. exact (MK_COMB (@lem112970) (@lem112969 n P)). Qed.
Lemma lem112976 (n : nat) (P : nat -> Prop) : (term37 P n) = (term47 n P).
Proof. exact (TRANS (@lem112950 n P) (@lem112971 n P)). Qed.
Lemma lem112977 (n : nat) (P : nat -> Prop) : (term48 P n) = (term49 n P).
Proof. exact (MK_COMB (@lem112937 n P) (@lem112976 n P)). Qed.
Lemma lem112980 (P : nat -> Prop) : (term50 P) = (term51 P).
Proof. exact (fun_ext (fun n : nat => @lem112977 n P)). Qed.
Lemma lem112981 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem112982 (P : nat -> Prop) : (term52 P) = (term53 P).
Proof. exact (MK_COMB (@lem112981) (@lem112980 P)). Qed.
Lemma lem112987 (P : nat -> Prop) : (term54 P) = (term55 P).
Proof. exact (MK_COMB (@lem112910 P) (@lem112982 P)). Qed.
Lemma lem112989 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem112990 (P : nat -> Prop) : (term55 P) = (term53 P).
Proof. exact (@lem112989 (term53 P)). Qed.
Lemma lem113013 (P : nat -> Prop) : (term54 P) = (term53 P).
Proof. exact (TRANS (@lem112987 P) (@lem112990 P)). Qed.
Lemma lem113014 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem113015 (P : nat -> Prop) : (term56 P) = (term57 P).
Proof. exact (MK_COMB (@lem113014) (@lem113013 P)). Qed.
Lemma lem113021 {A B : Type'} (f : A -> B) (y : A) : (term12 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem113022 (f : nat -> Prop) (y : nat) : (term13 f y) = (f y).
Proof. exact (@lem113021 nat Prop f y). Qed.
Lemma lem113023 (P : nat -> Prop) (n : nat) : (term31 P n) = (term16 P n).
Proof. exact (@lem113022 (term10 P) n). Qed.
Lemma lem113024 (n : nat) (P : nat -> Prop) : (term16 P n) = (term17 n P).
Proof. exact (eq_refl (term16 P n)). Qed.
Lemma lem113025 (P : nat -> Prop) : (term18 P) = (term10 P).
Proof. exact (fun_ext (fun n : nat => @lem113024 n P)). Qed.
Lemma lem113026 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem113027 (P : nat -> Prop) (n : nat) : (term31 P n) = (term16 P n).
Proof. exact (MK_COMB (@lem113025 P) (@lem113026 n)). Qed.
Lemma lem113028 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem113029 (P : nat -> Prop) (n : nat) : (term32 P n) = (term33 P n).
Proof. exact (MK_COMB (@lem113028) (@lem113027 P n)). Qed.
Lemma lem113030 (n : nat) (P : nat -> Prop) : (term16 P n) = (term17 n P).
Proof. exact (eq_refl (term16 P n)). Qed.
Lemma lem113031 (n : nat) (P : nat -> Prop) : ((term31 P n) = (term16 P n)) = ((term16 P n) = (term17 n P)).
Proof. exact (MK_COMB (@lem113029 P n) (@lem113030 n P)). Qed.
Lemma lem113032 (n : nat) (P : nat -> Prop) : (term16 P n) = (term17 n P).
Proof. exact (EQ_MP (@lem113031 n P) (@lem113023 P n)). Qed.
Lemma lem113039 (P : nat -> Prop) : (term18 P) = (term10 P).
Proof. exact (fun_ext (fun n : nat => @lem113032 n P)). Qed.
Lemma lem113040 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113041 (P : nat -> Prop) : (term58 P) = (term59 P).
Proof. exact (MK_COMB (@lem113040) (@lem113039 P)). Qed.
Lemma lem113046 (P : nat -> Prop) : (term11 P) = (term60 P).
Proof. exact (MK_COMB (@lem113015 P) (@lem113041 P)). Qed.
Lemma lem113049 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem113050 (P : nat -> Prop) : (term61 P) = (term62 P).
Proof. exact (MK_COMB (@lem113049) (@lem113046 P)). Qed.
Lemma lem113069 (P : nat -> Prop) : (term63 P) = (term63 P).
Proof. exact (eq_refl (term63 P)). Qed.
Lemma lem113070 (P : nat -> Prop) : (term64 P) = (term65 P).
Proof. exact (MK_COMB (@lem113050 P) (@lem113069 P)). Qed.
Lemma lem113073 (P : nat -> Prop) : (term65 P) = (term64 P).
Proof. exact (SYM (@lem113070 P)). Qed.
Lemma lem113075 (p : Prop) : p = (term66 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem113076 (P : nat -> Prop) : (term65 P) = (term67 P).
Proof. exact (@lem113075 (term65 P)). Qed.
Lemma lem113077 (P : nat -> Prop) : (term67 P) = (term65 P).
Proof. exact (SYM (@lem113076 P)). Qed.
Lemma lem113078 (P : nat -> Prop) (h1 : term68 P) : term68 P.
Proof. exact (h1). Qed.
Lemma lem113081 (P : nat -> Prop) (h1 : term69 P) : term69 P.
Proof. exact (h1). Qed.
Lemma lem113082 (P : nat -> Prop) : term70 P.
Proof. exact (fun h0 : term69 P => @lem113081 P h0). Qed.
Lemma lem113083 (P : nat -> Prop) (h1 : term70 P) : term70 P.
Proof. exact (h1). Qed.
Lemma lem113084 (P : nat -> Prop) (h1 : term69 P) : term69 P.
Proof. exact (h1). Qed.
Lemma lem113085 (P : nat -> Prop) (h1 : term69 P) (h2 : term70 P) : term69 P.
Proof. exact (@lem113083 P h2 (@lem113084 P h1)). Qed.
Lemma lem113086 (P : nat -> Prop) (h1 : term69 P) : term71 P.
Proof. exact (fun h0 : term70 P => @lem113085 P h1 h0). Qed.
Lemma lem113087 (P : nat -> Prop) (h1 : term70 P) : term70 P.
Proof. exact (h1). Qed.
Lemma lem113088 (P : nat -> Prop) (h1 : term69 P) (h2 : term70 P) : term69 P.
Proof. exact (@lem113086 P h1 (@lem113087 P h2)). Qed.
Lemma lem113089 (P : nat -> Prop) (h1 : term70 P) : term70 P.
Proof. exact (fun h0 : term69 P => @lem113088 P h0 h1). Qed.
Lemma lem113090 (P : nat -> Prop) : term72 P.
Proof. exact (fun h0 : term70 P => @lem113089 P h0). Qed.
Lemma lem113093 (P : nat -> Prop) : term70 P.
Proof. exact (@lem113090 P (@lem113082 P)). Qed.
Lemma lem113153 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem113154 : term73 = term74.
Proof. exact (@lem113153 term75). Qed.
Lemma lem113162 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem113163 (m : nat) : ((term8 m) = False) = (term76 m).
Proof. exact (@lem113162 (term8 m)). Qed.
Lemma lem113164 : term77 = term78.
Proof. exact (fun_ext (fun m : nat => @lem113163 m)). Qed.
Lemma lem113165 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113166 : term6 = term79.
Proof. exact (MK_COMB (@lem113165) (@lem113164)). Qed.
Lemma lem113171 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem113172 : term80 = term81.
Proof. exact (MK_COMB (@lem113171) (@lem113166)). Qed.
Lemma lem113183 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem113184 : term75 = term82.
Proof. exact (MK_COMB (@lem113172) (@lem113183)). Qed.
Lemma lem113187 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem113188 : term74 = term83.
Proof. exact (MK_COMB (@lem113187) (@lem113184)). Qed.
Lemma lem113189 : term73 = term83.
Proof. exact (TRANS (@lem113154) (@lem113188)). Qed.
Lemma lem113190 (P : nat -> Prop) : (term84 P) = (term84 P).
Proof. exact (eq_refl (term84 P)). Qed.
Lemma lem113191 (P : nat -> Prop) : (term69 P) = (term85 P).
Proof. exact (MK_COMB (@lem113190 P) (@lem113189)). Qed.
Lemma lem113194 : term86 = term87.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem113191 P)). Qed.
Lemma lem113195 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem113204 : term88 = term89.
Proof. exact (MK_COMB (@lem113195) (@lem113194)). Qed.
Lemma lem113213 (m : nat) (n : nat) : ((term4 m n) = (term5 m n)) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl ((term4 m n) = (term5 m n))). Qed.
Lemma lem113214 (m : nat) : (term90 m) = (term90 m).
Proof. exact (fun_ext (fun n : nat => @lem113213 m n)). Qed.
Lemma lem113215 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113216 (m : nat) : (term2 m) = (term2 m).
Proof. exact (MK_COMB (@lem113215) (@lem113214 m)). Qed.
Lemma lem113217 : term91 = term91.
Proof. exact (fun_ext (fun m : nat => @lem113216 m)). Qed.
Lemma lem113218 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113219 : term0 = term0.
Proof. exact (MK_COMB (@lem113218) (@lem113217)). Qed.
Lemma lem113222 (m : nat) : (term76 m) = (term76 m).
Proof. exact (eq_refl (term76 m)). Qed.
Lemma lem113223 : term78 = term78.
Proof. exact (fun_ext (fun m : nat => @lem113222 m)). Qed.
Lemma lem113224 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113225 : term79 = term79.
Proof. exact (MK_COMB (@lem113224) (@lem113223)). Qed.
Lemma lem113226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem113227 : term81 = term81.
Proof. exact (MK_COMB (@lem113226) (@lem113225)). Qed.
Lemma lem113228 : term82 = term82.
Proof. exact (MK_COMB (@lem113227) (@lem113219)). Qed.
Lemma lem113229 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem113230 : term83 = term83.
Proof. exact (MK_COMB (@lem113229) (@lem113228)). Qed.
Lemma lem113231 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem113232 (P : nat -> Prop) : (term92 P) = (term92 P).
Proof. exact (fun_ext (fun n : nat => @lem113231 P n)). Qed.
Lemma lem113233 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113234 (P : nat -> Prop) : (term93 P) = (term93 P).
Proof. exact (MK_COMB (@lem113233) (@lem113232 P)). Qed.
Lemma lem113235 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem113240 (n : nat) (P : nat -> Prop) (m : nat) : (term94 n P m) = (term94 n P m).
Proof. exact (eq_refl (term94 n P m)). Qed.
Lemma lem113241 (n : nat) (P : nat -> Prop) : (term95 n P) = (term95 n P).
Proof. exact (fun_ext (fun m : nat => @lem113240 n P m)). Qed.
Lemma lem113242 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113243 (n : nat) (P : nat -> Prop) : (term17 n P) = (term17 n P).
Proof. exact (MK_COMB (@lem113242) (@lem113241 n P)). Qed.
Lemma lem113244 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem113245 (n : nat) (P : nat -> Prop) : (term35 n P) = (term35 n P).
Proof. exact (MK_COMB (@lem113244) (@lem113243 n P)). Qed.
Lemma lem113246 (P : nat -> Prop) (n : nat) : (term96 P n) = (term96 P n).
Proof. exact (MK_COMB (@lem113245 n P) (@lem113235 P n)). Qed.
Lemma lem113247 (P : nat -> Prop) : (term97 P) = (term97 P).
Proof. exact (fun_ext (fun n : nat => @lem113246 P n)). Qed.
Lemma lem113248 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113249 (P : nat -> Prop) : (term98 P) = (term98 P).
Proof. exact (MK_COMB (@lem113248) (@lem113247 P)). Qed.
Lemma lem113250 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem113251 (P : nat -> Prop) : (term99 P) = (term99 P).
Proof. exact (MK_COMB (@lem113250) (@lem113249 P)). Qed.
Lemma lem113252 (P : nat -> Prop) : (term63 P) = (term63 P).
Proof. exact (MK_COMB (@lem113251 P) (@lem113234 P)). Qed.
Lemma lem113257 (n : nat) (P : nat -> Prop) (m : nat) : (term94 n P m) = (term94 n P m).
Proof. exact (eq_refl (term94 n P m)). Qed.
Lemma lem113258 (n : nat) (P : nat -> Prop) : (term95 n P) = (term95 n P).
Proof. exact (fun_ext (fun m : nat => @lem113257 n P m)). Qed.
Lemma lem113259 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113260 (n : nat) (P : nat -> Prop) : (term17 n P) = (term17 n P).
Proof. exact (MK_COMB (@lem113259) (@lem113258 n P)). Qed.
Lemma lem113261 (P : nat -> Prop) : (term10 P) = (term10 P).
Proof. exact (fun_ext (fun n : nat => @lem113260 n P)). Qed.
Lemma lem113262 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113263 (P : nat -> Prop) : (term59 P) = (term59 P).
Proof. exact (MK_COMB (@lem113262) (@lem113261 P)). Qed.
Lemma lem113272 (n : nat) (P : nat -> Prop) (m : nat) : (term44 n P m) = (term44 n P m).
Proof. exact (eq_refl (term44 n P m)). Qed.
Lemma lem113273 (n : nat) (P : nat -> Prop) : (term46 n P) = (term46 n P).
Proof. exact (fun_ext (fun m : nat => @lem113272 n P m)). Qed.
Lemma lem113274 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113275 (n : nat) (P : nat -> Prop) : (term47 n P) = (term47 n P).
Proof. exact (MK_COMB (@lem113274) (@lem113273 n P)). Qed.
Lemma lem113280 (n : nat) (P : nat -> Prop) (m : nat) : (term94 n P m) = (term94 n P m).
Proof. exact (eq_refl (term94 n P m)). Qed.
Lemma lem113281 (n : nat) (P : nat -> Prop) : (term95 n P) = (term95 n P).
Proof. exact (fun_ext (fun m : nat => @lem113280 n P m)). Qed.
Lemma lem113282 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113283 (n : nat) (P : nat -> Prop) : (term17 n P) = (term17 n P).
Proof. exact (MK_COMB (@lem113282) (@lem113281 n P)). Qed.
Lemma lem113284 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem113285 (n : nat) (P : nat -> Prop) : (term35 n P) = (term35 n P).
Proof. exact (MK_COMB (@lem113284) (@lem113283 n P)). Qed.
Lemma lem113286 (n : nat) (P : nat -> Prop) : (term49 n P) = (term49 n P).
Proof. exact (MK_COMB (@lem113285 n P) (@lem113275 n P)). Qed.
Lemma lem113287 (P : nat -> Prop) : (term51 P) = (term51 P).
Proof. exact (fun_ext (fun n : nat => @lem113286 n P)). Qed.
Lemma lem113288 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113289 (P : nat -> Prop) : (term53 P) = (term53 P).
Proof. exact (MK_COMB (@lem113288) (@lem113287 P)). Qed.
Lemma lem113290 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem113291 (P : nat -> Prop) : (term57 P) = (term57 P).
Proof. exact (MK_COMB (@lem113290) (@lem113289 P)). Qed.
Lemma lem113292 (P : nat -> Prop) : (term60 P) = (term60 P).
Proof. exact (MK_COMB (@lem113291 P) (@lem113263 P)). Qed.
Lemma lem113293 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem113294 (P : nat -> Prop) : (term62 P) = (term62 P).
Proof. exact (MK_COMB (@lem113293) (@lem113292 P)). Qed.
Lemma lem113295 (P : nat -> Prop) : (term65 P) = (term65 P).
Proof. exact (MK_COMB (@lem113294 P) (@lem113252 P)). Qed.
Lemma lem113296 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem113297 (P : nat -> Prop) : (term68 P) = (term68 P).
Proof. exact (MK_COMB (@lem113296) (@lem113295 P)). Qed.
Lemma lem113298 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem113299 (P : nat -> Prop) : (term84 P) = (term84 P).
Proof. exact (MK_COMB (@lem113298) (@lem113297 P)). Qed.
Lemma lem113300 (P : nat -> Prop) : (term85 P) = (term85 P).
Proof. exact (MK_COMB (@lem113299 P) (@lem113230)). Qed.
Lemma lem113301 : term87 = term87.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem113300 P)). Qed.
Lemma lem113302 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem113303 : term89 = term89.
Proof. exact (MK_COMB (@lem113302) (@lem113301)). Qed.
Lemma lem113404 : term88 = term89.
Proof. exact (TRANS (@lem113204) (@lem113303)). Qed.
Lemma lem113405 : term89 = term88.
Proof. exact (SYM (@lem113404)). Qed.
Lemma lem113406 (P : nat -> Prop) (h1 : term68 P) : term68 P.
Proof. exact (h1). Qed.
Lemma lem113407 (h1 : term82) : term82.
Proof. exact (h1). Qed.
Lemma lem113414 (n : nat) (P : nat -> Prop) (m : nat) : (term94 n P m) = (term100 n P m).
Proof. exact (@lem17265 (Peano.lt m n) (P m)). Qed.
Lemma lem113415 (n : nat) (P : nat -> Prop) : (term95 n P) = (term101 n P).
Proof. exact (fun_ext (fun m : nat => @lem113414 n P m)). Qed.
Lemma lem113416 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113417 (n : nat) (P : nat -> Prop) : (term17 n P) = (term102 n P).
Proof. exact (MK_COMB (@lem113416) (@lem113415 n P)). Qed.
Lemma lem113428 (n : nat) (P : nat -> Prop) (m : nat) : (term103 n P m) = (term104 n P m).
Proof. exact (@lem17362 (term5 m n) (P m)). Qed.
Lemma lem113429 (P : nat -> Prop) : (term105 P) = (term106 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem113430 (n : nat) (P : nat -> Prop) : (term107 n P) = (term108 n P).
Proof. exact (@lem113429 (term46 n P)). Qed.
Lemma lem113431 (n : nat) (P : nat -> Prop) (m : nat) : (term109 n P m) = (term44 n P m).
Proof. exact (eq_refl (term109 n P m)). Qed.
Lemma lem113432 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem113433 (n : nat) (P : nat -> Prop) (m : nat) : (term110 n P m) = (term103 n P m).
Proof. exact (MK_COMB (@lem113432) (@lem113431 n P m)). Qed.
Lemma lem113434 (n : nat) (P : nat -> Prop) (m : nat) : (term110 n P m) = (term104 n P m).
Proof. exact (TRANS (@lem113433 n P m) (@lem113428 n P m)). Qed.
Lemma lem113435 (n : nat) (P : nat -> Prop) : (term111 n P) = (term112 n P).
Proof. exact (fun_ext (fun m : nat => @lem113434 n P m)). Qed.
Lemma lem113436 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113437 (n : nat) (P : nat -> Prop) : (term108 n P) = (term113 n P).
Proof. exact (MK_COMB (@lem113436) (@lem113435 n P)). Qed.
Lemma lem113438 (n : nat) (P : nat -> Prop) : (term107 n P) = (term113 n P).
Proof. exact (TRANS (@lem113430 n P) (@lem113437 n P)). Qed.
Lemma lem113439 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem113440 (n : nat) (P : nat -> Prop) : (term114 n P) = (term115 n P).
Proof. exact (MK_COMB (@lem113439) (@lem113417 n P)). Qed.
Lemma lem113441 (n : nat) (P : nat -> Prop) : (term116 n P) = (term117 n P).
Proof. exact (MK_COMB (@lem113440 n P) (@lem113438 n P)). Qed.
Lemma lem113442 (n : nat) (P : nat -> Prop) : (term118 n P) = (term116 n P).
Proof. exact (@lem17362 (term17 n P) (term47 n P)). Qed.
Lemma lem113443 (n : nat) (P : nat -> Prop) : (term118 n P) = (term117 n P).
Proof. exact (TRANS (@lem113442 n P) (@lem113441 n P)). Qed.
Lemma lem113444 (P : nat -> Prop) : (term105 P) = (term106 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem113445 (P : nat -> Prop) : (term119 P) = (term120 P).
Proof. exact (@lem113444 (term51 P)). Qed.
Lemma lem113446 (n : nat) (P : nat -> Prop) : (term121 P n) = (term49 n P).
Proof. exact (eq_refl (term121 P n)). Qed.
Lemma lem113447 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem113448 (n : nat) (P : nat -> Prop) : (term122 P n) = (term118 n P).
Proof. exact (MK_COMB (@lem113447) (@lem113446 n P)). Qed.
Lemma lem113449 (n : nat) (P : nat -> Prop) : (term122 P n) = (term117 n P).
Proof. exact (TRANS (@lem113448 n P) (@lem113443 n P)). Qed.
Lemma lem113450 (P : nat -> Prop) : (term123 P) = (term124 P).
Proof. exact (fun_ext (fun n : nat => @lem113449 n P)). Qed.
Lemma lem113451 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113452 (P : nat -> Prop) : (term120 P) = (term125 P).
Proof. exact (MK_COMB (@lem113451) (@lem113450 P)). Qed.
Lemma lem113453 (P : nat -> Prop) : (term119 P) = (term125 P).
Proof. exact (TRANS (@lem113445 P) (@lem113452 P)). Qed.
Lemma lem113460 (n : nat) (P : nat -> Prop) (m : nat) : (term94 n P m) = (term100 n P m).
Proof. exact (@lem17265 (Peano.lt m n) (P m)). Qed.
Lemma lem113461 (n : nat) (P : nat -> Prop) : (term95 n P) = (term101 n P).
Proof. exact (fun_ext (fun m : nat => @lem113460 n P m)). Qed.
Lemma lem113462 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113463 (n : nat) (P : nat -> Prop) : (term17 n P) = (term102 n P).
Proof. exact (MK_COMB (@lem113462) (@lem113461 n P)). Qed.
Lemma lem113464 (P : nat -> Prop) : (term10 P) = (term126 P).
Proof. exact (fun_ext (fun n : nat => @lem113463 n P)). Qed.
Lemma lem113465 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113466 (P : nat -> Prop) : (term59 P) = (term127 P).
Proof. exact (MK_COMB (@lem113465) (@lem113464 P)). Qed.
Lemma lem113467 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem113468 (P : nat -> Prop) : (term128 P) = (term129 P).
Proof. exact (MK_COMB (@lem113467) (@lem113453 P)). Qed.
Lemma lem113469 (P : nat -> Prop) : (term130 P) = (term131 P).
Proof. exact (MK_COMB (@lem113468 P) (@lem113466 P)). Qed.
Lemma lem113470 (P : nat -> Prop) : (term60 P) = (term130 P).
Proof. exact (@lem17265 (term53 P) (term59 P)). Qed.
Lemma lem113471 (P : nat -> Prop) : (term60 P) = (term131 P).
Proof. exact (TRANS (@lem113470 P) (@lem113469 P)). Qed.
Lemma lem113478 (n : nat) (P : nat -> Prop) (m : nat) : (term132 n P m) = (term133 n P m).
Proof. exact (@lem17362 (Peano.lt m n) (P m)). Qed.
Lemma lem113479 (P : nat -> Prop) : (term105 P) = (term106 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem113480 (n : nat) (P : nat -> Prop) : (term134 n P) = (term135 n P).
Proof. exact (@lem113479 (term95 n P)). Qed.
Lemma lem113481 (n : nat) (P : nat -> Prop) (m : nat) : (term136 n P m) = (term94 n P m).
Proof. exact (eq_refl (term136 n P m)). Qed.
Lemma lem113482 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem113483 (n : nat) (P : nat -> Prop) (m : nat) : (term137 n P m) = (term132 n P m).
Proof. exact (MK_COMB (@lem113482) (@lem113481 n P m)). Qed.
Lemma lem113484 (n : nat) (P : nat -> Prop) (m : nat) : (term137 n P m) = (term133 n P m).
Proof. exact (TRANS (@lem113483 n P m) (@lem113478 n P m)). Qed.
Lemma lem113485 (n : nat) (P : nat -> Prop) : (term138 n P) = (term139 n P).
Proof. exact (fun_ext (fun m : nat => @lem113484 n P m)). Qed.
Lemma lem113486 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113487 (n : nat) (P : nat -> Prop) : (term135 n P) = (term140 n P).
Proof. exact (MK_COMB (@lem113486) (@lem113485 n P)). Qed.
Lemma lem113488 (n : nat) (P : nat -> Prop) : (term134 n P) = (term140 n P).
Proof. exact (TRANS (@lem113480 n P) (@lem113487 n P)). Qed.
Lemma lem113489 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem113490 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem113491 (n : nat) (P : nat -> Prop) : (term141 n P) = (term142 n P).
Proof. exact (MK_COMB (@lem113490) (@lem113488 n P)). Qed.
Lemma lem113492 (P : nat -> Prop) (n : nat) : (term143 P n) = (term144 P n).
Proof. exact (MK_COMB (@lem113491 n P) (@lem113489 P n)). Qed.
Lemma lem113493 (P : nat -> Prop) (n : nat) : (term96 P n) = (term143 P n).
Proof. exact (@lem17265 (term17 n P) (P n)). Qed.
Lemma lem113494 (P : nat -> Prop) (n : nat) : (term96 P n) = (term144 P n).
Proof. exact (TRANS (@lem113493 P n) (@lem113492 P n)). Qed.
Lemma lem113495 (P : nat -> Prop) : (term97 P) = (term145 P).
Proof. exact (fun_ext (fun n : nat => @lem113494 P n)). Qed.
Lemma lem113496 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113497 (P : nat -> Prop) : (term98 P) = (term146 P).
Proof. exact (MK_COMB (@lem113496) (@lem113495 P)). Qed.
Lemma lem113499 (P : nat -> Prop) : (term105 P) = (term106 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem113500 (P : nat -> Prop) : (term147 P) = (term148 P).
Proof. exact (@lem113499 (term92 P)). Qed.
Lemma lem113501 (P : nat -> Prop) (n : nat) : (term13 P n) = (P n).
Proof. exact (eq_refl (term13 P n)). Qed.
Lemma lem113502 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem113504 (P : nat -> Prop) (n : nat) : (term149 P n) = (term150 P n).
Proof. exact (MK_COMB (@lem113502) (@lem113501 P n)). Qed.
Lemma lem113505 (P : nat -> Prop) : (term151 P) = (term152 P).
Proof. exact (fun_ext (fun n : nat => @lem113504 P n)). Qed.
Lemma lem113506 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113507 (P : nat -> Prop) : (term148 P) = (term106 P).
Proof. exact (MK_COMB (@lem113506) (@lem113505 P)). Qed.
Lemma lem113508 (P : nat -> Prop) : (term147 P) = (term106 P).
Proof. exact (TRANS (@lem113500 P) (@lem113507 P)). Qed.
Lemma lem113509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem113510 (P : nat -> Prop) : (term153 P) = (term154 P).
Proof. exact (MK_COMB (@lem113509) (@lem113497 P)). Qed.
Lemma lem113511 (P : nat -> Prop) : (term155 P) = (term156 P).
Proof. exact (MK_COMB (@lem113510 P) (@lem113508 P)). Qed.
Lemma lem113512 (P : nat -> Prop) : (term157 P) = (term155 P).
Proof. exact (@lem17362 (term98 P) (term93 P)). Qed.
Lemma lem113513 (P : nat -> Prop) : (term157 P) = (term156 P).
Proof. exact (TRANS (@lem113512 P) (@lem113511 P)). Qed.
Lemma lem113514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem113515 (P : nat -> Prop) : (term158 P) = (term159 P).
Proof. exact (MK_COMB (@lem113514) (@lem113471 P)). Qed.
Lemma lem113516 (P : nat -> Prop) : (term160 P) = (term161 P).
Proof. exact (MK_COMB (@lem113515 P) (@lem113513 P)). Qed.
Lemma lem113517 (P : nat -> Prop) : (term68 P) = (term160 P).
Proof. exact (@lem17362 (term60 P) (term63 P)). Qed.
Lemma lem113518 (P : nat -> Prop) : (term68 P) = (term161 P).
Proof. exact (TRANS (@lem113517 P) (@lem113516 P)). Qed.
Lemma lem113769 {A : Type'} (P : Prop) (Q : A -> Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem113770 (P : Prop) (Q : nat -> Prop) : (term164 P Q) = (term165 P Q).
Proof. exact (@lem113769 nat P Q). Qed.
Lemma lem113771 (n : nat) (P : nat -> Prop) : (term166 n P) = (term167 n P).
Proof. exact (@lem113770 (term102 n P) (term112 n P)). Qed.
Lemma lem113772 (n : nat) (P : nat -> Prop) (m : nat) : (term168 n P m) = (term104 n P m).
Proof. exact (eq_refl (term168 n P m)). Qed.
Lemma lem113773 (n : nat) (P : nat -> Prop) : (term169 n P) = (term112 n P).
Proof. exact (fun_ext (fun m : nat => @lem113772 n P m)). Qed.
Lemma lem113774 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113775 (n : nat) (P : nat -> Prop) : (term170 n P) = (term113 n P).
Proof. exact (MK_COMB (@lem113774) (@lem113773 n P)). Qed.
Lemma lem113776 (n : nat) (P : nat -> Prop) : (term115 n P) = (term115 n P).
Proof. exact (eq_refl (term115 n P)). Qed.
Lemma lem113777 (n : nat) (P : nat -> Prop) : (term166 n P) = (term117 n P).
Proof. exact (MK_COMB (@lem113776 n P) (@lem113775 n P)). Qed.
Lemma lem113778 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem113779 (n : nat) (P : nat -> Prop) : (term171 n P) = (term172 n P).
Proof. exact (MK_COMB (@lem113778) (@lem113777 n P)). Qed.
Lemma lem113780 (n : nat) (P : nat -> Prop) (m : nat) : (term168 n P m) = (term104 n P m).
Proof. exact (eq_refl (term168 n P m)). Qed.
Lemma lem113781 (n : nat) (P : nat -> Prop) : (term115 n P) = (term115 n P).
Proof. exact (eq_refl (term115 n P)). Qed.
Lemma lem113782 (n : nat) (P : nat -> Prop) (m : nat) : (term173 n P m) = (term174 n P m).
Proof. exact (MK_COMB (@lem113781 n P) (@lem113780 n P m)). Qed.
Lemma lem113783 (n : nat) (P : nat -> Prop) : (term175 n P) = (term176 n P).
Proof. exact (fun_ext (fun m : nat => @lem113782 n P m)). Qed.
Lemma lem113784 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113785 (n : nat) (P : nat -> Prop) : (term167 n P) = (term177 n P).
Proof. exact (MK_COMB (@lem113784) (@lem113783 n P)). Qed.
Lemma lem113786 (n : nat) (P : nat -> Prop) : ((term166 n P) = (term167 n P)) = ((term117 n P) = (term177 n P)).
Proof. exact (MK_COMB (@lem113779 n P) (@lem113785 n P)). Qed.
Lemma lem113787 (n : nat) (P : nat -> Prop) : (term117 n P) = (term177 n P).
Proof. exact (EQ_MP (@lem113786 n P) (@lem113771 n P)). Qed.
Lemma lem113788 (P : nat -> Prop) : (term124 P) = (term178 P).
Proof. exact (fun_ext (fun n : nat => @lem113787 n P)). Qed.
Lemma lem113789 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113790 (P : nat -> Prop) : (term125 P) = (term179 P).
Proof. exact (MK_COMB (@lem113789) (@lem113788 P)). Qed.
Lemma lem113791 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem113792 (P : nat -> Prop) : (term129 P) = (term180 P).
Proof. exact (MK_COMB (@lem113791) (@lem113790 P)). Qed.
Lemma lem113793 (P : nat -> Prop) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem113794 (P : nat -> Prop) : (term131 P) = (term181 P).
Proof. exact (MK_COMB (@lem113792 P) (@lem113793 P)). Qed.
Lemma lem113796 {A : Type'} (P : A -> Prop) (Q : Prop) : (term182 A P Q) = (term183 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem113797 (P : nat -> Prop) (Q : Prop) : (term184 P Q) = (term185 P Q).
Proof. exact (@lem113796 nat P Q). Qed.
Lemma lem113798 (P : nat -> Prop) : (term186 P) = (term187 P).
Proof. exact (@lem113797 (term178 P) (term127 P)). Qed.
Lemma lem113799 (n : nat) (P : nat -> Prop) : (term188 P n) = (term177 n P).
Proof. exact (eq_refl (term188 P n)). Qed.
Lemma lem113800 (P : nat -> Prop) : (term189 P) = (term178 P).
Proof. exact (fun_ext (fun n : nat => @lem113799 n P)). Qed.
Lemma lem113801 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113802 (P : nat -> Prop) : (term190 P) = (term179 P).
Proof. exact (MK_COMB (@lem113801) (@lem113800 P)). Qed.
Lemma lem113803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem113804 (P : nat -> Prop) : (term191 P) = (term180 P).
Proof. exact (MK_COMB (@lem113803) (@lem113802 P)). Qed.
Lemma lem113805 (P : nat -> Prop) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem113806 (P : nat -> Prop) : (term186 P) = (term181 P).
Proof. exact (MK_COMB (@lem113804 P) (@lem113805 P)). Qed.
Lemma lem113807 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem113808 (P : nat -> Prop) : (term192 P) = (term193 P).
Proof. exact (MK_COMB (@lem113807) (@lem113806 P)). Qed.
Lemma lem113809 (n : nat) (P : nat -> Prop) : (term188 P n) = (term177 n P).
Proof. exact (eq_refl (term188 P n)). Qed.
Lemma lem113810 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem113811 (n : nat) (P : nat -> Prop) : (term194 P n) = (term195 n P).
Proof. exact (MK_COMB (@lem113810) (@lem113809 n P)). Qed.
Lemma lem113812 (P : nat -> Prop) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem113813 (n : nat) (P : nat -> Prop) : (term196 n P) = (term197 n P).
Proof. exact (MK_COMB (@lem113811 n P) (@lem113812 P)). Qed.
Lemma lem113814 (P : nat -> Prop) : (term198 P) = (term199 P).
Proof. exact (fun_ext (fun n : nat => @lem113813 n P)). Qed.
Lemma lem113815 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113816 (P : nat -> Prop) : (term187 P) = (term200 P).
Proof. exact (MK_COMB (@lem113815) (@lem113814 P)). Qed.
Lemma lem113817 (P : nat -> Prop) : ((term186 P) = (term187 P)) = ((term181 P) = (term200 P)).
Proof. exact (MK_COMB (@lem113808 P) (@lem113816 P)). Qed.
Lemma lem113818 (P : nat -> Prop) : (term181 P) = (term200 P).
Proof. exact (EQ_MP (@lem113817 P) (@lem113798 P)). Qed.
Lemma lem113820 {A : Type'} (P : A -> Prop) (Q : Prop) : (term182 A P Q) = (term183 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem113821 (P : nat -> Prop) (Q : Prop) : (term184 P Q) = (term185 P Q).
Proof. exact (@lem113820 nat P Q). Qed.
Lemma lem113822 (n : nat) (P : nat -> Prop) : (term201 n P) = (term202 n P).
Proof. exact (@lem113821 (term176 n P) (term127 P)). Qed.
Lemma lem113823 (n : nat) (P : nat -> Prop) (m : nat) : (term203 n P m) = (term174 n P m).
Proof. exact (eq_refl (term203 n P m)). Qed.
Lemma lem113824 (n : nat) (P : nat -> Prop) : (term204 n P) = (term176 n P).
Proof. exact (fun_ext (fun m : nat => @lem113823 n P m)). Qed.
Lemma lem113825 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113826 (n : nat) (P : nat -> Prop) : (term205 n P) = (term177 n P).
Proof. exact (MK_COMB (@lem113825) (@lem113824 n P)). Qed.
Lemma lem113827 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem113828 (n : nat) (P : nat -> Prop) : (term206 n P) = (term195 n P).
Proof. exact (MK_COMB (@lem113827) (@lem113826 n P)). Qed.
Lemma lem113829 (P : nat -> Prop) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem113830 (n : nat) (P : nat -> Prop) : (term201 n P) = (term197 n P).
Proof. exact (MK_COMB (@lem113828 n P) (@lem113829 P)). Qed.
Lemma lem113831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem113832 (n : nat) (P : nat -> Prop) : (term207 n P) = (term208 n P).
Proof. exact (MK_COMB (@lem113831) (@lem113830 n P)). Qed.
Lemma lem113833 (n : nat) (P : nat -> Prop) (m : nat) : (term203 n P m) = (term174 n P m).
Proof. exact (eq_refl (term203 n P m)). Qed.
Lemma lem113834 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem113835 (n : nat) (P : nat -> Prop) (m : nat) : (term209 n P m) = (term210 n P m).
Proof. exact (MK_COMB (@lem113834) (@lem113833 n P m)). Qed.
Lemma lem113836 (P : nat -> Prop) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem113837 (n : nat) (m : nat) (P : nat -> Prop) : (term211 n m P) = (term212 n m P).
Proof. exact (MK_COMB (@lem113835 n P m) (@lem113836 P)). Qed.
Lemma lem113838 (n : nat) (P : nat -> Prop) : (term213 n P) = (term214 n P).
Proof. exact (fun_ext (fun m : nat => @lem113837 n m P)). Qed.
Lemma lem113839 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113840 (n : nat) (P : nat -> Prop) : (term202 n P) = (term215 n P).
Proof. exact (MK_COMB (@lem113839) (@lem113838 n P)). Qed.
Lemma lem113841 (n : nat) (P : nat -> Prop) : ((term201 n P) = (term202 n P)) = ((term197 n P) = (term215 n P)).
Proof. exact (MK_COMB (@lem113832 n P) (@lem113840 n P)). Qed.
Lemma lem113842 (n : nat) (P : nat -> Prop) : (term197 n P) = (term215 n P).
Proof. exact (EQ_MP (@lem113841 n P) (@lem113822 n P)). Qed.
Lemma lem113843 (P : nat -> Prop) : (term199 P) = (term216 P).
Proof. exact (fun_ext (fun n : nat => @lem113842 n P)). Qed.
Lemma lem113844 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113845 (P : nat -> Prop) : (term200 P) = (term217 P).
Proof. exact (MK_COMB (@lem113844) (@lem113843 P)). Qed.
Lemma lem113846 (P : nat -> Prop) : (term181 P) = (term217 P).
Proof. exact (TRANS (@lem113818 P) (@lem113845 P)). Qed.
Lemma lem113847 (P : nat -> Prop) : (term131 P) = (term217 P).
Proof. exact (TRANS (@lem113794 P) (@lem113846 P)). Qed.
Lemma lem113848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem113849 (P : nat -> Prop) : (term159 P) = (term218 P).
Proof. exact (MK_COMB (@lem113848) (@lem113847 P)). Qed.
Lemma lem113851 {A : Type'} (P : A -> Prop) (Q : Prop) : (term182 A P Q) = (term183 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem113852 (P : nat -> Prop) (Q : Prop) : (term184 P Q) = (term185 P Q).
Proof. exact (@lem113851 nat P Q). Qed.
Lemma lem113853 (P : nat -> Prop) (n : nat) : (term219 P n) = (term220 P n).
Proof. exact (@lem113852 (term139 n P) (P n)). Qed.
Lemma lem113854 (n : nat) (P : nat -> Prop) (m : nat) : (term221 n P m) = (term133 n P m).
Proof. exact (eq_refl (term221 n P m)). Qed.
Lemma lem113855 (n : nat) (P : nat -> Prop) : (term222 n P) = (term139 n P).
Proof. exact (fun_ext (fun m : nat => @lem113854 n P m)). Qed.
Lemma lem113856 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113857 (n : nat) (P : nat -> Prop) : (term223 n P) = (term140 n P).
Proof. exact (MK_COMB (@lem113856) (@lem113855 n P)). Qed.
Lemma lem113858 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem113859 (n : nat) (P : nat -> Prop) : (term224 n P) = (term142 n P).
Proof. exact (MK_COMB (@lem113858) (@lem113857 n P)). Qed.
Lemma lem113860 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem113861 (P : nat -> Prop) (n : nat) : (term219 P n) = (term144 P n).
Proof. exact (MK_COMB (@lem113859 n P) (@lem113860 P n)). Qed.
Lemma lem113862 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem113863 (P : nat -> Prop) (n : nat) : (term225 P n) = (term226 P n).
Proof. exact (MK_COMB (@lem113862) (@lem113861 P n)). Qed.
Lemma lem113864 (n : nat) (P : nat -> Prop) (m : nat) : (term221 n P m) = (term133 n P m).
Proof. exact (eq_refl (term221 n P m)). Qed.
Lemma lem113865 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem113866 (n : nat) (P : nat -> Prop) (m : nat) : (term227 n P m) = (term228 n P m).
Proof. exact (MK_COMB (@lem113865) (@lem113864 n P m)). Qed.
Lemma lem113867 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem113868 (m : nat) (P : nat -> Prop) (n : nat) : (term229 m P n) = (term230 m P n).
Proof. exact (MK_COMB (@lem113866 n P m) (@lem113867 P n)). Qed.
Lemma lem113869 (P : nat -> Prop) (n : nat) : (term231 P n) = (term232 P n).
Proof. exact (fun_ext (fun m : nat => @lem113868 m P n)). Qed.
Lemma lem113870 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113871 (P : nat -> Prop) (n : nat) : (term220 P n) = (term233 P n).
Proof. exact (MK_COMB (@lem113870) (@lem113869 P n)). Qed.
Lemma lem113872 (P : nat -> Prop) (n : nat) : ((term219 P n) = (term220 P n)) = ((term144 P n) = (term233 P n)).
Proof. exact (MK_COMB (@lem113863 P n) (@lem113871 P n)). Qed.
Lemma lem113873 (P : nat -> Prop) (n : nat) : (term144 P n) = (term233 P n).
Proof. exact (EQ_MP (@lem113872 P n) (@lem113853 P n)). Qed.
Lemma lem113874 (P : nat -> Prop) : (term145 P) = (term234 P).
Proof. exact (fun_ext (fun n : nat => @lem113873 P n)). Qed.
Lemma lem113875 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113876 (P : nat -> Prop) : (term146 P) = (term235 P).
Proof. exact (MK_COMB (@lem113875) (@lem113874 P)). Qed.
Lemma lem113878 {A B : Type'} (P : type1413 A B) : (term236 A B P) = (term237 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem113879 (P : type1605) : (term238 P) = (term239 P).
Proof. exact (@lem113878 nat nat P). Qed.
Lemma lem113880 (P : nat -> Prop) : (term240 P) = (term241 P).
Proof. exact (@lem113879 (term242 P)). Qed.
Lemma lem113881 (P : nat -> Prop) (n : nat) : (term243 P n) = (term232 P n).
Proof. exact (eq_refl (term243 P n)). Qed.
Lemma lem113882 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem113883 (P : nat -> Prop) (n : nat) (m : nat) : (term244 P n m) = (term245 P n m).
Proof. exact (MK_COMB (@lem113881 P n) (@lem113882 m)). Qed.
Lemma lem113884 (m : nat) (P : nat -> Prop) (n : nat) : (term245 P n m) = (term230 m P n).
Proof. exact (eq_refl (term245 P n m)). Qed.
Lemma lem113885 (m : nat) (P : nat -> Prop) (n : nat) : (term244 P n m) = (term230 m P n).
Proof. exact (TRANS (@lem113883 P n m) (@lem113884 m P n)). Qed.
Lemma lem113886 (P : nat -> Prop) (n : nat) : (term246 P n) = (term232 P n).
Proof. exact (fun_ext (fun m : nat => @lem113885 m P n)). Qed.
Lemma lem113887 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113888 (P : nat -> Prop) (n : nat) : (term247 P n) = (term233 P n).
Proof. exact (MK_COMB (@lem113887) (@lem113886 P n)). Qed.
Lemma lem113889 (P : nat -> Prop) : (term248 P) = (term234 P).
Proof. exact (fun_ext (fun n : nat => @lem113888 P n)). Qed.
Lemma lem113890 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113891 (P : nat -> Prop) : (term240 P) = (term235 P).
Proof. exact (MK_COMB (@lem113890) (@lem113889 P)). Qed.
Lemma lem113892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem113893 (P : nat -> Prop) : (term249 P) = (term250 P).
Proof. exact (MK_COMB (@lem113892) (@lem113891 P)). Qed.
Lemma lem113894 (P : nat -> Prop) (n : nat) : (term243 P n) = (term232 P n).
Proof. exact (eq_refl (term243 P n)). Qed.
Lemma lem113895 (m : nat -> nat) (n : nat) : (m n) = (m n).
Proof. exact (eq_refl (m n)). Qed.
Lemma lem113896 (P : nat -> Prop) (m : nat -> nat) (n : nat) : (term251 P m n) = (term252 P m n).
Proof. exact (MK_COMB (@lem113894 P n) (@lem113895 m n)). Qed.
Lemma lem113897 (m : nat -> nat) (P : nat -> Prop) (n : nat) : (term252 P m n) = (term253 m P n).
Proof. exact (eq_refl (term252 P m n)). Qed.
Lemma lem113898 (m : nat -> nat) (P : nat -> Prop) (n : nat) : (term251 P m n) = (term253 m P n).
Proof. exact (TRANS (@lem113896 P m n) (@lem113897 m P n)). Qed.
Lemma lem113899 (m : nat -> nat) (P : nat -> Prop) : (term254 P m) = (term255 m P).
Proof. exact (fun_ext (fun n : nat => @lem113898 m P n)). Qed.
Lemma lem113900 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem113901 (m : nat -> nat) (P : nat -> Prop) : (term256 P m) = (term257 m P).
Proof. exact (MK_COMB (@lem113900) (@lem113899 m P)). Qed.
Lemma lem113902 (P : nat -> Prop) : (term258 P) = (term259 P).
Proof. exact (fun_ext (fun m : nat -> nat => @lem113901 m P)). Qed.
Lemma lem113903 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem113904 (P : nat -> Prop) : (term241 P) = (term260 P).
Proof. exact (MK_COMB (@lem113903) (@lem113902 P)). Qed.
Lemma lem113905 (P : nat -> Prop) : ((term240 P) = (term241 P)) = ((term235 P) = (term260 P)).
Proof. exact (MK_COMB (@lem113893 P) (@lem113904 P)). Qed.
Lemma lem113906 (P : nat -> Prop) : (term235 P) = (term260 P).
Proof. exact (EQ_MP (@lem113905 P) (@lem113880 P)). Qed.
Lemma lem113907 (P : nat -> Prop) : (term146 P) = (term260 P).
Proof. exact (TRANS (@lem113876 P) (@lem113906 P)). Qed.
Lemma lem113908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem113909 (P : nat -> Prop) : (term154 P) = (term261 P).
Proof. exact (MK_COMB (@lem113908) (@lem113907 P)). Qed.
Lemma lem113910 (P : nat -> Prop) : (term106 P) = (term106 P).
Proof. exact (eq_refl (term106 P)). Qed.
Lemma lem113911 (P : nat -> Prop) : (term156 P) = (term262 P).
Proof. exact (MK_COMB (@lem113909 P) (@lem113910 P)). Qed.
Lemma lem113913 {A : Type'} (P : A -> Prop) (Q : Prop) : (term263 A P Q) = (term264 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem113914 (P : type1002) (Q : Prop) : (term265 P Q) = (term266 P Q).
Proof. exact (@lem113913 (nat -> nat) P Q). Qed.
Lemma lem113915 (P : nat -> Prop) : (term267 P) = (term268 P).
Proof. exact (@lem113914 (term259 P) (term106 P)). Qed.
Lemma lem113916 (m : nat -> nat) (P : nat -> Prop) : (term269 P m) = (term257 m P).
Proof. exact (eq_refl (term269 P m)). Qed.
Lemma lem113917 (P : nat -> Prop) : (term270 P) = (term259 P).
Proof. exact (fun_ext (fun m : nat -> nat => @lem113916 m P)). Qed.
Lemma lem113918 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem113919 (P : nat -> Prop) : (term271 P) = (term260 P).
Proof. exact (MK_COMB (@lem113918) (@lem113917 P)). Qed.
Lemma lem113920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem113921 (P : nat -> Prop) : (term272 P) = (term261 P).
Proof. exact (MK_COMB (@lem113920) (@lem113919 P)). Qed.
Lemma lem113922 (P : nat -> Prop) : (term106 P) = (term106 P).
Proof. exact (eq_refl (term106 P)). Qed.
Lemma lem113923 (P : nat -> Prop) : (term267 P) = (term262 P).
Proof. exact (MK_COMB (@lem113921 P) (@lem113922 P)). Qed.
Lemma lem113924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem113925 (P : nat -> Prop) : (term273 P) = (term274 P).
Proof. exact (MK_COMB (@lem113924) (@lem113923 P)). Qed.
Lemma lem113926 (m : nat -> nat) (P : nat -> Prop) : (term269 P m) = (term257 m P).
Proof. exact (eq_refl (term269 P m)). Qed.
Lemma lem113927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem113928 (m : nat -> nat) (P : nat -> Prop) : (term275 P m) = (term276 m P).
Proof. exact (MK_COMB (@lem113927) (@lem113926 m P)). Qed.
Lemma lem113929 (P : nat -> Prop) : (term106 P) = (term106 P).
Proof. exact (eq_refl (term106 P)). Qed.
Lemma lem113930 (m : nat -> nat) (P : nat -> Prop) : (term277 m P) = (term278 m P).
Proof. exact (MK_COMB (@lem113928 m P) (@lem113929 P)). Qed.
Lemma lem113931 (P : nat -> Prop) : (term279 P) = (term280 P).
Proof. exact (fun_ext (fun m : nat -> nat => @lem113930 m P)). Qed.
Lemma lem113932 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem113933 (P : nat -> Prop) : (term268 P) = (term281 P).
Proof. exact (MK_COMB (@lem113932) (@lem113931 P)). Qed.
Lemma lem113934 (P : nat -> Prop) : ((term267 P) = (term268 P)) = ((term262 P) = (term281 P)).
Proof. exact (MK_COMB (@lem113925 P) (@lem113933 P)). Qed.
Lemma lem113935 (P : nat -> Prop) : (term262 P) = (term281 P).
Proof. exact (EQ_MP (@lem113934 P) (@lem113915 P)). Qed.
Lemma lem113937 {A : Type'} (P : Prop) (Q : A -> Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem113938 (P : Prop) (Q : nat -> Prop) : (term164 P Q) = (term165 P Q).
Proof. exact (@lem113937 nat P Q). Qed.
Lemma lem113939 (m : nat -> nat) (P : nat -> Prop) : (term282 m P) = (term283 m P).
Proof. exact (@lem113938 (term257 m P) (term152 P)). Qed.
Lemma lem113940 (P : nat -> Prop) (n : nat) : (term284 P n) = (term150 P n).
Proof. exact (eq_refl (term284 P n)). Qed.
Lemma lem113941 (P : nat -> Prop) : (term285 P) = (term152 P).
Proof. exact (fun_ext (fun n : nat => @lem113940 P n)). Qed.
Lemma lem113942 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113943 (P : nat -> Prop) : (term286 P) = (term106 P).
Proof. exact (MK_COMB (@lem113942) (@lem113941 P)). Qed.
Lemma lem113944 (m : nat -> nat) (P : nat -> Prop) : (term276 m P) = (term276 m P).
Proof. exact (eq_refl (term276 m P)). Qed.
Lemma lem113945 (m : nat -> nat) (P : nat -> Prop) : (term282 m P) = (term278 m P).
Proof. exact (MK_COMB (@lem113944 m P) (@lem113943 P)). Qed.
Lemma lem113946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem113947 (m : nat -> nat) (P : nat -> Prop) : (term287 m P) = (term288 m P).
Proof. exact (MK_COMB (@lem113946) (@lem113945 m P)). Qed.
Lemma lem113948 (P : nat -> Prop) (n : nat) : (term284 P n) = (term150 P n).
Proof. exact (eq_refl (term284 P n)). Qed.
Lemma lem113949 (m : nat -> nat) (P : nat -> Prop) : (term276 m P) = (term276 m P).
Proof. exact (eq_refl (term276 m P)). Qed.
Lemma lem113950 (m : nat -> nat) (P : nat -> Prop) (n : nat) : (term289 m P n) = (term290 m P n).
Proof. exact (MK_COMB (@lem113949 m P) (@lem113948 P n)). Qed.
Lemma lem113951 (m : nat -> nat) (P : nat -> Prop) : (term291 m P) = (term292 m P).
Proof. exact (fun_ext (fun n : nat => @lem113950 m P n)). Qed.
Lemma lem113952 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113953 (m : nat -> nat) (P : nat -> Prop) : (term283 m P) = (term293 m P).
Proof. exact (MK_COMB (@lem113952) (@lem113951 m P)). Qed.
Lemma lem113954 (m : nat -> nat) (P : nat -> Prop) : ((term282 m P) = (term283 m P)) = ((term278 m P) = (term293 m P)).
Proof. exact (MK_COMB (@lem113947 m P) (@lem113953 m P)). Qed.
Lemma lem113955 (m : nat -> nat) (P : nat -> Prop) : (term278 m P) = (term293 m P).
Proof. exact (EQ_MP (@lem113954 m P) (@lem113939 m P)). Qed.
Lemma lem113956 (P : nat -> Prop) : (term280 P) = (term294 P).
Proof. exact (fun_ext (fun m : nat -> nat => @lem113955 m P)). Qed.
Lemma lem113957 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem113958 (P : nat -> Prop) : (term281 P) = (term295 P).
Proof. exact (MK_COMB (@lem113957) (@lem113956 P)). Qed.
Lemma lem113959 (P : nat -> Prop) : (term262 P) = (term295 P).
Proof. exact (TRANS (@lem113935 P) (@lem113958 P)). Qed.
Lemma lem113960 (P : nat -> Prop) : (term156 P) = (term295 P).
Proof. exact (TRANS (@lem113911 P) (@lem113959 P)). Qed.
Lemma lem113961 (P : nat -> Prop) : (term161 P) = (term296 P).
Proof. exact (MK_COMB (@lem113849 P) (@lem113960 P)). Qed.
Lemma lem113963 {A : Type'} (P : A -> Prop) (Q : Prop) : (term263 A P Q) = (term264 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem113964 (P : nat -> Prop) (Q : Prop) : (term297 P Q) = (term298 P Q).
Proof. exact (@lem113963 nat P Q). Qed.
Lemma lem113965 (P : nat -> Prop) : (term299 P) = (term300 P).
Proof. exact (@lem113964 (term216 P) (term295 P)). Qed.
Lemma lem113966 (n : nat) (P : nat -> Prop) : (term301 P n) = (term215 n P).
Proof. exact (eq_refl (term301 P n)). Qed.
Lemma lem113967 (P : nat -> Prop) : (term302 P) = (term216 P).
Proof. exact (fun_ext (fun n : nat => @lem113966 n P)). Qed.
Lemma lem113968 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113969 (P : nat -> Prop) : (term303 P) = (term217 P).
Proof. exact (MK_COMB (@lem113968) (@lem113967 P)). Qed.
Lemma lem113970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem113971 (P : nat -> Prop) : (term304 P) = (term218 P).
Proof. exact (MK_COMB (@lem113970) (@lem113969 P)). Qed.
Lemma lem113972 (P : nat -> Prop) : (term295 P) = (term295 P).
Proof. exact (eq_refl (term295 P)). Qed.
Lemma lem113973 (P : nat -> Prop) : (term299 P) = (term296 P).
Proof. exact (MK_COMB (@lem113971 P) (@lem113972 P)). Qed.
Lemma lem113974 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem113975 (P : nat -> Prop) : (term305 P) = (term306 P).
Proof. exact (MK_COMB (@lem113974) (@lem113973 P)). Qed.
Lemma lem113976 (n : nat) (P : nat -> Prop) : (term301 P n) = (term215 n P).
Proof. exact (eq_refl (term301 P n)). Qed.
Lemma lem113977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem113978 (n : nat) (P : nat -> Prop) : (term307 P n) = (term308 n P).
Proof. exact (MK_COMB (@lem113977) (@lem113976 n P)). Qed.
Lemma lem113979 (P : nat -> Prop) : (term295 P) = (term295 P).
Proof. exact (eq_refl (term295 P)). Qed.
Lemma lem113980 (n : nat) (P : nat -> Prop) : (term309 n P) = (term310 n P).
Proof. exact (MK_COMB (@lem113978 n P) (@lem113979 P)). Qed.
Lemma lem113981 (P : nat -> Prop) : (term311 P) = (term312 P).
Proof. exact (fun_ext (fun n : nat => @lem113980 n P)). Qed.
Lemma lem113982 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113983 (P : nat -> Prop) : (term300 P) = (term313 P).
Proof. exact (MK_COMB (@lem113982) (@lem113981 P)). Qed.
Lemma lem113984 (P : nat -> Prop) : ((term299 P) = (term300 P)) = ((term296 P) = (term313 P)).
Proof. exact (MK_COMB (@lem113975 P) (@lem113983 P)). Qed.
Lemma lem113985 (P : nat -> Prop) : (term296 P) = (term313 P).
Proof. exact (EQ_MP (@lem113984 P) (@lem113965 P)). Qed.
Lemma lem113987 {A : Type'} (P : A -> Prop) (Q : Prop) : (term263 A P Q) = (term264 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem113988 (P : nat -> Prop) (Q : Prop) : (term297 P Q) = (term298 P Q).
Proof. exact (@lem113987 nat P Q). Qed.
Lemma lem113989 (n : nat) (P : nat -> Prop) : (term314 n P) = (term315 n P).
Proof. exact (@lem113988 (term214 n P) (term295 P)). Qed.
Lemma lem113990 (n : nat) (m : nat) (P : nat -> Prop) : (term316 n P m) = (term212 n m P).
Proof. exact (eq_refl (term316 n P m)). Qed.
Lemma lem113991 (n : nat) (P : nat -> Prop) : (term317 n P) = (term214 n P).
Proof. exact (fun_ext (fun m : nat => @lem113990 n m P)). Qed.
Lemma lem113992 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem113993 (n : nat) (P : nat -> Prop) : (term318 n P) = (term215 n P).
Proof. exact (MK_COMB (@lem113992) (@lem113991 n P)). Qed.
Lemma lem113994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem113995 (n : nat) (P : nat -> Prop) : (term319 n P) = (term308 n P).
Proof. exact (MK_COMB (@lem113994) (@lem113993 n P)). Qed.
Lemma lem113996 (P : nat -> Prop) : (term295 P) = (term295 P).
Proof. exact (eq_refl (term295 P)). Qed.
Lemma lem113997 (n : nat) (P : nat -> Prop) : (term314 n P) = (term310 n P).
Proof. exact (MK_COMB (@lem113995 n P) (@lem113996 P)). Qed.
Lemma lem113998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem113999 (n : nat) (P : nat -> Prop) : (term320 n P) = (term321 n P).
Proof. exact (MK_COMB (@lem113998) (@lem113997 n P)). Qed.
Lemma lem114000 (n : nat) (m : nat) (P : nat -> Prop) : (term316 n P m) = (term212 n m P).
Proof. exact (eq_refl (term316 n P m)). Qed.
Lemma lem114001 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem114002 (n : nat) (m : nat) (P : nat -> Prop) : (term322 n P m) = (term323 n m P).
Proof. exact (MK_COMB (@lem114001) (@lem114000 n m P)). Qed.
Lemma lem114003 (P : nat -> Prop) : (term295 P) = (term295 P).
Proof. exact (eq_refl (term295 P)). Qed.
Lemma lem114004 (n : nat) (m : nat) (P : nat -> Prop) : (term324 n m P) = (term325 n m P).
Proof. exact (MK_COMB (@lem114002 n m P) (@lem114003 P)). Qed.
Lemma lem114005 (n : nat) (P : nat -> Prop) : (term326 n P) = (term327 n P).
Proof. exact (fun_ext (fun m : nat => @lem114004 n m P)). Qed.
Lemma lem114006 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem114007 (n : nat) (P : nat -> Prop) : (term315 n P) = (term328 n P).
Proof. exact (MK_COMB (@lem114006) (@lem114005 n P)). Qed.
Lemma lem114008 (n : nat) (P : nat -> Prop) : ((term314 n P) = (term315 n P)) = ((term310 n P) = (term328 n P)).
Proof. exact (MK_COMB (@lem113999 n P) (@lem114007 n P)). Qed.
Lemma lem114009 (n : nat) (P : nat -> Prop) : (term310 n P) = (term328 n P).
Proof. exact (EQ_MP (@lem114008 n P) (@lem113989 n P)). Qed.
Lemma lem114011 {A : Type'} (P : Prop) (Q : A -> Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem114012 (P : Prop) (Q : type1002) : (term329 P Q) = (term330 P Q).
Proof. exact (@lem114011 (nat -> nat) P Q). Qed.
Lemma lem114013 (n : nat) (m : nat) (P : nat -> Prop) : (term331 n m P) = (term332 n m P).
Proof. exact (@lem114012 (term212 n m P) (term294 P)). Qed.
Lemma lem114014 (m : nat -> nat) (P : nat -> Prop) : (term333 P m) = (term293 m P).
Proof. exact (eq_refl (term333 P m)). Qed.
Lemma lem114015 (P : nat -> Prop) : (term334 P) = (term294 P).
Proof. exact (fun_ext (fun m : nat -> nat => @lem114014 m P)). Qed.
Lemma lem114016 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem114017 (P : nat -> Prop) : (term335 P) = (term295 P).
Proof. exact (MK_COMB (@lem114016) (@lem114015 P)). Qed.
Lemma lem114018 (n : nat) (m : nat) (P : nat -> Prop) : (term323 n m P) = (term323 n m P).
Proof. exact (eq_refl (term323 n m P)). Qed.
Lemma lem114019 (n : nat) (m : nat) (P : nat -> Prop) : (term331 n m P) = (term325 n m P).
Proof. exact (MK_COMB (@lem114018 n m P) (@lem114017 P)). Qed.
Lemma lem114020 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem114021 (n : nat) (m : nat) (P : nat -> Prop) : (term336 n m P) = (term337 n m P).
Proof. exact (MK_COMB (@lem114020) (@lem114019 n m P)). Qed.
Lemma lem114022 (m : nat -> nat) (P : nat -> Prop) : (term333 P m) = (term293 m P).
Proof. exact (eq_refl (term333 P m)). Qed.
Lemma lem114023 (n : nat) (m : nat) (P : nat -> Prop) : (term323 n m P) = (term323 n m P).
Proof. exact (eq_refl (term323 n m P)). Qed.
Lemma lem114024 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) : (term338 n m P m') = (term339 n m m' P).
Proof. exact (MK_COMB (@lem114023 n m P) (@lem114022 m' P)). Qed.
Lemma lem114025 (n : nat) (m : nat) (P : nat -> Prop) : (term340 n m P) = (term341 n m P).
Proof. exact (fun_ext (fun m' : nat -> nat => @lem114024 n m m' P)). Qed.
Lemma lem114026 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem114027 (n : nat) (m : nat) (P : nat -> Prop) : (term332 n m P) = (term342 n m P).
Proof. exact (MK_COMB (@lem114026) (@lem114025 n m P)). Qed.
Lemma lem114028 (n : nat) (m : nat) (P : nat -> Prop) : ((term331 n m P) = (term332 n m P)) = ((term325 n m P) = (term342 n m P)).
Proof. exact (MK_COMB (@lem114021 n m P) (@lem114027 n m P)). Qed.
Lemma lem114029 (n : nat) (m : nat) (P : nat -> Prop) : (term325 n m P) = (term342 n m P).
Proof. exact (EQ_MP (@lem114028 n m P) (@lem114013 n m P)). Qed.
Lemma lem114031 {A : Type'} (P : Prop) (Q : A -> Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem114032 (P : Prop) (Q : nat -> Prop) : (term164 P Q) = (term165 P Q).
Proof. exact (@lem114031 nat P Q). Qed.
Lemma lem114033 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) : (term343 n m m' P) = (term344 n m m' P).
Proof. exact (@lem114032 (term212 n m P) (term292 m' P)). Qed.
Lemma lem114034 (m : nat -> nat) (P : nat -> Prop) (n : nat) : (term345 m P n) = (term290 m P n).
Proof. exact (eq_refl (term345 m P n)). Qed.
Lemma lem114035 (m : nat -> nat) (P : nat -> Prop) : (term346 m P) = (term292 m P).
Proof. exact (fun_ext (fun n : nat => @lem114034 m P n)). Qed.
Lemma lem114036 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem114037 (m : nat -> nat) (P : nat -> Prop) : (term347 m P) = (term293 m P).
Proof. exact (MK_COMB (@lem114036) (@lem114035 m P)). Qed.
Lemma lem114038 (n : nat) (m : nat) (P : nat -> Prop) : (term323 n m P) = (term323 n m P).
Proof. exact (eq_refl (term323 n m P)). Qed.
Lemma lem114039 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) : (term343 n m m' P) = (term339 n m m' P).
Proof. exact (MK_COMB (@lem114038 n m P) (@lem114037 m' P)). Qed.
Lemma lem114040 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem114041 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) : (term348 n m m' P) = (term349 n m m' P).
Proof. exact (MK_COMB (@lem114040) (@lem114039 n m m' P)). Qed.
Lemma lem114042 (m : nat -> nat) (P : nat -> Prop) (n' : nat) : (term345 m P n') = (term290 m P n').
Proof. exact (eq_refl (term345 m P n')). Qed.
Lemma lem114043 (n : nat) (m : nat) (P : nat -> Prop) : (term323 n m P) = (term323 n m P).
Proof. exact (eq_refl (term323 n m P)). Qed.
Lemma lem114044 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) : (term350 n m m' P n') = (term351 n m m' P n').
Proof. exact (MK_COMB (@lem114043 n m P) (@lem114042 m' P n')). Qed.
Lemma lem114045 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) : (term352 n m m' P) = (term353 n m m' P).
Proof. exact (fun_ext (fun n' : nat => @lem114044 n m m' P n')). Qed.
Lemma lem114046 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem114047 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) : (term344 n m m' P) = (term354 n m m' P).
Proof. exact (MK_COMB (@lem114046) (@lem114045 n m m' P)). Qed.
Lemma lem114048 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) : ((term343 n m m' P) = (term344 n m m' P)) = ((term339 n m m' P) = (term354 n m m' P)).
Proof. exact (MK_COMB (@lem114041 n m m' P) (@lem114047 n m m' P)). Qed.
Lemma lem114049 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) : (term339 n m m' P) = (term354 n m m' P).
Proof. exact (EQ_MP (@lem114048 n m m' P) (@lem114033 n m m' P)). Qed.
Lemma lem114050 (n : nat) (m : nat) (P : nat -> Prop) : (term341 n m P) = (term355 n m P).
Proof. exact (fun_ext (fun m' : nat -> nat => @lem114049 n m m' P)). Qed.
Lemma lem114051 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem114052 (n : nat) (m : nat) (P : nat -> Prop) : (term342 n m P) = (term356 n m P).
Proof. exact (MK_COMB (@lem114051) (@lem114050 n m P)). Qed.
Lemma lem114053 (n : nat) (m : nat) (P : nat -> Prop) : (term325 n m P) = (term356 n m P).
Proof. exact (TRANS (@lem114029 n m P) (@lem114052 n m P)). Qed.
Lemma lem114054 (n : nat) (P : nat -> Prop) : (term327 n P) = (term357 n P).
Proof. exact (fun_ext (fun m : nat => @lem114053 n m P)). Qed.
Lemma lem114055 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem114056 (n : nat) (P : nat -> Prop) : (term328 n P) = (term358 n P).
Proof. exact (MK_COMB (@lem114055) (@lem114054 n P)). Qed.
Lemma lem114057 (n : nat) (P : nat -> Prop) : (term310 n P) = (term358 n P).
Proof. exact (TRANS (@lem114009 n P) (@lem114056 n P)). Qed.
Lemma lem114058 (P : nat -> Prop) : (term312 P) = (term359 P).
Proof. exact (fun_ext (fun n : nat => @lem114057 n P)). Qed.
Lemma lem114059 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem114060 (P : nat -> Prop) : (term313 P) = (term360 P).
Proof. exact (MK_COMB (@lem114059) (@lem114058 P)). Qed.
Lemma lem114061 (P : nat -> Prop) : (term296 P) = (term360 P).
Proof. exact (TRANS (@lem113985 P) (@lem114060 P)). Qed.
Lemma lem114063 (P : nat -> Prop) : (term161 P) = (term360 P).
Proof. exact (TRANS (@lem113961 P) (@lem114061 P)). Qed.
Lemma lem114064 (P : nat -> Prop) : (term68 P) = (term360 P).
Proof. exact (TRANS (@lem113518 P) (@lem114063 P)). Qed.
Lemma lem114065 (P : nat -> Prop) (h1 : term68 P) : term360 P.
Proof. exact (EQ_MP (@lem114064 P) (@lem113406 P h1)). Qed.
Lemma lem114066 (m : nat) : (term76 m) = (term76 m).
Proof. exact (eq_refl (term76 m)). Qed.
Lemma lem114067 : term78 = term78.
Proof. exact (fun_ext (fun m : nat => @lem114066 m)). Qed.
Lemma lem114068 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114069 : term79 = term79.
Proof. exact (MK_COMB (@lem114068) (@lem114067)). Qed.
Lemma lem114080 (m : nat) (n : nat) : (term361 m n) = (term362 m n).
Proof. exact (@lem17160 (m = n) (Peano.lt m n)). Qed.
Lemma lem114086 (m : nat) (n : nat) : (term363 m n) = (term363 m n).
Proof. exact (eq_refl (term363 m n)). Qed.
Lemma lem114088 (m : nat) (n : nat) : (term364 m n) = (term364 m n).
Proof. exact (eq_refl (term364 m n)). Qed.
Lemma lem114089 (m : nat) (n : nat) : (term365 m n) = (term366 m n).
Proof. exact (MK_COMB (@lem114088 m n) (@lem114080 m n)). Qed.
Lemma lem114090 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem114091 (m : nat) (n : nat) : (term367 m n) = (term368 m n).
Proof. exact (MK_COMB (@lem114090) (@lem114089 m n)). Qed.
Lemma lem114092 (m : nat) (n : nat) : (term369 m n) = (term370 m n).
Proof. exact (MK_COMB (@lem114091 m n) (@lem114086 m n)). Qed.
Lemma lem114093 (m : nat) (n : nat) : ((term4 m n) = (term5 m n)) = (term369 m n).
Proof. exact (@lem17784 (term4 m n) (term5 m n)). Qed.
Lemma lem114094 (m : nat) (n : nat) : ((term4 m n) = (term5 m n)) = (term370 m n).
Proof. exact (TRANS (@lem114093 m n) (@lem114092 m n)). Qed.
Lemma lem114095 (m : nat) : (term90 m) = (term371 m).
Proof. exact (fun_ext (fun n : nat => @lem114094 m n)). Qed.
Lemma lem114096 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114097 (m : nat) : (term2 m) = (term372 m).
Proof. exact (MK_COMB (@lem114096) (@lem114095 m)). Qed.
Lemma lem114098 : term91 = term373.
Proof. exact (fun_ext (fun m : nat => @lem114097 m)). Qed.
Lemma lem114099 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114100 : term0 = term374.
Proof. exact (MK_COMB (@lem114099) (@lem114098)). Qed.
Lemma lem114101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem114102 : term81 = term81.
Proof. exact (MK_COMB (@lem114101) (@lem114069)). Qed.
Lemma lem114103 : term82 = term375.
Proof. exact (MK_COMB (@lem114102) (@lem114100)). Qed.
Lemma lem114113 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term376 A P Q) = (term377 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem114114 (P : nat -> Prop) (Q : nat -> Prop) : (term378 P Q) = (term379 P Q).
Proof. exact (@lem114113 nat P Q). Qed.
Lemma lem114115 (m : nat) : (term380 m) = (term381 m).
Proof. exact (@lem114114 (term382 m) (term383 m)). Qed.
Lemma lem114116 (m : nat) (n : nat) : (term384 m n) = (term366 m n).
Proof. exact (eq_refl (term384 m n)). Qed.
Lemma lem114117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem114118 (m : nat) (n : nat) : (term385 m n) = (term368 m n).
Proof. exact (MK_COMB (@lem114117) (@lem114116 m n)). Qed.
Lemma lem114119 (m : nat) (n : nat) : (term386 m n) = (term363 m n).
Proof. exact (eq_refl (term386 m n)). Qed.
Lemma lem114120 (m : nat) (n : nat) : (term387 m n) = (term370 m n).
Proof. exact (MK_COMB (@lem114118 m n) (@lem114119 m n)). Qed.
Lemma lem114121 (m : nat) : (term388 m) = (term371 m).
Proof. exact (fun_ext (fun n : nat => @lem114120 m n)). Qed.
Lemma lem114122 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114123 (m : nat) : (term380 m) = (term372 m).
Proof. exact (MK_COMB (@lem114122) (@lem114121 m)). Qed.
Lemma lem114124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem114125 (m : nat) : (term389 m) = (term390 m).
Proof. exact (MK_COMB (@lem114124) (@lem114123 m)). Qed.
Lemma lem114126 (m : nat) (n : nat) : (term384 m n) = (term366 m n).
Proof. exact (eq_refl (term384 m n)). Qed.
Lemma lem114127 (m : nat) : (term391 m) = (term382 m).
Proof. exact (fun_ext (fun n : nat => @lem114126 m n)). Qed.
Lemma lem114128 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114129 (m : nat) : (term392 m) = (term393 m).
Proof. exact (MK_COMB (@lem114128) (@lem114127 m)). Qed.
Lemma lem114130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem114131 (m : nat) : (term394 m) = (term395 m).
Proof. exact (MK_COMB (@lem114130) (@lem114129 m)). Qed.
Lemma lem114132 (m : nat) (n : nat) : (term386 m n) = (term363 m n).
Proof. exact (eq_refl (term386 m n)). Qed.
Lemma lem114133 (m : nat) : (term396 m) = (term383 m).
Proof. exact (fun_ext (fun n : nat => @lem114132 m n)). Qed.
Lemma lem114134 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114135 (m : nat) : (term397 m) = (term398 m).
Proof. exact (MK_COMB (@lem114134) (@lem114133 m)). Qed.
Lemma lem114136 (m : nat) : (term381 m) = (term399 m).
Proof. exact (MK_COMB (@lem114131 m) (@lem114135 m)). Qed.
Lemma lem114137 (m : nat) : ((term380 m) = (term381 m)) = ((term372 m) = (term399 m)).
Proof. exact (MK_COMB (@lem114125 m) (@lem114136 m)). Qed.
Lemma lem114138 (m : nat) : (term372 m) = (term399 m).
Proof. exact (EQ_MP (@lem114137 m) (@lem114115 m)). Qed.
Lemma lem114235 : term373 = term400.
Proof. exact (fun_ext (fun m : nat => @lem114138 m)). Qed.
Lemma lem114236 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114237 : term374 = term401.
Proof. exact (MK_COMB (@lem114236) (@lem114235)). Qed.
Lemma lem114239 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term376 A P Q) = (term377 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem114240 (P : nat -> Prop) (Q : nat -> Prop) : (term378 P Q) = (term379 P Q).
Proof. exact (@lem114239 nat P Q). Qed.
Lemma lem114241 : term402 = term403.
Proof. exact (@lem114240 term404 term405). Qed.
Lemma lem114242 (m : nat) : (term406 m) = (term393 m).
Proof. exact (eq_refl (term406 m)). Qed.
Lemma lem114243 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem114244 (m : nat) : (term407 m) = (term395 m).
Proof. exact (MK_COMB (@lem114243) (@lem114242 m)). Qed.
Lemma lem114245 (m : nat) : (term408 m) = (term398 m).
Proof. exact (eq_refl (term408 m)). Qed.
Lemma lem114246 (m : nat) : (term409 m) = (term399 m).
Proof. exact (MK_COMB (@lem114244 m) (@lem114245 m)). Qed.
Lemma lem114247 : term410 = term400.
Proof. exact (fun_ext (fun m : nat => @lem114246 m)). Qed.
Lemma lem114248 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114249 : term402 = term401.
Proof. exact (MK_COMB (@lem114248) (@lem114247)). Qed.
Lemma lem114250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem114251 : term411 = term412.
Proof. exact (MK_COMB (@lem114250) (@lem114249)). Qed.
Lemma lem114252 (m : nat) : (term406 m) = (term393 m).
Proof. exact (eq_refl (term406 m)). Qed.
Lemma lem114253 : term413 = term404.
Proof. exact (fun_ext (fun m : nat => @lem114252 m)). Qed.
Lemma lem114254 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114255 : term414 = term415.
Proof. exact (MK_COMB (@lem114254) (@lem114253)). Qed.
Lemma lem114256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem114257 : term416 = term417.
Proof. exact (MK_COMB (@lem114256) (@lem114255)). Qed.
Lemma lem114258 (m : nat) : (term408 m) = (term398 m).
Proof. exact (eq_refl (term408 m)). Qed.
Lemma lem114259 : term418 = term405.
Proof. exact (fun_ext (fun m : nat => @lem114258 m)). Qed.
Lemma lem114260 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114261 : term419 = term420.
Proof. exact (MK_COMB (@lem114260) (@lem114259)). Qed.
Lemma lem114262 : term403 = term421.
Proof. exact (MK_COMB (@lem114257) (@lem114261)). Qed.
Lemma lem114263 : (term402 = term403) = (term401 = term421).
Proof. exact (MK_COMB (@lem114251) (@lem114262)). Qed.
Lemma lem114264 : term401 = term421.
Proof. exact (EQ_MP (@lem114263) (@lem114241)). Qed.
Lemma lem114369 : term374 = term421.
Proof. exact (TRANS (@lem114237) (@lem114264)). Qed.
Lemma lem114370 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem114373 : term375 = term422.
Proof. exact (MK_COMB (@lem114370) (@lem114369)). Qed.
Lemma lem114374 : term82 = term422.
Proof. exact (TRANS (@lem114103) (@lem114373)). Qed.
Lemma lem114375 (h1 : term82) : term422.
Proof. exact (EQ_MP (@lem114374) (@lem113407 h1)). Qed.
Lemma lem114376 (n : nat) (P : nat -> Prop) (h1 : term358 n P) : term358 n P.
Proof. exact (h1). Qed.
Lemma lem114377 (n : nat) (m : nat) (P : nat -> Prop) (h1 : term356 n m P) : term356 n m P.
Proof. exact (h1). Qed.
Lemma lem114378 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (h1 : term354 n m m' P) : term354 n m m' P.
Proof. exact (h1). Qed.
Lemma lem114379 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term351 n m m' P n'.
Proof. exact (h1). Qed.
Lemma lem114404 (m : nat) (n : nat) : (term363 m n) = (term363 m n).
Proof. exact (eq_refl (term363 m n)). Qed.
Lemma lem114405 (m : nat) : (term383 m) = (term383 m).
Proof. exact (fun_ext (fun n : nat => @lem114404 m n)). Qed.
Lemma lem114406 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114407 (m : nat) : (term398 m) = (term398 m).
Proof. exact (MK_COMB (@lem114406) (@lem114405 m)). Qed.
Lemma lem114408 : term405 = term405.
Proof. exact (fun_ext (fun m : nat => @lem114407 m)). Qed.
Lemma lem114409 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114410 : term420 = term420.
Proof. exact (MK_COMB (@lem114409) (@lem114408)). Qed.
Lemma lem114437 (m : nat) (n : nat) : (term366 m n) = (term366 m n).
Proof. exact (eq_refl (term366 m n)). Qed.
Lemma lem114438 (m : nat) : (term382 m) = (term382 m).
Proof. exact (fun_ext (fun n : nat => @lem114437 m n)). Qed.
Lemma lem114439 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114440 (m : nat) : (term393 m) = (term393 m).
Proof. exact (MK_COMB (@lem114439) (@lem114438 m)). Qed.
Lemma lem114441 : term404 = term404.
Proof. exact (fun_ext (fun m : nat => @lem114440 m)). Qed.
Lemma lem114442 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114443 : term415 = term415.
Proof. exact (MK_COMB (@lem114442) (@lem114441)). Qed.
Lemma lem114444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem114445 : term417 = term417.
Proof. exact (MK_COMB (@lem114444) (@lem114443)). Qed.
Lemma lem114446 : term421 = term421.
Proof. exact (MK_COMB (@lem114445) (@lem114410)). Qed.
Lemma lem114455 (m : nat) : (term76 m) = (term76 m).
Proof. exact (eq_refl (term76 m)). Qed.
Lemma lem114456 : term78 = term78.
Proof. exact (fun_ext (fun m : nat => @lem114455 m)). Qed.
Lemma lem114457 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114458 : term79 = term79.
Proof. exact (MK_COMB (@lem114457) (@lem114456)). Qed.
Lemma lem114459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem114460 : term81 = term81.
Proof. exact (MK_COMB (@lem114459) (@lem114458)). Qed.
Lemma lem114461 : term422 = term422.
Proof. exact (MK_COMB (@lem114460) (@lem114446)). Qed.
Lemma lem114462 (h1 : term82) : term422.
Proof. exact (EQ_MP (@lem114461) (@lem114375 h1)). Qed.
Lemma lem114467 (P : nat -> Prop) (n' : nat) : (term150 P n') = (term150 P n').
Proof. exact (eq_refl (term150 P n')). Qed.
Lemma lem114490 (m' : nat -> nat) (P : nat -> Prop) (n : nat) : (term253 m' P n) = (term253 m' P n).
Proof. exact (eq_refl (term253 m' P n)). Qed.
Lemma lem114491 (m' : nat -> nat) (P : nat -> Prop) : (term255 m' P) = (term255 m' P).
Proof. exact (fun_ext (fun n : nat => @lem114490 m' P n)). Qed.
Lemma lem114492 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114493 (m' : nat -> nat) (P : nat -> Prop) : (term257 m' P) = (term257 m' P).
Proof. exact (MK_COMB (@lem114492) (@lem114491 m' P)). Qed.
Lemma lem114494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem114495 (m' : nat -> nat) (P : nat -> Prop) : (term276 m' P) = (term276 m' P).
Proof. exact (MK_COMB (@lem114494) (@lem114493 m' P)). Qed.
Lemma lem114496 (m' : nat -> nat) (P : nat -> Prop) (n' : nat) : (term290 m' P n') = (term290 m' P n').
Proof. exact (MK_COMB (@lem114495 m' P) (@lem114467 P n')). Qed.
Lemma lem114509 (n : nat) (P : nat -> Prop) (m : nat) : (term100 n P m) = (term100 n P m).
Proof. exact (eq_refl (term100 n P m)). Qed.
Lemma lem114510 (n : nat) (P : nat -> Prop) : (term101 n P) = (term101 n P).
Proof. exact (fun_ext (fun m : nat => @lem114509 n P m)). Qed.
Lemma lem114511 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114512 (n : nat) (P : nat -> Prop) : (term102 n P) = (term102 n P).
Proof. exact (MK_COMB (@lem114511) (@lem114510 n P)). Qed.
Lemma lem114513 (P : nat -> Prop) : (term126 P) = (term126 P).
Proof. exact (fun_ext (fun n : nat => @lem114512 n P)). Qed.
Lemma lem114514 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114515 (P : nat -> Prop) : (term127 P) = (term127 P).
Proof. exact (MK_COMB (@lem114514) (@lem114513 P)). Qed.
Lemma lem114536 (n : nat) (P : nat -> Prop) (m : nat) : (term104 n P m) = (term104 n P m).
Proof. exact (eq_refl (term104 n P m)). Qed.
Lemma lem114549 (n : nat) (P : nat -> Prop) (m : nat) : (term100 n P m) = (term100 n P m).
Proof. exact (eq_refl (term100 n P m)). Qed.
Lemma lem114550 (n : nat) (P : nat -> Prop) : (term101 n P) = (term101 n P).
Proof. exact (fun_ext (fun m : nat => @lem114549 n P m)). Qed.
Lemma lem114551 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114552 (n : nat) (P : nat -> Prop) : (term102 n P) = (term102 n P).
Proof. exact (MK_COMB (@lem114551) (@lem114550 n P)). Qed.
Lemma lem114553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem114554 (n : nat) (P : nat -> Prop) : (term115 n P) = (term115 n P).
Proof. exact (MK_COMB (@lem114553) (@lem114552 n P)). Qed.
Lemma lem114555 (n : nat) (P : nat -> Prop) (m : nat) : (term174 n P m) = (term174 n P m).
Proof. exact (MK_COMB (@lem114554 n P) (@lem114536 n P m)). Qed.
Lemma lem114556 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem114557 (n : nat) (P : nat -> Prop) (m : nat) : (term210 n P m) = (term210 n P m).
Proof. exact (MK_COMB (@lem114556) (@lem114555 n P m)). Qed.
Lemma lem114558 (n : nat) (m : nat) (P : nat -> Prop) : (term212 n m P) = (term212 n m P).
Proof. exact (MK_COMB (@lem114557 n P m) (@lem114515 P)). Qed.
Lemma lem114559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem114560 (n : nat) (m : nat) (P : nat -> Prop) : (term323 n m P) = (term323 n m P).
Proof. exact (MK_COMB (@lem114559) (@lem114558 n m P)). Qed.
Lemma lem114561 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) : (term351 n m m' P n') = (term351 n m m' P n').
Proof. exact (MK_COMB (@lem114560 n m P) (@lem114496 m' P n')). Qed.
Lemma lem114562 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term351 n m m' P n'.
Proof. exact (EQ_MP (@lem114561 n m m' P n') (@lem114379 n m m' P n' h1)). Qed.
Lemma lem114563 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term290 m' P n'.
Proof. exact (proj2 (@lem114562 n m m' P n' h1)). Qed.
Lemma lem114564 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term212 n m P.
Proof. exact (proj1 (@lem114562 n m m' P n' h1)). Qed.
Lemma lem114566 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term257 m' P.
Proof. exact (proj1 (@lem114563 n m m' P n' h1)). Qed.
Lemma lem114567 (h1 : term82) : term421.
Proof. exact (proj2 (@lem114462 h1)). Qed.
Lemma lem114570 (h1 : term82) : term415.
Proof. exact (proj1 (@lem114567 h1)). Qed.
Lemma lem114571 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term174 n P m.
Proof. exact (h1). Qed.
Lemma lem114572 (P : nat -> Prop) (h1 : term127 P) : term127 P.
Proof. exact (h1). Qed.
Lemma lem114573 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term104 n P m.
Proof. exact (proj2 (@lem114571 n P m h1)). Qed.
Lemma lem114574 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term102 n P.
Proof. exact (proj1 (@lem114571 n P m h1)). Qed.
Lemma lem114576 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term5 m n.
Proof. exact (proj1 (@lem114573 n P m h1)). Qed.
Lemma lem114596 (m' : nat -> nat) (P : nat -> Prop) (n : nat) : (term253 m' P n) = (term423 m' P n).
Proof. exact (@lem19699 (term424 m' n) (term425 P m' n) (P n)). Qed.
Lemma lem114597 (m' : nat -> nat) (P : nat -> Prop) : (term255 m' P) = (term426 m' P).
Proof. exact (fun_ext (fun n : nat => @lem114596 m' P n)). Qed.
Lemma lem114598 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114600 (m' : nat -> nat) (P : nat -> Prop) : (term257 m' P) = (term427 m' P).
Proof. exact (MK_COMB (@lem114598) (@lem114597 m' P)). Qed.
Lemma lem114601 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term427 m' P.
Proof. exact (EQ_MP (@lem114600 m' P) (@lem114566 n m m' P n' h1)). Qed.
Lemma lem114668 (n : nat) (P : nat -> Prop) (m : nat) : (term100 n P m) = (term100 n P m).
Proof. exact (eq_refl (term100 n P m)). Qed.
Lemma lem114669 (n : nat) (P : nat -> Prop) : (term101 n P) = (term101 n P).
Proof. exact (fun_ext (fun m : nat => @lem114668 n P m)). Qed.
Lemma lem114670 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114672 (n : nat) (P : nat -> Prop) : (term102 n P) = (term102 n P).
Proof. exact (MK_COMB (@lem114670) (@lem114669 n P)). Qed.
Lemma lem114673 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term102 n P.
Proof. exact (EQ_MP (@lem114672 n P) (@lem114574 n P m h1)). Qed.
Lemma lem114681 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem114771 (n : nat) (P : nat -> Prop) (m : nat) : (term100 n P m) = (term100 n P m).
Proof. exact (eq_refl (term100 n P m)). Qed.
Lemma lem114772 (n : nat) (P : nat -> Prop) : (term101 n P) = (term101 n P).
Proof. exact (fun_ext (fun m : nat => @lem114771 n P m)). Qed.
Lemma lem114773 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114775 (n : nat) (P : nat -> Prop) : (term102 n P) = (term102 n P).
Proof. exact (MK_COMB (@lem114773) (@lem114772 n P)). Qed.
Lemma lem114776 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term102 n P.
Proof. exact (EQ_MP (@lem114775 n P) (@lem114574 n P m h1)). Qed.
Lemma lem114784 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem114836 (m : nat) (n : nat) : (term366 m n) = (term428 m n).
Proof. exact (@lem19490 (term429 m n) (term4 m n) (term430 m n)). Qed.
Lemma lem114837 (m : nat) : (term382 m) = (term431 m).
Proof. exact (fun_ext (fun n : nat => @lem114836 m n)). Qed.
Lemma lem114838 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114839 (m : nat) : (term393 m) = (term432 m).
Proof. exact (MK_COMB (@lem114838) (@lem114837 m)). Qed.
Lemma lem114840 : term404 = term433.
Proof. exact (fun_ext (fun m : nat => @lem114839 m)). Qed.
Lemma lem114841 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114843 : term415 = term434.
Proof. exact (MK_COMB (@lem114841) (@lem114840)). Qed.
Lemma lem114844 (h1 : term82) : term434.
Proof. exact (EQ_MP (@lem114843) (@lem114570 h1)). Qed.
Lemma lem114874 (n : nat) (P : nat -> Prop) (m : nat) : (term100 n P m) = (term100 n P m).
Proof. exact (eq_refl (term100 n P m)). Qed.
Lemma lem114875 (n : nat) (P : nat -> Prop) : (term101 n P) = (term101 n P).
Proof. exact (fun_ext (fun m : nat => @lem114874 n P m)). Qed.
Lemma lem114876 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114877 (n : nat) (P : nat -> Prop) : (term102 n P) = (term102 n P).
Proof. exact (MK_COMB (@lem114876) (@lem114875 n P)). Qed.
Lemma lem114878 (P : nat -> Prop) : (term126 P) = (term126 P).
Proof. exact (fun_ext (fun n : nat => @lem114877 n P)). Qed.
Lemma lem114879 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem114881 (P : nat -> Prop) : (term127 P) = (term127 P).
Proof. exact (MK_COMB (@lem114879) (@lem114878 P)). Qed.
Lemma lem114882 (P : nat -> Prop) (h1 : term127 P) : term127 P.
Proof. exact (EQ_MP (@lem114881 P) (@lem114572 P h1)). Qed.
Lemma lem114883 (_2390 : nat) (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term435 m' P _2390.
Proof. exact (@lem114601 n m m' P n' h1 _2390). Qed.
Lemma lem114884 (m' : nat -> nat) (P : nat -> Prop) (_2390 : nat) : (term435 m' P _2390) = (term423 m' P _2390).
Proof. exact (eq_refl (term435 m' P _2390)). Qed.
Lemma lem114885 (_2390 : nat) (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term423 m' P _2390.
Proof. exact (EQ_MP (@lem114884 m' P _2390) (@lem114883 _2390 n m m' P n' h1)). Qed.
Lemma lem114901 (_2396 : nat) (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term436 n P _2396.
Proof. exact (@lem114673 n P m h1 _2396). Qed.
Lemma lem114902 (n : nat) (P : nat -> Prop) (_2396 : nat) : (term436 n P _2396) = (term100 n P _2396).
Proof. exact (eq_refl (term436 n P _2396)). Qed.
Lemma lem114922 (_2403 : nat) (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term436 n P _2403.
Proof. exact (@lem114776 n P m h1 _2403). Qed.
Lemma lem114923 (n : nat) (P : nat -> Prop) (_2403 : nat) : (term436 n P _2403) = (term100 n P _2403).
Proof. exact (eq_refl (term436 n P _2403)). Qed.
Lemma lem114931 (_2406 : nat) (h1 : term82) : term437 _2406.
Proof. exact (@lem114844 h1 _2406). Qed.
Lemma lem114932 (_2406 : nat) : (term437 _2406) = (term432 _2406).
Proof. exact (eq_refl (term437 _2406)). Qed.
Lemma lem114933 (_2406 : nat) (h1 : term82) : term432 _2406.
Proof. exact (EQ_MP (@lem114932 _2406) (@lem114931 _2406 h1)). Qed.
Lemma lem114934 (_2406 : nat) (_2407 : nat) (h1 : term82) : term438 _2406 _2407.
Proof. exact (@lem114933 _2406 h1 _2407). Qed.
Lemma lem114935 (_2406 : nat) (_2407 : nat) : (term438 _2406 _2407) = (term428 _2406 _2407).
Proof. exact (eq_refl (term438 _2406 _2407)). Qed.
Lemma lem114936 (_2406 : nat) (_2407 : nat) (h1 : term82) : term428 _2406 _2407.
Proof. exact (EQ_MP (@lem114935 _2406 _2407) (@lem114934 _2406 _2407 h1)). Qed.
Lemma lem114943 (_2410 : nat) (P : nat -> Prop) (h1 : term127 P) : term439 P _2410.
Proof. exact (@lem114882 P h1 _2410). Qed.
Lemma lem114944 (_2410 : nat) (P : nat -> Prop) : (term439 P _2410) = (term102 _2410 P).
Proof. exact (eq_refl (term439 P _2410)). Qed.
Lemma lem114945 (_2410 : nat) (P : nat -> Prop) (h1 : term127 P) : term102 _2410 P.
Proof. exact (EQ_MP (@lem114944 _2410 P) (@lem114943 _2410 P h1)). Qed.
Lemma lem114946 (_2410 : nat) (_2411 : nat) (P : nat -> Prop) (h1 : term127 P) : term436 _2410 P _2411.
Proof. exact (@lem114945 _2410 P h1 _2411). Qed.
Lemma lem114947 (_2410 : nat) (P : nat -> Prop) (_2411 : nat) : (term436 _2410 P _2411) = (term100 _2410 P _2411).
Proof. exact (eq_refl (term436 _2410 P _2411)). Qed.
Lemma lem114982 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term150 P m.
Proof. exact (proj2 (@lem114573 n P m h1)). Qed.
Lemma lem114984 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem115028 (_2403 : nat) (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term100 n P _2403.
Proof. exact (EQ_MP (@lem114923 n P _2403) (@lem114922 _2403 n P m h1)). Qed.
Lemma lem115030 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term150 P m.
Proof. exact (proj2 (@lem114573 n P m h1)). Qed.
Lemma lem115032 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem115058 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term150 P n'.
Proof. exact (proj2 (@lem114563 n m m' P n' h1)). Qed.
Lemma lem115076 (_2410 : nat) (_2411 : nat) (P : nat -> Prop) (h1 : term127 P) : term100 _2410 P _2411.
Proof. exact (EQ_MP (@lem114947 _2410 P _2411) (@lem114946 _2410 _2411 P h1)). Qed.
Lemma lem115082 (_2406 : nat) (_2407 : nat) (h1 : term82) : term440 _2406 _2407.
Proof. exact (proj1 (@lem114936 _2406 _2407 h1)). Qed.
Lemma lem115170 (_2396 : nat) (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term100 n P _2396.
Proof. exact (EQ_MP (@lem114902 n P _2396) (@lem114901 _2396 n P m h1)). Qed.
Lemma lem115171 (P : nat -> Prop) : (term152 P) = (term152 P).
Proof. exact (eq_refl (term152 P)). Qed.
Lemma lem115172 (P : nat -> Prop) (m : nat) (n : nat) (h1 : m = n) : (term284 P m) = (term284 P n).
Proof. exact (MK_COMB (@lem115171 P) (@lem114984 m n h1)). Qed.
Lemma lem115173 (P : nat -> Prop) (n : nat) : (term284 P n) = (term150 P n).
Proof. exact (eq_refl (term284 P n)). Qed.
Lemma lem115174 (P : nat -> Prop) (m : nat) : (term441 P m) = (term441 P m).
Proof. exact (eq_refl (term441 P m)). Qed.
Lemma lem115175 (m : nat) (P : nat -> Prop) (n : nat) : ((term284 P m) = (term284 P n)) = ((term284 P m) = (term150 P n)).
Proof. exact (MK_COMB (@lem115174 P m) (@lem115173 P n)). Qed.
Lemma lem115176 (P : nat -> Prop) (m : nat) : (term284 P m) = (term150 P m).
Proof. exact (eq_refl (term284 P m)). Qed.
Lemma lem115177 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem115178 (P : nat -> Prop) (m : nat) : (term441 P m) = (term442 P m).
Proof. exact (MK_COMB (@lem115177) (@lem115176 P m)). Qed.
Lemma lem115179 (P : nat -> Prop) (n : nat) : (term150 P n) = (term150 P n).
Proof. exact (eq_refl (term150 P n)). Qed.
Lemma lem115180 (m : nat) (P : nat -> Prop) (n : nat) : ((term284 P m) = (term150 P n)) = ((term150 P m) = (term150 P n)).
Proof. exact (MK_COMB (@lem115178 P m) (@lem115179 P n)). Qed.
Lemma lem115181 (m : nat) (P : nat -> Prop) (n : nat) : ((term284 P m) = (term284 P n)) = ((term150 P m) = (term150 P n)).
Proof. exact (TRANS (@lem115175 m P n) (@lem115180 m P n)). Qed.
Lemma lem115182 (P : nat -> Prop) (m : nat) (n : nat) (h1 : m = n) : (term150 P m) = (term150 P n).
Proof. exact (EQ_MP (@lem115181 m P n) (@lem115172 P m n h1)). Qed.
Lemma lem115183 (P : nat -> Prop) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : m = n) : term150 P n.
Proof. exact (EQ_MP (@lem115182 P m n h2) (@lem114982 n P m h1)). Qed.
Lemma lem115225 (_2390 : nat) (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term443 m' P _2390.
Proof. exact (proj1 (@lem114885 _2390 n m m' P n' h1)). Qed.
Lemma lem115239 (_2390 : nat) (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term444 m' P _2390.
Proof. exact (proj2 (@lem114885 _2390 n m m' P n' h1)). Qed.
Lemma lem115299 (P : nat -> Prop) (n : nat) (h1 : term150 P n) : term150 P n.
Proof. exact (h1). Qed.
Lemma lem115300 (P : nat -> Prop) (n : nat) (h1 : term150 P n) : term445 P n.
Proof. exact (fun h0 : P n => @lem115299 P n h1). Qed.
Lemma lem115302 (p : Prop) : (term446 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem115303 (P : nat -> Prop) (n : nat) : (term445 P n) = (term150 P n).
Proof. exact (@lem115302 (P n)). Qed.
Lemma lem115304 (P : nat -> Prop) (n : nat) (h1 : term150 P n) : term150 P n.
Proof. exact (EQ_MP (@lem115303 P n) (@lem115300 P n h1)). Qed.
Lemma lem115306 (b : Prop) (a : Prop) : (a \/ b) = (term447 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem115309 (P : nat -> Prop) (m' : nat -> nat) (_2390 : nat) : (term443 m' P _2390) = (term448 P m' _2390).
Proof. exact (@lem115306 (P _2390) (term424 m' _2390)). Qed.
Lemma lem115312 (_2390 : nat) (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term448 P m' _2390.
Proof. exact (EQ_MP (@lem115309 P m' _2390) (@lem115225 _2390 n m m' P n' h1)). Qed.
Lemma lem115313 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term448 P m' n.
Proof. exact (@lem115312 n n m m' P n' h1). Qed.
Lemma lem115316 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term150 P n) (h2 : term351 n m m' P n') : term424 m' n.
Proof. exact (@lem115313 n m m' P n' h2 (@lem115304 P n h1)). Qed.
Lemma lem115317 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term150 P n) (h2 : term351 n m m' P n') : term449 m' n.
Proof. exact (fun h0 : term450 m' n => @lem115316 n m m' P n' h1 h2). Qed.
Lemma lem115319 (p : Prop) : (term451 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem115320 (m' : nat -> nat) (n : nat) : (term449 m' n) = (term424 m' n).
Proof. exact (@lem115319 (term424 m' n)). Qed.
Lemma lem115321 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term150 P n) (h2 : term351 n m m' P n') : term424 m' n.
Proof. exact (EQ_MP (@lem115320 m' n) (@lem115317 n m m' P n' h1 h2)). Qed.
Lemma lem115327 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem115328 (P : nat -> Prop) (_2396 : nat) (n : nat) : (term100 n P _2396) = (term452 P _2396 n).
Proof. exact (@lem115327 (P _2396) (term430 _2396 n)). Qed.
Lemma lem115334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem115335 (P : nat -> Prop) (_2396 : nat) (n : nat) : (term453 n P _2396) = (term454 P _2396 n).
Proof. exact (MK_COMB (@lem115334) (@lem115328 P _2396 n)). Qed.
Lemma lem115341 (P : nat -> Prop) (_2396 : nat) (n : nat) : (term452 P _2396 n) = (term452 P _2396 n).
Proof. exact (eq_refl (term452 P _2396 n)). Qed.
Lemma lem115342 (P : nat -> Prop) (_2396 : nat) (n : nat) : ((term100 n P _2396) = (term452 P _2396 n)) = ((term452 P _2396 n) = (term452 P _2396 n)).
Proof. exact (MK_COMB (@lem115335 P _2396 n) (@lem115341 P _2396 n)). Qed.
Lemma lem115344 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem115345 (x : Prop) : (x = x) = True.
Proof. exact (@lem115344 Prop x). Qed.
Lemma lem115346 (P : nat -> Prop) (_2396 : nat) (n : nat) : ((term452 P _2396 n) = (term452 P _2396 n)) = True.
Proof. exact (@lem115345 (term452 P _2396 n)). Qed.
Lemma lem115347 (P : nat -> Prop) (_2396 : nat) (n : nat) : ((term100 n P _2396) = (term452 P _2396 n)) = True.
Proof. exact (TRANS (@lem115342 P _2396 n) (@lem115346 P _2396 n)). Qed.
Lemma lem115348 (P : nat -> Prop) (_2396 : nat) (n : nat) : True = ((term100 n P _2396) = (term452 P _2396 n)).
Proof. exact (SYM (@lem115347 P _2396 n)). Qed.
Lemma lem115349 (P : nat -> Prop) (_2396 : nat) (n : nat) : (term100 n P _2396) = (term452 P _2396 n).
Proof. exact (EQ_MP (@lem115348 P _2396 n) (@lem0)). Qed.
Lemma lem115350 (_2396 : nat) (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term452 P _2396 n.
Proof. exact (EQ_MP (@lem115349 P _2396 n) (@lem115170 _2396 n P m h1)). Qed.
Lemma lem115352 (b : Prop) (a : Prop) : (a \/ b) = (term447 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem115353 (n : nat) (P : nat -> Prop) (_2396 : nat) : (term452 P _2396 n) = (term455 n P _2396).
Proof. exact (@lem115352 (term430 _2396 n) (P _2396)). Qed.
Lemma lem115355 (a : Prop) : (term456 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem115356 (_2396 : nat) (n : nat) : (term457 _2396 n) = (Peano.lt _2396 n).
Proof. exact (@lem115355 (Peano.lt _2396 n)). Qed.
Lemma lem115357 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem115358 (_2396 : nat) (n : nat) : (term458 _2396 n) = (term459 _2396 n).
Proof. exact (MK_COMB (@lem115357) (@lem115356 _2396 n)). Qed.
Lemma lem115359 (P : nat -> Prop) (_2396 : nat) : (P _2396) = (P _2396).
Proof. exact (eq_refl (P _2396)). Qed.
Lemma lem115360 (n : nat) (P : nat -> Prop) (_2396 : nat) : (term455 n P _2396) = (term94 n P _2396).
Proof. exact (MK_COMB (@lem115358 _2396 n) (@lem115359 P _2396)). Qed.
Lemma lem115361 (n : nat) (P : nat -> Prop) (_2396 : nat) : (term452 P _2396 n) = (term94 n P _2396).
Proof. exact (TRANS (@lem115353 n P _2396) (@lem115360 n P _2396)). Qed.
Lemma lem115364 (_2396 : nat) (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term94 n P _2396.
Proof. exact (EQ_MP (@lem115361 n P _2396) (@lem115350 _2396 n P m h1)). Qed.
Lemma lem115365 (m' : nat -> nat) (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term460 P m' n.
Proof. exact (@lem115364 (m' n) n P m h1). Qed.
Lemma lem115368 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term150 P n) (h2 : term174 n P m) (h3 : term351 n m m' P n') : term461 P m' n.
Proof. exact (@lem115365 m' n P m h2 (@lem115321 n m m' P n' h1 h3)). Qed.
Lemma lem115369 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term150 P n) (h2 : term174 n P m) (h3 : term351 n m m' P n') : term462 P m' n.
Proof. exact (fun h0 : term425 P m' n => @lem115368 n m m' P n' h1 h2 h3). Qed.
Lemma lem115371 (p : Prop) : (term451 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem115372 (P : nat -> Prop) (m' : nat -> nat) (n : nat) : (term462 P m' n) = (term461 P m' n).
Proof. exact (@lem115371 (term461 P m' n)). Qed.
Lemma lem115373 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term150 P n) (h2 : term174 n P m) (h3 : term351 n m m' P n') : term461 P m' n.
Proof. exact (EQ_MP (@lem115372 P m' n) (@lem115369 n m m' P n' h1 h2 h3)). Qed.
Lemma lem115379 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem115380 (P : nat -> Prop) (m' : nat -> nat) (_2390 : nat) : (term444 m' P _2390) = (term463 P m' _2390).
Proof. exact (@lem115379 (P _2390) (term425 P m' _2390)). Qed.
Lemma lem115386 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem115387 (P : nat -> Prop) (m' : nat -> nat) (_2390 : nat) : (term464 m' P _2390) = (term465 P m' _2390).
Proof. exact (MK_COMB (@lem115386) (@lem115380 P m' _2390)). Qed.
Lemma lem115393 (P : nat -> Prop) (m' : nat -> nat) (_2390 : nat) : (term463 P m' _2390) = (term463 P m' _2390).
Proof. exact (eq_refl (term463 P m' _2390)). Qed.
Lemma lem115394 (P : nat -> Prop) (m' : nat -> nat) (_2390 : nat) : ((term444 m' P _2390) = (term463 P m' _2390)) = ((term463 P m' _2390) = (term463 P m' _2390)).
Proof. exact (MK_COMB (@lem115387 P m' _2390) (@lem115393 P m' _2390)). Qed.
Lemma lem115396 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem115397 (x : Prop) : (x = x) = True.
Proof. exact (@lem115396 Prop x). Qed.
Lemma lem115398 (P : nat -> Prop) (m' : nat -> nat) (_2390 : nat) : ((term463 P m' _2390) = (term463 P m' _2390)) = True.
Proof. exact (@lem115397 (term463 P m' _2390)). Qed.
Lemma lem115399 (P : nat -> Prop) (m' : nat -> nat) (_2390 : nat) : ((term444 m' P _2390) = (term463 P m' _2390)) = True.
Proof. exact (TRANS (@lem115394 P m' _2390) (@lem115398 P m' _2390)). Qed.
Lemma lem115400 (P : nat -> Prop) (m' : nat -> nat) (_2390 : nat) : True = ((term444 m' P _2390) = (term463 P m' _2390)).
Proof. exact (SYM (@lem115399 P m' _2390)). Qed.
Lemma lem115401 (P : nat -> Prop) (m' : nat -> nat) (_2390 : nat) : (term444 m' P _2390) = (term463 P m' _2390).
Proof. exact (EQ_MP (@lem115400 P m' _2390) (@lem0)). Qed.
Lemma lem115402 (_2390 : nat) (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term463 P m' _2390.
Proof. exact (EQ_MP (@lem115401 P m' _2390) (@lem115239 _2390 n m m' P n' h1)). Qed.
Lemma lem115404 (b : Prop) (a : Prop) : (a \/ b) = (term447 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem115405 (m' : nat -> nat) (P : nat -> Prop) (_2390 : nat) : (term463 P m' _2390) = (term466 m' P _2390).
Proof. exact (@lem115404 (term425 P m' _2390) (P _2390)). Qed.
Lemma lem115407 (a : Prop) : (term456 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem115408 (P : nat -> Prop) (m' : nat -> nat) (_2390 : nat) : (term467 P m' _2390) = (term461 P m' _2390).
Proof. exact (@lem115407 (term461 P m' _2390)). Qed.
Lemma lem115409 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem115410 (P : nat -> Prop) (m' : nat -> nat) (_2390 : nat) : (term468 P m' _2390) = (term469 P m' _2390).
Proof. exact (MK_COMB (@lem115409) (@lem115408 P m' _2390)). Qed.
Lemma lem115411 (P : nat -> Prop) (_2390 : nat) : (P _2390) = (P _2390).
Proof. exact (eq_refl (P _2390)). Qed.
Lemma lem115412 (m' : nat -> nat) (P : nat -> Prop) (_2390 : nat) : (term466 m' P _2390) = (term470 m' P _2390).
Proof. exact (MK_COMB (@lem115410 P m' _2390) (@lem115411 P _2390)). Qed.
Lemma lem115413 (m' : nat -> nat) (P : nat -> Prop) (_2390 : nat) : (term463 P m' _2390) = (term470 m' P _2390).
Proof. exact (TRANS (@lem115405 m' P _2390) (@lem115412 m' P _2390)). Qed.
Lemma lem115416 (_2390 : nat) (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term470 m' P _2390.
Proof. exact (EQ_MP (@lem115413 m' P _2390) (@lem115402 _2390 n m m' P n' h1)). Qed.
Lemma lem115417 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term470 m' P n.
Proof. exact (@lem115416 n n m m' P n' h1). Qed.
Lemma lem115420 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term150 P n) (h2 : term174 n P m) (h3 : term351 n m m' P n') : P n.
Proof. exact (@lem115417 n m m' P n' h3 (@lem115373 n m m' P n' h1 h2 h3)). Qed.
Lemma lem115421 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term174 n P m) (h2 : term351 n m m' P n') : term471 P n.
Proof. exact (fun h0 : term150 P n => @lem115420 n m m' P n' h0 h1 h2). Qed.
Lemma lem115423 (p : Prop) : (term451 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem115424 (P : nat -> Prop) (n : nat) : (term471 P n) = (P n).
Proof. exact (@lem115423 (P n)). Qed.
Lemma lem115425 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term174 n P m) (h2 : term351 n m m' P n') : P n.
Proof. exact (EQ_MP (@lem115424 P n) (@lem115421 n m m' P n' h1 h2)). Qed.
Lemma lem115428 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem115430 (P : nat -> Prop) (n : nat) : (term150 P n) = (term472 P n).
Proof. exact (@lem115428 (P n)). Qed.
Lemma lem115433 (P : nat -> Prop) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : m = n) : term472 P n.
Proof. exact (EQ_MP (@lem115430 P n) (@lem115183 P m n h1 h2)). Qed.
Lemma lem115436 (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : term351 n m m' P n') (h3 : m = n) : False.
Proof. exact (@lem115433 P m n h1 h3 (@lem115425 n m m' P n' h1 h2)). Qed.
Lemma lem115437 (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : term351 n m m' P n') (h3 : m = n) : term473.
Proof. exact (fun h0 : ~ False => @lem115436 m' P n' m n h1 h2 h3). Qed.
Lemma lem115439 (p : Prop) : (term451 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem115440 : term473 = False.
Proof. exact (@lem115439 False). Qed.
Lemma lem115500 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem115501 (m : nat) (n : nat) (h1 : Peano.lt m n) : term474 m n.
Proof. exact (fun h0 : term430 m n => @lem115500 m n h1). Qed.
Lemma lem115503 (p : Prop) : (term451 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem115504 (m : nat) (n : nat) : (term474 m n) = (Peano.lt m n).
Proof. exact (@lem115503 (Peano.lt m n)). Qed.
Lemma lem115505 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem115504 m n) (@lem115501 m n h1)). Qed.
Lemma lem115511 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem115512 (P : nat -> Prop) (_2403 : nat) (n : nat) : (term100 n P _2403) = (term452 P _2403 n).
Proof. exact (@lem115511 (P _2403) (term430 _2403 n)). Qed.
Lemma lem115518 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem115519 (P : nat -> Prop) (_2403 : nat) (n : nat) : (term453 n P _2403) = (term454 P _2403 n).
Proof. exact (MK_COMB (@lem115518) (@lem115512 P _2403 n)). Qed.
Lemma lem115525 (P : nat -> Prop) (_2403 : nat) (n : nat) : (term452 P _2403 n) = (term452 P _2403 n).
Proof. exact (eq_refl (term452 P _2403 n)). Qed.
Lemma lem115526 (P : nat -> Prop) (_2403 : nat) (n : nat) : ((term100 n P _2403) = (term452 P _2403 n)) = ((term452 P _2403 n) = (term452 P _2403 n)).
Proof. exact (MK_COMB (@lem115519 P _2403 n) (@lem115525 P _2403 n)). Qed.
Lemma lem115528 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem115529 (x : Prop) : (x = x) = True.
Proof. exact (@lem115528 Prop x). Qed.
Lemma lem115530 (P : nat -> Prop) (_2403 : nat) (n : nat) : ((term452 P _2403 n) = (term452 P _2403 n)) = True.
Proof. exact (@lem115529 (term452 P _2403 n)). Qed.
Lemma lem115531 (P : nat -> Prop) (_2403 : nat) (n : nat) : ((term100 n P _2403) = (term452 P _2403 n)) = True.
Proof. exact (TRANS (@lem115526 P _2403 n) (@lem115530 P _2403 n)). Qed.
Lemma lem115532 (P : nat -> Prop) (_2403 : nat) (n : nat) : True = ((term100 n P _2403) = (term452 P _2403 n)).
Proof. exact (SYM (@lem115531 P _2403 n)). Qed.
Lemma lem115533 (P : nat -> Prop) (_2403 : nat) (n : nat) : (term100 n P _2403) = (term452 P _2403 n).
Proof. exact (EQ_MP (@lem115532 P _2403 n) (@lem0)). Qed.
Lemma lem115534 (_2403 : nat) (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term452 P _2403 n.
Proof. exact (EQ_MP (@lem115533 P _2403 n) (@lem115028 _2403 n P m h1)). Qed.
Lemma lem115536 (b : Prop) (a : Prop) : (a \/ b) = (term447 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem115537 (n : nat) (P : nat -> Prop) (_2403 : nat) : (term452 P _2403 n) = (term455 n P _2403).
Proof. exact (@lem115536 (term430 _2403 n) (P _2403)). Qed.
Lemma lem115539 (a : Prop) : (term456 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem115540 (_2403 : nat) (n : nat) : (term457 _2403 n) = (Peano.lt _2403 n).
Proof. exact (@lem115539 (Peano.lt _2403 n)). Qed.
Lemma lem115541 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem115542 (_2403 : nat) (n : nat) : (term458 _2403 n) = (term459 _2403 n).
Proof. exact (MK_COMB (@lem115541) (@lem115540 _2403 n)). Qed.
Lemma lem115543 (P : nat -> Prop) (_2403 : nat) : (P _2403) = (P _2403).
Proof. exact (eq_refl (P _2403)). Qed.
Lemma lem115544 (n : nat) (P : nat -> Prop) (_2403 : nat) : (term455 n P _2403) = (term94 n P _2403).
Proof. exact (MK_COMB (@lem115542 _2403 n) (@lem115543 P _2403)). Qed.
Lemma lem115545 (n : nat) (P : nat -> Prop) (_2403 : nat) : (term452 P _2403 n) = (term94 n P _2403).
Proof. exact (TRANS (@lem115537 n P _2403) (@lem115544 n P _2403)). Qed.
Lemma lem115548 (_2403 : nat) (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term94 n P _2403.
Proof. exact (EQ_MP (@lem115545 n P _2403) (@lem115534 _2403 n P m h1)). Qed.
Lemma lem115549 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term94 n P m.
Proof. exact (@lem115548 m n P m h1). Qed.
Lemma lem115552 (P : nat -> Prop) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : Peano.lt m n) : P m.
Proof. exact (@lem115549 n P m h1 (@lem115505 m n h2)). Qed.
Lemma lem115553 (P : nat -> Prop) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : Peano.lt m n) : term471 P m.
Proof. exact (fun h0 : term150 P m => @lem115552 P m n h1 h2). Qed.
Lemma lem115555 (p : Prop) : (term451 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem115556 (P : nat -> Prop) (m : nat) : (term471 P m) = (P m).
Proof. exact (@lem115555 (P m)). Qed.
Lemma lem115557 (P : nat -> Prop) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : Peano.lt m n) : P m.
Proof. exact (EQ_MP (@lem115556 P m) (@lem115553 P m n h1 h2)). Qed.
Lemma lem115560 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem115562 (P : nat -> Prop) (m : nat) : (term150 P m) = (term472 P m).
Proof. exact (@lem115560 (P m)). Qed.
Lemma lem115565 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term174 n P m) : term472 P m.
Proof. exact (EQ_MP (@lem115562 P m) (@lem115030 n P m h1)). Qed.
Lemma lem115568 (P : nat -> Prop) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : Peano.lt m n) : False.
Proof. exact (@lem115565 n P m h1 (@lem115557 P m n h1 h2)). Qed.
Lemma lem115569 (P : nat -> Prop) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : Peano.lt m n) : term473.
Proof. exact (fun h0 : ~ False => @lem115568 P m n h1 h2). Qed.
Lemma lem115571 (p : Prop) : (term451 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem115572 : term473 = False.
Proof. exact (@lem115571 False). Qed.
Lemma lem115573 (P : nat -> Prop) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem115572) (@lem115569 P m n h1 h2)). Qed.
Lemma lem115632 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem115633 (n' : nat) : n' = n'.
Proof. exact (@lem115632 n'). Qed.
Lemma lem115634 (n' : nat) : term475 n'.
Proof. exact (fun h0 : term476 n' => @lem115633 n'). Qed.
Lemma lem115636 (p : Prop) : (term451 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem115637 (n' : nat) : (term475 n') = (n' = n').
Proof. exact (@lem115636 (n' = n')). Qed.
Lemma lem115638 (n' : nat) : n' = n'.
Proof. exact (EQ_MP (@lem115637 n') (@lem115634 n')). Qed.
Lemma lem115640 (b : Prop) (a : Prop) : (a \/ b) = (term447 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem115641 (_2406 : nat) (_2407 : nat) : (term440 _2406 _2407) = (term477 _2406 _2407).
Proof. exact (@lem115640 (term429 _2406 _2407) (term4 _2406 _2407)). Qed.
Lemma lem115643 (a : Prop) : (term456 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem115644 (_2406 : nat) (_2407 : nat) : (term478 _2406 _2407) = (_2406 = _2407).
Proof. exact (@lem115643 (_2406 = _2407)). Qed.
Lemma lem115645 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem115646 (_2406 : nat) (_2407 : nat) : (term479 _2406 _2407) = (term480 _2406 _2407).
Proof. exact (MK_COMB (@lem115645) (@lem115644 _2406 _2407)). Qed.
Lemma lem115647 (_2406 : nat) (_2407 : nat) : (term4 _2406 _2407) = (term4 _2406 _2407).
Proof. exact (eq_refl (term4 _2406 _2407)). Qed.
Lemma lem115648 (_2406 : nat) (_2407 : nat) : (term477 _2406 _2407) = (term481 _2406 _2407).
Proof. exact (MK_COMB (@lem115646 _2406 _2407) (@lem115647 _2406 _2407)). Qed.
Lemma lem115649 (_2406 : nat) (_2407 : nat) : (term440 _2406 _2407) = (term481 _2406 _2407).
Proof. exact (TRANS (@lem115641 _2406 _2407) (@lem115648 _2406 _2407)). Qed.
Lemma lem115652 (_2406 : nat) (_2407 : nat) (h1 : term82) : term481 _2406 _2407.
Proof. exact (EQ_MP (@lem115649 _2406 _2407) (@lem115082 _2406 _2407 h1)). Qed.
Lemma lem115653 (n' : nat) (h1 : term82) : term482 n'.
Proof. exact (@lem115652 n' n' h1). Qed.
Lemma lem115656 (n' : nat) (h1 : term82) : term483 n'.
Proof. exact (@lem115653 n' h1 (@lem115638 n')). Qed.
Lemma lem115657 (n' : nat) (h1 : term82) : term484 n'.
Proof. exact (fun h0 : term485 n' => @lem115656 n' h1). Qed.
Lemma lem115659 (p : Prop) : (term451 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem115660 (n' : nat) : (term484 n') = (term483 n').
Proof. exact (@lem115659 (term483 n')). Qed.
Lemma lem115661 (n' : nat) (h1 : term82) : term483 n'.
Proof. exact (EQ_MP (@lem115660 n') (@lem115657 n' h1)). Qed.
Lemma lem115667 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem115668 (P : nat -> Prop) (_2411 : nat) (_2410 : nat) : (term100 _2410 P _2411) = (term452 P _2411 _2410).
Proof. exact (@lem115667 (P _2411) (term430 _2411 _2410)). Qed.
Lemma lem115674 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem115675 (P : nat -> Prop) (_2411 : nat) (_2410 : nat) : (term453 _2410 P _2411) = (term454 P _2411 _2410).
Proof. exact (MK_COMB (@lem115674) (@lem115668 P _2411 _2410)). Qed.
Lemma lem115681 (P : nat -> Prop) (_2411 : nat) (_2410 : nat) : (term452 P _2411 _2410) = (term452 P _2411 _2410).
Proof. exact (eq_refl (term452 P _2411 _2410)). Qed.
Lemma lem115682 (P : nat -> Prop) (_2411 : nat) (_2410 : nat) : ((term100 _2410 P _2411) = (term452 P _2411 _2410)) = ((term452 P _2411 _2410) = (term452 P _2411 _2410)).
Proof. exact (MK_COMB (@lem115675 P _2411 _2410) (@lem115681 P _2411 _2410)). Qed.
Lemma lem115684 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem115685 (x : Prop) : (x = x) = True.
Proof. exact (@lem115684 Prop x). Qed.
Lemma lem115686 (P : nat -> Prop) (_2411 : nat) (_2410 : nat) : ((term452 P _2411 _2410) = (term452 P _2411 _2410)) = True.
Proof. exact (@lem115685 (term452 P _2411 _2410)). Qed.
Lemma lem115687 (P : nat -> Prop) (_2411 : nat) (_2410 : nat) : ((term100 _2410 P _2411) = (term452 P _2411 _2410)) = True.
Proof. exact (TRANS (@lem115682 P _2411 _2410) (@lem115686 P _2411 _2410)). Qed.
Lemma lem115688 (P : nat -> Prop) (_2411 : nat) (_2410 : nat) : True = ((term100 _2410 P _2411) = (term452 P _2411 _2410)).
Proof. exact (SYM (@lem115687 P _2411 _2410)). Qed.
Lemma lem115689 (P : nat -> Prop) (_2411 : nat) (_2410 : nat) : (term100 _2410 P _2411) = (term452 P _2411 _2410).
Proof. exact (EQ_MP (@lem115688 P _2411 _2410) (@lem0)). Qed.
Lemma lem115690 (_2411 : nat) (_2410 : nat) (P : nat -> Prop) (h1 : term127 P) : term452 P _2411 _2410.
Proof. exact (EQ_MP (@lem115689 P _2411 _2410) (@lem115076 _2410 _2411 P h1)). Qed.
Lemma lem115692 (b : Prop) (a : Prop) : (a \/ b) = (term447 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem115693 (_2410 : nat) (P : nat -> Prop) (_2411 : nat) : (term452 P _2411 _2410) = (term455 _2410 P _2411).
Proof. exact (@lem115692 (term430 _2411 _2410) (P _2411)). Qed.
Lemma lem115695 (a : Prop) : (term456 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem115696 (_2411 : nat) (_2410 : nat) : (term457 _2411 _2410) = (Peano.lt _2411 _2410).
Proof. exact (@lem115695 (Peano.lt _2411 _2410)). Qed.
Lemma lem115697 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem115698 (_2411 : nat) (_2410 : nat) : (term458 _2411 _2410) = (term459 _2411 _2410).
Proof. exact (MK_COMB (@lem115697) (@lem115696 _2411 _2410)). Qed.
Lemma lem115699 (P : nat -> Prop) (_2411 : nat) : (P _2411) = (P _2411).
Proof. exact (eq_refl (P _2411)). Qed.
Lemma lem115700 (_2410 : nat) (P : nat -> Prop) (_2411 : nat) : (term455 _2410 P _2411) = (term94 _2410 P _2411).
Proof. exact (MK_COMB (@lem115698 _2411 _2410) (@lem115699 P _2411)). Qed.
Lemma lem115701 (_2410 : nat) (P : nat -> Prop) (_2411 : nat) : (term452 P _2411 _2410) = (term94 _2410 P _2411).
Proof. exact (TRANS (@lem115693 _2410 P _2411) (@lem115700 _2410 P _2411)). Qed.
Lemma lem115704 (_2410 : nat) (_2411 : nat) (P : nat -> Prop) (h1 : term127 P) : term94 _2410 P _2411.
Proof. exact (EQ_MP (@lem115701 _2410 P _2411) (@lem115690 _2411 _2410 P h1)). Qed.
Lemma lem115705 (n' : nat) (P : nat -> Prop) (h1 : term127 P) : term486 P n'.
Proof. exact (@lem115704 (S n') n' P h1). Qed.
Lemma lem115708 (n' : nat) (P : nat -> Prop) (h1 : term127 P) (h2 : term82) : P n'.
Proof. exact (@lem115705 n' P h1 (@lem115661 n' h2)). Qed.
Lemma lem115709 (n' : nat) (P : nat -> Prop) (h1 : term127 P) (h2 : term82) : term471 P n'.
Proof. exact (fun h0 : term150 P n' => @lem115708 n' P h1 h2). Qed.
Lemma lem115711 (p : Prop) : (term451 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem115712 (P : nat -> Prop) (n' : nat) : (term471 P n') = (P n').
Proof. exact (@lem115711 (P n')). Qed.
Lemma lem115713 (n' : nat) (P : nat -> Prop) (h1 : term127 P) (h2 : term82) : P n'.
Proof. exact (EQ_MP (@lem115712 P n') (@lem115709 n' P h1 h2)). Qed.
Lemma lem115716 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem115718 (P : nat -> Prop) (n' : nat) : (term150 P n') = (term472 P n').
Proof. exact (@lem115716 (P n')). Qed.
Lemma lem115721 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term351 n m m' P n') : term472 P n'.
Proof. exact (EQ_MP (@lem115718 P n') (@lem115058 n m m' P n' h1)). Qed.
Lemma lem115724 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term127 P) (h2 : term82) (h3 : term351 n m m' P n') : False.
Proof. exact (@lem115721 n m m' P n' h3 (@lem115713 n' P h1 h2)). Qed.
Lemma lem115725 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term127 P) (h2 : term82) (h3 : term351 n m m' P n') : term473.
Proof. exact (fun h0 : ~ False => @lem115724 n m m' P n' h1 h2 h3). Qed.
Lemma lem115727 (p : Prop) : (term451 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem115728 : term473 = False.
Proof. exact (@lem115727 False). Qed.
Lemma lem115729 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term127 P) (h2 : term82) (h3 : term351 n m m' P n') : False.
Proof. exact (EQ_MP (@lem115728) (@lem115725 n m m' P n' h1 h2 h3)). Qed.
Lemma lem115730 (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : term351 n m m' P n') (h3 : m = n) : False.
Proof. exact (EQ_MP (@lem115440) (@lem115437 m' P n' m n h1 h2 h3)). Qed.
Lemma lem115731 (P : nat -> Prop) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem115573 P m n h1 h2) (fun h3 : False => @lem115032 m n h2)). Qed.
Lemma lem115732 (P : nat -> Prop) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem115731 P m n h1 h2) (@lem115032 m n h2)). Qed.
Lemma lem115733 (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : term351 n m m' P n') (h3 : m = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem115730 m' P n' m n h1 h2 h3) (fun h4 : False => @lem114984 m n h3)). Qed.
Lemma lem115734 (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : term351 n m m' P n') (h3 : m = n) : False.
Proof. exact (EQ_MP (@lem115733 m' P n' m n h1 h2 h3) (@lem114984 m n h3)). Qed.
Lemma lem115735 (P : nat -> Prop) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem115732 P m n h1 h2) (fun h3 : False => @lem114784 m n h2)). Qed.
Lemma lem115736 (P : nat -> Prop) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem115735 P m n h1 h2) (@lem114784 m n h2)). Qed.
Lemma lem115737 (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : term351 n m m' P n') (h3 : m = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem115734 m' P n' m n h1 h2 h3) (fun h4 : False => @lem114681 m n h3)). Qed.
Lemma lem115738 (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : term351 n m m' P n') (h3 : m = n) : False.
Proof. exact (EQ_MP (@lem115737 m' P n' m n h1 h2 h3) (@lem114681 m n h3)). Qed.
Lemma lem115739 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term127 P) (h2 : term82) (h3 : term351 n m m' P n') : (term127 P) = False.
Proof. exact (prop_ext (fun h4 : term127 P => @lem115729 n m m' P n' h1 h2 h3) (fun h4 : False => @lem114882 P h1)). Qed.
Lemma lem115740 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term127 P) (h2 : term82) (h3 : term351 n m m' P n') : False.
Proof. exact (EQ_MP (@lem115739 n m m' P n' h1 h2 h3) (@lem114882 P h1)). Qed.
Lemma lem115741 (P : nat -> Prop) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem115736 P m n h1 h2) (fun h3 : False => @lem114784 m n h2)). Qed.
Lemma lem115742 (P : nat -> Prop) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem115741 P m n h1 h2) (@lem114784 m n h2)). Qed.
Lemma lem115743 (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : term351 n m m' P n') (h3 : m = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem115738 m' P n' m n h1 h2 h3) (fun h4 : False => @lem114681 m n h3)). Qed.
Lemma lem115744 (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (m : nat) (n : nat) (h1 : term174 n P m) (h2 : term351 n m m' P n') (h3 : m = n) : False.
Proof. exact (EQ_MP (@lem115743 m' P n' m n h1 h2 h3) (@lem114681 m n h3)). Qed.
Lemma lem115745 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term174 n P m) (h2 : term351 n m m' P n') : False.
Proof. exact (or_elim (@lem114576 n P m h1) (fun h0 : m = n => @lem115744 m' P n' m n h1 h2 h0) (fun h0 : Peano.lt m n => @lem115742 P m n h1 h0)). Qed.
Lemma lem115746 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term82) (h2 : term351 n m m' P n') : False.
Proof. exact (or_elim (@lem114564 n m m' P n' h2) (fun h0 : term174 n P m => @lem115745 n m m' P n' h0 h2) (fun h0 : term127 P => @lem115740 n m m' P n' h0 h1 h2)). Qed.
Lemma lem115747 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term82) (h2 : term351 n m m' P n') : (term351 n m m' P n') = False.
Proof. exact (prop_ext (fun h3 : term351 n m m' P n' => @lem115746 n m m' P n' h1 h2) (fun h3 : False => @lem114562 n m m' P n' h2)). Qed.
Lemma lem115748 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term82) (h2 : term351 n m m' P n') : False.
Proof. exact (EQ_MP (@lem115747 n m m' P n' h1 h2) (@lem114562 n m m' P n' h2)). Qed.
Lemma lem115749 (n : nat) (m : nat) (m' : nat -> nat) (P : nat -> Prop) (h1 : term354 n m m' P) (h2 : term82) : False.
Proof. exact (ex_elim (@lem114378 n m m' P h1) (fun n' : nat => fun h0 : term353 n m m' P n' => @lem115748 n m m' P n' h2 h0)). Qed.
Lemma lem115750 (n : nat) (m : nat) (P : nat -> Prop) (h1 : term356 n m P) (h2 : term82) : False.
Proof. exact (ex_elim (@lem114377 n m P h1) (fun m' : nat -> nat => fun h0 : term355 n m P m' => @lem115749 n m m' P h0 h2)). Qed.
Lemma lem115751 (n : nat) (P : nat -> Prop) (h1 : term358 n P) (h2 : term82) : False.
Proof. exact (ex_elim (@lem114376 n P h1) (fun m : nat => fun h0 : term357 n P m => @lem115750 n m P h0 h2)). Qed.
Lemma lem115752 (P : nat -> Prop) (h1 : term68 P) (h2 : term82) : False.
Proof. exact (ex_elim (@lem114065 P h1) (fun n : nat => fun h0 : term359 P n => @lem115751 n P h0 h2)). Qed.
Lemma lem115753 (P : nat -> Prop) (h1 : term68 P) : term487.
Proof. exact (fun h0 : term82 => @lem115752 P h1 h0). Qed.
Lemma lem115754 : term487 = term83.
Proof. exact (@lem69 term82). Qed.
Lemma lem115755 (P : nat -> Prop) (h1 : term68 P) : term83.
Proof. exact (EQ_MP (@lem115754) (@lem115753 P h1)). Qed.
Lemma lem115756 (P : nat -> Prop) : term85 P.
Proof. exact (fun h0 : term68 P => @lem115755 P h0). Qed.
Lemma lem115761 : term89.
Proof. exact (fun P : nat -> Prop => @lem115756 P). Qed.
Lemma lem115762 : term88.
Proof. exact (EQ_MP (@lem113405) (@lem115761)). Qed.
Lemma lem115763 (P : nat -> Prop) : term488 P.
Proof. exact (@lem115762 P). Qed.
Lemma lem115764 (P : nat -> Prop) : (term488 P) = (term69 P).
Proof. exact (eq_refl (term488 P)). Qed.
Lemma lem115765 (P : nat -> Prop) : term69 P.
Proof. exact (EQ_MP (@lem115764 P) (@lem115763 P)). Qed.
Lemma lem115767 (P : nat -> Prop) : term69 P.
Proof. exact (@lem113093 P (@lem115765 P)). Qed.
Lemma lem115768 (P : nat -> Prop) (h1 : term68 P) : term73.
Proof. exact (@lem115767 P (@lem113078 P h1)). Qed.
Lemma lem115769 (P : nat -> Prop) (h1 : term68 P) : False.
Proof. exact (@lem115768 P h1 (@lem89997)). Qed.
Lemma lem115770 (P : nat -> Prop) (h1 : term68 P) : (term68 P) = False.
Proof. exact (prop_ext (fun h2 : term68 P => @lem115769 P h1) (fun h2 : False => @lem113078 P h1)). Qed.
Lemma lem115771 (P : nat -> Prop) (h1 : term68 P) : False.
Proof. exact (EQ_MP (@lem115770 P h1) (@lem113078 P h1)). Qed.
Lemma lem115772 (P : nat -> Prop) : term67 P.
Proof. exact (fun h0 : term68 P => @lem115771 P h0). Qed.
Lemma lem115773 (P : nat -> Prop) : term65 P.
Proof. exact (EQ_MP (@lem113077 P) (@lem115772 P)). Qed.
Lemma lem115774 (P : nat -> Prop) : term64 P.
Proof. exact (EQ_MP (@lem113073 P) (@lem115773 P)). Qed.
Lemma lem115775 (P : nat -> Prop) : term63 P.
Proof. exact (@lem115774 P (@lem112864 P)). Qed.
Lemma lem115780 : term489.
Proof. exact (fun P : nat -> Prop => @lem115775 P). Qed.
