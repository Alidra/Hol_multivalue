Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EVEN_ODD_DECOMPOSITION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EVEN_EXISTS_spec.
Require Import EVEN_OR_ODD_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import EXP_spec.
Require Import EXP_EQ_0_spec.
Require Import LT_MULT_RCANCEL_spec.
Require Import MONO_EXISTS_spec.
Require Import MULT_ASSOC_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_EQ_0_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import ODD_spec.
Require Import SWAP_EXISTS_THM_spec.
Require Import TWO_spec.
Require Import num_WF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm129_spec.
Require Import thm137_spec.
Require Import thm16464_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm80550_spec.
Require Import thm82_spec.
Require Import thm86199_spec.
Require Import thm89994_spec.
Lemma lem128895 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem128896 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term1 A P Q.
Proof. exact (h1). Qed.
Lemma lem128897 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem128895 A P Q h2 (@lem128896 A P Q h1)). Qed.
Lemma lem128898 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term3 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem128897 A P Q h1 h0). Qed.
Lemma lem128899 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem128900 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem128898 A P Q h1 (@lem128899 A P Q h2)). Qed.
Lemma lem128901 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (fun h0 : term1 A P Q => @lem128900 A P Q h0 h1). Qed.
Lemma lem128902 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term4 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem128901 A P Q h0). Qed.
Lemma lem128904 {A B : Type'} (P : type1413 A B) : term5 A B P.
Proof. exact (@lem4848 A B P). Qed.
Lemma lem128905 {A B : Type'} (P : type1413 A B) : (term5 A B P) = ((term6 A B P) = (term7 A B P)).
Proof. exact (eq_refl (term5 A B P)). Qed.
Lemma lem128907 (h1 : term8 = term9) : term8 = term9.
Proof. exact (h1). Qed.
Lemma lem128908 (h1 : term8 = term9) : term9 = term8.
Proof. exact (SYM (@lem128907 h1)). Qed.
Lemma lem128909 (h1 : term9 = term8) : term9 = term8.
Proof. exact (h1). Qed.
Lemma lem128910 (h1 : term9 = term8) : term8 = term9.
Proof. exact (SYM (@lem128909 h1)). Qed.
Lemma lem128911 : (term8 = term9) = (term9 = term8).
Proof. exact (prop_ext (fun h1 : term8 = term9 => @lem128908 h1) (fun h1 : term9 = term8 => @lem128910 h1)). Qed.
Lemma lem128913 (n : nat) : term10 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem128914 (n : nat) : (term10 n) = (term11 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem128915 (n : nat) : term11 n.
Proof. exact (EQ_MP (@lem128914 n) (@lem128913 n)). Qed.
Lemma lem128916 (n : nat) : term12 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem128929 : term13.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem128931 : term14.
Proof. exact (proj2 (@lem128929)). Qed.
Lemma lem128934 : term15.
Proof. exact (proj1 (@lem128931)). Qed.
Lemma lem128940 (n : nat) (h1 : (term16 n) = n) : (term16 n) = n.
Proof. exact (h1). Qed.
Lemma lem128941 (n : nat) (h1 : (term16 n) = n) : n = (term16 n).
Proof. exact (SYM (@lem128940 n h1)). Qed.
Lemma lem128942 (n : nat) (h1 : n = (term16 n)) : n = (term16 n).
Proof. exact (h1). Qed.
Lemma lem128943 (n : nat) (h1 : n = (term16 n)) : (term16 n) = n.
Proof. exact (SYM (@lem128942 n h1)). Qed.
Lemma lem128944 (n : nat) : ((term16 n) = n) = (n = (term16 n)).
Proof. exact (prop_ext (fun h1 : (term16 n) = n => @lem128941 n h1) (fun h1 : n = (term16 n) => @lem128943 n h1)). Qed.
Lemma lem128945 : term17 = term18.
Proof. exact (fun_ext (fun n : nat => @lem128944 n)). Qed.
Lemma lem128946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem128947 : term15 = term19.
Proof. exact (MK_COMB (@lem128946) (@lem128945)). Qed.
Lemma lem128948 : term19.
Proof. exact (EQ_MP (@lem128947) (@lem128934)). Qed.
Lemma lem128949 (n : nat) : term20 n.
Proof. exact (@lem128948 n). Qed.
Lemma lem128950 (n : nat) : (term20 n) = (n = (term16 n)).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem128962 (n : nat) : term10 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem128963 (n : nat) : (term10 n) = (term11 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem128964 (n : nat) : term11 n.
Proof. exact (EQ_MP (@lem128963 n) (@lem128962 n)). Qed.
Lemma lem128965 (n : nat) : term12 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem128978 (m : nat) : term21 m.
Proof. exact (@lem83870 m). Qed.
Lemma lem128979 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem128980 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem128979 m) (@lem128978 m)). Qed.
Lemma lem128981 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem128980 m n). Qed.
Lemma lem128982 (m : nat) (n : nat) : (term23 m n) = (((Nat.mul m n) = (NUMERAL 0)) = (term24 m n)).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem128984 (m : nat) : term25 m.
Proof. exact (@lem86997 m). Qed.
Lemma lem128985 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem128986 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem128985 m) (@lem128984 m)). Qed.
Lemma lem128987 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem128986 m n). Qed.
Lemma lem128988 (m : nat) (n : nat) : (term27 m n) = (((Nat.pow m n) = (NUMERAL 0)) = (term28 m n)).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem128997 : term29.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem128998 (m : nat) : term30 m.
Proof. exact (@lem128997 m). Qed.
Lemma lem128999 (m : nat) : (term30 m) = ((term31 m) = False).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem129001 : term13.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem129027 : term32.
Proof. exact (proj1 (@lem129001)). Qed.
Lemma lem129028 (m : nat) : term33 m.
Proof. exact (@lem129027 m). Qed.
Lemma lem129029 (m : nat) : (term33 m) = ((term34 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem129035 (m : nat) : term35 m.
Proof. exact (@lem9784 (m = (NUMERAL 0))). Qed.
Lemma lem129036 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem129037 (m : nat) : term36 m.
Proof. exact (EQ_MP (@lem129036 m) (@lem129035 m)). Qed.
Lemma lem129039 (m : nat) (h1 : term37 m) : term37 m.
Proof. exact (h1). Qed.
Lemma lem129040 (n : nat) : term38 n.
Proof. exact (@lem128828 n). Qed.
Lemma lem129041 (n : nat) : (term38 n) = ((Coq.Arith.PeanoNat.Nat.Even n) = (term39 n)).
Proof. exact (eq_refl (term38 n)). Qed.
Lemma lem129053 (n : nat) : term40 n.
Proof. exact (@lem124909 n). Qed.
Lemma lem129054 (n : nat) : (term40 n) = (term41 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem129055 (n : nat) : term41 n.
Proof. exact (EQ_MP (@lem129054 n) (@lem129053 n)). Qed.
Lemma lem129056 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem129057 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem129058 (h1 : term42) : term42.
Proof. exact (h1). Qed.
Lemma lem129059 (P : nat -> Prop) (h1 : term42) : term43 P.
Proof. exact (@lem129058 h1 P). Qed.
Lemma lem129060 (P : nat -> Prop) : (term43 P) = (term44 P).
Proof. exact (eq_refl (term43 P)). Qed.
Lemma lem129061 (P : nat -> Prop) (h1 : term42) : term44 P.
Proof. exact (EQ_MP (@lem129060 P) (@lem129059 P h1)). Qed.
Lemma lem129062 (P : nat -> Prop) (h1 : term45 P) : term45 P.
Proof. exact (h1). Qed.
Lemma lem129063 (P : nat -> Prop) (h1 : term42) (h2 : term45 P) : term46 P.
Proof. exact (@lem129061 P h1 (@lem129062 P h2)). Qed.
Lemma lem129064 (P : nat -> Prop) (h1 : term45 P) : term47 P.
Proof. exact (fun h0 : term42 => @lem129063 P h0 h1). Qed.
Lemma lem129065 (h1 : term42) : term42.
Proof. exact (h1). Qed.
Lemma lem129066 (P : nat -> Prop) (h1 : term42) (h2 : term45 P) : term46 P.
Proof. exact (@lem129064 P h2 (@lem129065 h1)). Qed.
Lemma lem129067 (P : nat -> Prop) (h1 : term42) : term44 P.
Proof. exact (fun h0 : term45 P => @lem129066 P h1 h0). Qed.
Lemma lem129068 (h1 : term42) : term42.
Proof. exact (fun P : nat -> Prop => @lem129067 P h1). Qed.
Lemma lem129069 : term48.
Proof. exact (fun h0 : term42 => @lem129068 h0). Qed.
Lemma lem129070 : term42.
Proof. exact (@lem129069 (@lem115780)). Qed.
Lemma lem129071 (P : nat -> Prop) : term43 P.
Proof. exact (@lem129070 P). Qed.
Lemma lem129072 (P : nat -> Prop) : (term43 P) = (term44 P).
Proof. exact (eq_refl (term43 P)). Qed.
Lemma lem129075 (P : nat -> Prop) : term44 P.
Proof. exact (EQ_MP (@lem129072 P) (@lem129071 P)). Qed.
Lemma lem129076 : term49.
Proof. exact (@lem129075 term50). Qed.
Lemma lem129077 (m : nat) : (term51 m) = ((term52 m) = (term37 m)).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem129078 (m : nat) (n : nat) : (term53 m n) = (term53 m n).
Proof. exact (eq_refl (term53 m n)). Qed.
Lemma lem129079 (n : nat) (m : nat) : (term54 n m) = (term55 n m).
Proof. exact (MK_COMB (@lem129078 m n) (@lem129077 m)). Qed.
Lemma lem129080 (n : nat) : (term56 n) = (term57 n).
Proof. exact (fun_ext (fun m : nat => @lem129079 n m)). Qed.
Lemma lem129081 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129082 (n : nat) : (term58 n) = (term59 n).
Proof. exact (MK_COMB (@lem129081) (@lem129080 n)). Qed.
Lemma lem129083 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem129084 (n : nat) : (term60 n) = (term61 n).
Proof. exact (MK_COMB (@lem129083) (@lem129082 n)). Qed.
Lemma lem129085 (n : nat) : (term51 n) = ((term52 n) = (term37 n)).
Proof. exact (eq_refl (term51 n)). Qed.
Lemma lem129086 (n : nat) : (term62 n) = (term63 n).
Proof. exact (MK_COMB (@lem129084 n) (@lem129085 n)). Qed.
Lemma lem129087 : term64 = term65.
Proof. exact (fun_ext (fun n : nat => @lem129086 n)). Qed.
Lemma lem129088 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129089 : term66 = term67.
Proof. exact (MK_COMB (@lem129088) (@lem129087)). Qed.
Lemma lem129090 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem129091 : term68 = term69.
Proof. exact (MK_COMB (@lem129090) (@lem129089)). Qed.
Lemma lem129092 (n : nat) : (term51 n) = ((term52 n) = (term37 n)).
Proof. exact (eq_refl (term51 n)). Qed.
Lemma lem129093 : term70 = term50.
Proof. exact (fun_ext (fun n : nat => @lem129092 n)). Qed.
Lemma lem129094 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129095 : term71 = term72.
Proof. exact (MK_COMB (@lem129094) (@lem129093)). Qed.
Lemma lem129096 : term49 = term73.
Proof. exact (MK_COMB (@lem129091) (@lem129095)). Qed.
Lemma lem129097 : term73.
Proof. exact (EQ_MP (@lem129096) (@lem129076)). Qed.
Lemma lem129098 (n : nat) (h1 : term59 n) : term59 n.
Proof. exact (h1). Qed.
Lemma lem129100 (p : Prop) : p = (term74 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem129101 (n : nat) : ((term52 n) = (term37 n)) = (term75 n).
Proof. exact (@lem129100 ((term52 n) = (term37 n))). Qed.
Lemma lem129102 (n : nat) : (term75 n) = ((term52 n) = (term37 n)).
Proof. exact (SYM (@lem129101 n)). Qed.
Lemma lem129103 (n : nat) (h1 : term76 n) : term76 n.
Proof. exact (h1). Qed.
Lemma lem129106 (n : nat) (h1 : term77 n) : term77 n.
Proof. exact (h1). Qed.
Lemma lem129107 (n : nat) : term78 n.
Proof. exact (fun h0 : term77 n => @lem129106 n h0). Qed.
Lemma lem129108 (n : nat) (h1 : term78 n) : term78 n.
Proof. exact (h1). Qed.
Lemma lem129109 (n : nat) (h1 : term77 n) : term77 n.
Proof. exact (h1). Qed.
Lemma lem129110 (n : nat) (h1 : term77 n) (h2 : term78 n) : term77 n.
Proof. exact (@lem129108 n h2 (@lem129109 n h1)). Qed.
Lemma lem129111 (n : nat) (h1 : term77 n) : term79 n.
Proof. exact (fun h0 : term78 n => @lem129110 n h1 h0). Qed.
Lemma lem129112 (n : nat) (h1 : term78 n) : term78 n.
Proof. exact (h1). Qed.
Lemma lem129113 (n : nat) (h1 : term77 n) (h2 : term78 n) : term77 n.
Proof. exact (@lem129111 n h1 (@lem129112 n h2)). Qed.
Lemma lem129114 (n : nat) (h1 : term78 n) : term78 n.
Proof. exact (fun h0 : term77 n => @lem129113 n h0 h1). Qed.
Lemma lem129115 (n : nat) : term80 n.
Proof. exact (fun h0 : term78 n => @lem129114 n h0). Qed.
Lemma lem129118 (n : nat) : term78 n.
Proof. exact (@lem129115 n (@lem129107 n)). Qed.
Lemma lem129264 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem129265 : term81 = term82.
Proof. exact (@lem129264 term83). Qed.
Lemma lem129269 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem129270 : (term84 = False) = term85.
Proof. exact (@lem129269 term84). Qed.
Lemma lem129271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem129272 : term86 = term87.
Proof. exact (MK_COMB (@lem129271) (@lem129270)). Qed.
Lemma lem129277 : term88 = term88.
Proof. exact (eq_refl term88). Qed.
Lemma lem129278 : term83 = term89.
Proof. exact (MK_COMB (@lem129272) (@lem129277)). Qed.
Lemma lem129281 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem129282 : term82 = term90.
Proof. exact (MK_COMB (@lem129281) (@lem129278)). Qed.
Lemma lem129283 : term81 = term90.
Proof. exact (TRANS (@lem129265) (@lem129282)). Qed.
Lemma lem129284 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem129285 : term92 = term93.
Proof. exact (MK_COMB (@lem129284) (@lem129283)). Qed.
Lemma lem129288 : term94 = term94.
Proof. exact (eq_refl term94). Qed.
Lemma lem129289 : term95 = term96.
Proof. exact (MK_COMB (@lem129288) (@lem129285)). Qed.
Lemma lem129292 (n : nat) : (term97 n) = (term97 n).
Proof. exact (eq_refl (term97 n)). Qed.
Lemma lem129293 (n : nat) : (term98 n) = (term99 n).
Proof. exact (MK_COMB (@lem129292 n) (@lem129289)). Qed.
Lemma lem129296 (n : nat) : (term100 n) = (term100 n).
Proof. exact (eq_refl (term100 n)). Qed.
Lemma lem129297 (n : nat) : (term101 n) = (term102 n).
Proof. exact (MK_COMB (@lem129296 n) (@lem129293 n)). Qed.
Lemma lem129300 (n : nat) : (term61 n) = (term61 n).
Proof. exact (eq_refl (term61 n)). Qed.
Lemma lem129301 (n : nat) : (term77 n) = (term103 n).
Proof. exact (MK_COMB (@lem129300 n) (@lem129297 n)). Qed.
Lemma lem129304 : term104 = term105.
Proof. exact (fun_ext (fun n : nat => @lem129301 n)). Qed.
Lemma lem129305 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129314 : term106 = term107.
Proof. exact (MK_COMB (@lem129305) (@lem129304)). Qed.
Lemma lem129321 (n : nat) : ((term108 n) = (term109 n)) = ((term108 n) = (term109 n)).
Proof. exact (eq_refl ((term108 n) = (term109 n))). Qed.
Lemma lem129322 : term110 = term110.
Proof. exact (fun_ext (fun n : nat => @lem129321 n)). Qed.
Lemma lem129323 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129324 : term88 = term88.
Proof. exact (MK_COMB (@lem129323) (@lem129322)). Qed.
Lemma lem129329 : term87 = term87.
Proof. exact (eq_refl term87). Qed.
Lemma lem129330 : term89 = term89.
Proof. exact (MK_COMB (@lem129329) (@lem129324)). Qed.
Lemma lem129331 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem129332 : term90 = term90.
Proof. exact (MK_COMB (@lem129331) (@lem129330)). Qed.
Lemma lem129333 (m : nat) (n : nat) : ((term111 m n) = (term112 m n)) = ((term111 m n) = (term112 m n)).
Proof. exact (eq_refl ((term111 m n) = (term112 m n))). Qed.
Lemma lem129334 (m : nat) : (term113 m) = (term113 m).
Proof. exact (fun_ext (fun n : nat => @lem129333 m n)). Qed.
Lemma lem129335 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129336 (m : nat) : (term114 m) = (term114 m).
Proof. exact (MK_COMB (@lem129335) (@lem129334 m)). Qed.
Lemma lem129337 : term115 = term115.
Proof. exact (fun_ext (fun m : nat => @lem129336 m)). Qed.
Lemma lem129338 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129339 : term116 = term116.
Proof. exact (MK_COMB (@lem129338) (@lem129337)). Qed.
Lemma lem129340 (m : nat) : ((term117 m) = term118) = ((term117 m) = term118).
Proof. exact (eq_refl ((term117 m) = term118)). Qed.
Lemma lem129341 : term119 = term119.
Proof. exact (fun_ext (fun m : nat => @lem129340 m)). Qed.
Lemma lem129342 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129343 : term120 = term120.
Proof. exact (MK_COMB (@lem129342) (@lem129341)). Qed.
Lemma lem129344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem129345 : term121 = term121.
Proof. exact (MK_COMB (@lem129344) (@lem129343)). Qed.
Lemma lem129346 : term122 = term122.
Proof. exact (MK_COMB (@lem129345) (@lem129339)). Qed.
Lemma lem129347 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem129348 : term91 = term91.
Proof. exact (MK_COMB (@lem129347) (@lem129346)). Qed.
Lemma lem129349 : term93 = term93.
Proof. exact (MK_COMB (@lem129348) (@lem129332)). Qed.
Lemma lem129350 (m : nat) (n : nat) : ((term123 m n) = (term124 m n)) = ((term123 m n) = (term124 m n)).
Proof. exact (eq_refl ((term123 m n) = (term124 m n))). Qed.
Lemma lem129351 (m : nat) : (term125 m) = (term125 m).
Proof. exact (fun_ext (fun n : nat => @lem129350 m n)). Qed.
Lemma lem129352 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129353 (m : nat) : (term126 m) = (term126 m).
Proof. exact (MK_COMB (@lem129352) (@lem129351 m)). Qed.
Lemma lem129354 : term127 = term127.
Proof. exact (fun_ext (fun m : nat => @lem129353 m)). Qed.
Lemma lem129355 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129356 : term128 = term128.
Proof. exact (MK_COMB (@lem129355) (@lem129354)). Qed.
Lemma lem129357 (m : nat) (n : nat) : ((term129 m n) = (term130 m n)) = ((term129 m n) = (term130 m n)).
Proof. exact (eq_refl ((term129 m n) = (term130 m n))). Qed.
Lemma lem129358 (m : nat) : (term131 m) = (term131 m).
Proof. exact (fun_ext (fun n : nat => @lem129357 m n)). Qed.
Lemma lem129359 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129360 (m : nat) : (term132 m) = (term132 m).
Proof. exact (MK_COMB (@lem129359) (@lem129358 m)). Qed.
Lemma lem129361 : term133 = term133.
Proof. exact (fun_ext (fun m : nat => @lem129360 m)). Qed.
Lemma lem129362 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129363 : term134 = term134.
Proof. exact (MK_COMB (@lem129362) (@lem129361)). Qed.
Lemma lem129364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem129365 : term135 = term135.
Proof. exact (MK_COMB (@lem129364) (@lem129363)). Qed.
Lemma lem129366 : term136 = term136.
Proof. exact (MK_COMB (@lem129365) (@lem129356)). Qed.
Lemma lem129367 (m : nat) : ((term137 m) = m) = ((term137 m) = m).
Proof. exact (eq_refl ((term137 m) = m)). Qed.
Lemma lem129368 : term138 = term138.
Proof. exact (fun_ext (fun m : nat => @lem129367 m)). Qed.
Lemma lem129369 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129370 : term139 = term139.
Proof. exact (MK_COMB (@lem129369) (@lem129368)). Qed.
Lemma lem129371 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem129372 : term140 = term140.
Proof. exact (MK_COMB (@lem129371) (@lem129370)). Qed.
Lemma lem129373 : term141 = term141.
Proof. exact (MK_COMB (@lem129372) (@lem129366)). Qed.
Lemma lem129374 (n : nat) : ((term16 n) = n) = ((term16 n) = n).
Proof. exact (eq_refl ((term16 n) = n)). Qed.
Lemma lem129375 : term17 = term17.
Proof. exact (fun_ext (fun n : nat => @lem129374 n)). Qed.
Lemma lem129376 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129377 : term15 = term15.
Proof. exact (MK_COMB (@lem129376) (@lem129375)). Qed.
Lemma lem129378 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem129379 : term142 = term142.
Proof. exact (MK_COMB (@lem129378) (@lem129377)). Qed.
Lemma lem129380 : term14 = term14.
Proof. exact (MK_COMB (@lem129379) (@lem129373)). Qed.
Lemma lem129381 (m : nat) : ((term34 m) = (NUMERAL 0)) = ((term34 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term34 m) = (NUMERAL 0))). Qed.
Lemma lem129382 : term143 = term143.
Proof. exact (fun_ext (fun m : nat => @lem129381 m)). Qed.
Lemma lem129383 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129384 : term32 = term32.
Proof. exact (MK_COMB (@lem129383) (@lem129382)). Qed.
Lemma lem129385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem129386 : term144 = term144.
Proof. exact (MK_COMB (@lem129385) (@lem129384)). Qed.
Lemma lem129387 : term13 = term13.
Proof. exact (MK_COMB (@lem129386) (@lem129380)). Qed.
Lemma lem129388 (n : nat) : ((term145 n) = (NUMERAL 0)) = ((term145 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term145 n) = (NUMERAL 0))). Qed.
Lemma lem129389 : term146 = term146.
Proof. exact (fun_ext (fun n : nat => @lem129388 n)). Qed.
Lemma lem129390 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129391 : term147 = term147.
Proof. exact (MK_COMB (@lem129390) (@lem129389)). Qed.
Lemma lem129392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem129393 : term148 = term148.
Proof. exact (MK_COMB (@lem129392) (@lem129391)). Qed.
Lemma lem129394 : term149 = term149.
Proof. exact (MK_COMB (@lem129393) (@lem129387)). Qed.
Lemma lem129395 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem129396 : term94 = term94.
Proof. exact (MK_COMB (@lem129395) (@lem129394)). Qed.
Lemma lem129397 : term96 = term96.
Proof. exact (MK_COMB (@lem129396) (@lem129349)). Qed.
Lemma lem129400 (n : nat) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem129405 (n : nat) (k : nat) (m : nat) : (term150 n k m) = (term150 n k m).
Proof. exact (eq_refl (term150 n k m)). Qed.
Lemma lem129406 (n : nat) (k : nat) : (term151 n k) = (term151 n k).
Proof. exact (fun_ext (fun m : nat => @lem129405 n k m)). Qed.
Lemma lem129407 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129408 (n : nat) (k : nat) : (term152 n k) = (term152 n k).
Proof. exact (MK_COMB (@lem129407) (@lem129406 n k)). Qed.
Lemma lem129409 (n : nat) : (term153 n) = (term153 n).
Proof. exact (fun_ext (fun k : nat => @lem129408 n k)). Qed.
Lemma lem129410 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129411 (n : nat) : (term52 n) = (term52 n).
Proof. exact (MK_COMB (@lem129410) (@lem129409 n)). Qed.
Lemma lem129412 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem129413 (n : nat) : (term154 n) = (term154 n).
Proof. exact (MK_COMB (@lem129412) (@lem129411 n)). Qed.
Lemma lem129414 (n : nat) : ((term52 n) = (term37 n)) = ((term52 n) = (term37 n)).
Proof. exact (MK_COMB (@lem129413 n) (@lem129400 n)). Qed.
Lemma lem129415 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem129416 (n : nat) : (term76 n) = (term76 n).
Proof. exact (MK_COMB (@lem129415) (@lem129414 n)). Qed.
Lemma lem129417 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem129418 (n : nat) : (term97 n) = (term97 n).
Proof. exact (MK_COMB (@lem129417) (@lem129416 n)). Qed.
Lemma lem129419 (n : nat) : (term99 n) = (term99 n).
Proof. exact (MK_COMB (@lem129418 n) (@lem129397)). Qed.
Lemma lem129422 (n : nat) : (term100 n) = (term100 n).
Proof. exact (eq_refl (term100 n)). Qed.
Lemma lem129423 (n : nat) : (term102 n) = (term102 n).
Proof. exact (MK_COMB (@lem129422 n) (@lem129419 n)). Qed.
Lemma lem129426 (m : nat) : (term37 m) = (term37 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem129431 (m : nat) (k : nat) (m' : nat) : (term150 m k m') = (term150 m k m').
Proof. exact (eq_refl (term150 m k m')). Qed.
Lemma lem129432 (m : nat) (k : nat) : (term151 m k) = (term151 m k).
Proof. exact (fun_ext (fun m' : nat => @lem129431 m k m')). Qed.
Lemma lem129433 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129434 (m : nat) (k : nat) : (term152 m k) = (term152 m k).
Proof. exact (MK_COMB (@lem129433) (@lem129432 m k)). Qed.
Lemma lem129435 (m : nat) : (term153 m) = (term153 m).
Proof. exact (fun_ext (fun k : nat => @lem129434 m k)). Qed.
Lemma lem129436 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129437 (m : nat) : (term52 m) = (term52 m).
Proof. exact (MK_COMB (@lem129436) (@lem129435 m)). Qed.
Lemma lem129438 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem129439 (m : nat) : (term154 m) = (term154 m).
Proof. exact (MK_COMB (@lem129438) (@lem129437 m)). Qed.
Lemma lem129440 (m : nat) : ((term52 m) = (term37 m)) = ((term52 m) = (term37 m)).
Proof. exact (MK_COMB (@lem129439 m) (@lem129426 m)). Qed.
Lemma lem129443 (m : nat) (n : nat) : (term53 m n) = (term53 m n).
Proof. exact (eq_refl (term53 m n)). Qed.
Lemma lem129444 (n : nat) (m : nat) : (term55 n m) = (term55 n m).
Proof. exact (MK_COMB (@lem129443 m n) (@lem129440 m)). Qed.
Lemma lem129445 (n : nat) : (term57 n) = (term57 n).
Proof. exact (fun_ext (fun m : nat => @lem129444 n m)). Qed.
Lemma lem129446 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129447 (n : nat) : (term59 n) = (term59 n).
Proof. exact (MK_COMB (@lem129446) (@lem129445 n)). Qed.
Lemma lem129448 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem129449 (n : nat) : (term61 n) = (term61 n).
Proof. exact (MK_COMB (@lem129448) (@lem129447 n)). Qed.
Lemma lem129450 (n : nat) : (term103 n) = (term103 n).
Proof. exact (MK_COMB (@lem129449 n) (@lem129423 n)). Qed.
Lemma lem129451 : term105 = term105.
Proof. exact (fun_ext (fun n : nat => @lem129450 n)). Qed.
Lemma lem129452 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129453 : term107 = term107.
Proof. exact (MK_COMB (@lem129452) (@lem129451)). Qed.
Lemma lem129594 : term106 = term107.
Proof. exact (TRANS (@lem129314) (@lem129453)). Qed.
Lemma lem129595 : term107 = term106.
Proof. exact (SYM (@lem129594)). Qed.
Lemma lem129596 (n : nat) (h1 : term59 n) : term59 n.
Proof. exact (h1). Qed.
Lemma lem129598 (n : nat) (h1 : term76 n) : term76 n.
Proof. exact (h1). Qed.
Lemma lem129599 (h1 : term149) : term149.
Proof. exact (h1). Qed.
Lemma lem129600 (h1 : term122) : term122.
Proof. exact (h1). Qed.
Lemma lem129601 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem129611 (m : nat) (k : nat) (m' : nat) : (term155 m k m') = (term156 m k m').
Proof. exact (@lem17045 (Coq.Arith.PeanoNat.Nat.Odd m') (m = (term157 k m'))). Qed.
Lemma lem129614 (m : nat) (k : nat) (m' : nat) : (term150 m k m') = (term150 m k m').
Proof. exact (eq_refl (term150 m k m')). Qed.
Lemma lem129615 (P : nat -> Prop) : (term158 P) = (term159 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem129616 (m : nat) (k : nat) : (term160 m k) = (term161 m k).
Proof. exact (@lem129615 (term151 m k)). Qed.
Lemma lem129617 (m : nat) (k : nat) (m' : nat) : (term162 m k m') = (term150 m k m').
Proof. exact (eq_refl (term162 m k m')). Qed.
Lemma lem129618 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem129619 (m : nat) (k : nat) (m' : nat) : (term163 m k m') = (term155 m k m').
Proof. exact (MK_COMB (@lem129618) (@lem129617 m k m')). Qed.
Lemma lem129620 (m : nat) (k : nat) (m' : nat) : (term163 m k m') = (term156 m k m').
Proof. exact (TRANS (@lem129619 m k m') (@lem129611 m k m')). Qed.
Lemma lem129621 (m : nat) (k : nat) : (term164 m k) = (term165 m k).
Proof. exact (fun_ext (fun m' : nat => @lem129620 m k m')). Qed.
Lemma lem129622 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129623 (m : nat) (k : nat) : (term161 m k) = (term166 m k).
Proof. exact (MK_COMB (@lem129622) (@lem129621 m k)). Qed.
Lemma lem129624 (m : nat) (k : nat) : (term160 m k) = (term166 m k).
Proof. exact (TRANS (@lem129616 m k) (@lem129623 m k)). Qed.
Lemma lem129625 (m : nat) (k : nat) : (term151 m k) = (term151 m k).
Proof. exact (fun_ext (fun m' : nat => @lem129614 m k m')). Qed.
Lemma lem129626 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129627 (m : nat) (k : nat) : (term152 m k) = (term152 m k).
Proof. exact (MK_COMB (@lem129626) (@lem129625 m k)). Qed.
Lemma lem129628 (P : nat -> Prop) : (term158 P) = (term159 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem129629 (m : nat) : (term167 m) = (term168 m).
Proof. exact (@lem129628 (term153 m)). Qed.
Lemma lem129630 (m : nat) (k : nat) : (term169 m k) = (term152 m k).
Proof. exact (eq_refl (term169 m k)). Qed.
Lemma lem129631 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem129632 (m : nat) (k : nat) : (term170 m k) = (term160 m k).
Proof. exact (MK_COMB (@lem129631) (@lem129630 m k)). Qed.
Lemma lem129633 (m : nat) (k : nat) : (term170 m k) = (term166 m k).
Proof. exact (TRANS (@lem129632 m k) (@lem129624 m k)). Qed.
Lemma lem129634 (m : nat) : (term171 m) = (term172 m).
Proof. exact (fun_ext (fun k : nat => @lem129633 m k)). Qed.
Lemma lem129635 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129636 (m : nat) : (term168 m) = (term173 m).
Proof. exact (MK_COMB (@lem129635) (@lem129634 m)). Qed.
Lemma lem129637 (m : nat) : (term167 m) = (term173 m).
Proof. exact (TRANS (@lem129629 m) (@lem129636 m)). Qed.
Lemma lem129638 (m : nat) : (term153 m) = (term153 m).
Proof. exact (fun_ext (fun k : nat => @lem129627 m k)). Qed.
Lemma lem129639 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129640 (m : nat) : (term52 m) = (term52 m).
Proof. exact (MK_COMB (@lem129639) (@lem129638 m)). Qed.
Lemma lem129641 (m : nat) : (term37 m) = (term37 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem129644 (m : nat) : (term174 m) = (m = (NUMERAL 0)).
Proof. exact (@lem16933 (m = (NUMERAL 0))). Qed.
Lemma lem129645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem129646 (m : nat) : (term175 m) = (term176 m).
Proof. exact (MK_COMB (@lem129645) (@lem129637 m)). Qed.
Lemma lem129647 (m : nat) : (term177 m) = (term178 m).
Proof. exact (MK_COMB (@lem129646 m) (@lem129641 m)). Qed.
Lemma lem129648 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem129649 (m : nat) : (term179 m) = (term179 m).
Proof. exact (MK_COMB (@lem129648) (@lem129640 m)). Qed.
Lemma lem129650 (m : nat) : (term180 m) = (term181 m).
Proof. exact (MK_COMB (@lem129649 m) (@lem129644 m)). Qed.
Lemma lem129651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem129652 (m : nat) : (term182 m) = (term183 m).
Proof. exact (MK_COMB (@lem129651) (@lem129650 m)). Qed.
Lemma lem129653 (m : nat) : (term184 m) = (term185 m).
Proof. exact (MK_COMB (@lem129652 m) (@lem129647 m)). Qed.
Lemma lem129654 (m : nat) : ((term52 m) = (term37 m)) = (term184 m).
Proof. exact (@lem17784 (term52 m) (term37 m)). Qed.
Lemma lem129655 (m : nat) : ((term52 m) = (term37 m)) = (term185 m).
Proof. exact (TRANS (@lem129654 m) (@lem129653 m)). Qed.
Lemma lem129657 (m : nat) (n : nat) : (term186 m n) = (term186 m n).
Proof. exact (eq_refl (term186 m n)). Qed.
Lemma lem129658 (n : nat) (m : nat) : (term187 n m) = (term188 n m).
Proof. exact (MK_COMB (@lem129657 m n) (@lem129655 m)). Qed.
Lemma lem129659 (n : nat) (m : nat) : (term55 n m) = (term187 n m).
Proof. exact (@lem17265 (Peano.lt m n) ((term52 m) = (term37 m))). Qed.
Lemma lem129660 (n : nat) (m : nat) : (term55 n m) = (term188 n m).
Proof. exact (TRANS (@lem129659 n m) (@lem129658 n m)). Qed.
Lemma lem129661 (n : nat) : (term57 n) = (term189 n).
Proof. exact (fun_ext (fun m : nat => @lem129660 n m)). Qed.
Lemma lem129662 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129663 (n : nat) : (term59 n) = (term190 n).
Proof. exact (MK_COMB (@lem129662) (@lem129661 n)). Qed.
Lemma lem129798 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem129799 (P : nat -> Prop) (Q : Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem129798 nat P Q). Qed.
Lemma lem129800 (m : nat) : (term195 m) = (term196 m).
Proof. exact (@lem129799 (term153 m) (m = (NUMERAL 0))). Qed.
Lemma lem129801 (m : nat) (k : nat) : (term169 m k) = (term152 m k).
Proof. exact (eq_refl (term169 m k)). Qed.
Lemma lem129802 (m : nat) : (term197 m) = (term153 m).
Proof. exact (fun_ext (fun k : nat => @lem129801 m k)). Qed.
Lemma lem129803 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129804 (m : nat) : (term198 m) = (term52 m).
Proof. exact (MK_COMB (@lem129803) (@lem129802 m)). Qed.
Lemma lem129805 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem129806 (m : nat) : (term199 m) = (term179 m).
Proof. exact (MK_COMB (@lem129805) (@lem129804 m)). Qed.
Lemma lem129807 (m : nat) : (m = (NUMERAL 0)) = (m = (NUMERAL 0)).
Proof. exact (eq_refl (m = (NUMERAL 0))). Qed.
Lemma lem129808 (m : nat) : (term195 m) = (term181 m).
Proof. exact (MK_COMB (@lem129806 m) (@lem129807 m)). Qed.
Lemma lem129809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem129810 (m : nat) : (term200 m) = (term201 m).
Proof. exact (MK_COMB (@lem129809) (@lem129808 m)). Qed.
Lemma lem129811 (m : nat) (k : nat) : (term169 m k) = (term152 m k).
Proof. exact (eq_refl (term169 m k)). Qed.
Lemma lem129812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem129813 (m : nat) (k : nat) : (term202 m k) = (term203 m k).
Proof. exact (MK_COMB (@lem129812) (@lem129811 m k)). Qed.
Lemma lem129814 (m : nat) : (m = (NUMERAL 0)) = (m = (NUMERAL 0)).
Proof. exact (eq_refl (m = (NUMERAL 0))). Qed.
Lemma lem129815 (k : nat) (m : nat) : (term204 k m) = (term205 k m).
Proof. exact (MK_COMB (@lem129813 m k) (@lem129814 m)). Qed.
Lemma lem129816 (m : nat) : (term206 m) = (term207 m).
Proof. exact (fun_ext (fun k : nat => @lem129815 k m)). Qed.
Lemma lem129817 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129818 (m : nat) : (term196 m) = (term208 m).
Proof. exact (MK_COMB (@lem129817) (@lem129816 m)). Qed.
Lemma lem129819 (m : nat) : ((term195 m) = (term196 m)) = ((term181 m) = (term208 m)).
Proof. exact (MK_COMB (@lem129810 m) (@lem129818 m)). Qed.
Lemma lem129820 (m : nat) : (term181 m) = (term208 m).
Proof. exact (EQ_MP (@lem129819 m) (@lem129800 m)). Qed.
Lemma lem129822 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem129823 (P : nat -> Prop) (Q : Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem129822 nat P Q). Qed.
Lemma lem129824 (k : nat) (m : nat) : (term209 k m) = (term210 k m).
Proof. exact (@lem129823 (term151 m k) (m = (NUMERAL 0))). Qed.
Lemma lem129825 (m : nat) (k : nat) (m' : nat) : (term162 m k m') = (term150 m k m').
Proof. exact (eq_refl (term162 m k m')). Qed.
Lemma lem129826 (m : nat) (k : nat) : (term211 m k) = (term151 m k).
Proof. exact (fun_ext (fun m' : nat => @lem129825 m k m')). Qed.
Lemma lem129827 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129828 (m : nat) (k : nat) : (term212 m k) = (term152 m k).
Proof. exact (MK_COMB (@lem129827) (@lem129826 m k)). Qed.
Lemma lem129829 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem129830 (m : nat) (k : nat) : (term213 m k) = (term203 m k).
Proof. exact (MK_COMB (@lem129829) (@lem129828 m k)). Qed.
Lemma lem129831 (m : nat) : (m = (NUMERAL 0)) = (m = (NUMERAL 0)).
Proof. exact (eq_refl (m = (NUMERAL 0))). Qed.
Lemma lem129832 (k : nat) (m : nat) : (term209 k m) = (term205 k m).
Proof. exact (MK_COMB (@lem129830 m k) (@lem129831 m)). Qed.
Lemma lem129833 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem129834 (k : nat) (m : nat) : (term214 k m) = (term215 k m).
Proof. exact (MK_COMB (@lem129833) (@lem129832 k m)). Qed.
Lemma lem129835 (m : nat) (k : nat) (m' : nat) : (term162 m k m') = (term150 m k m').
Proof. exact (eq_refl (term162 m k m')). Qed.
Lemma lem129836 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem129837 (m : nat) (k : nat) (m' : nat) : (term216 m k m') = (term217 m k m').
Proof. exact (MK_COMB (@lem129836) (@lem129835 m k m')). Qed.
Lemma lem129838 (m : nat) : (m = (NUMERAL 0)) = (m = (NUMERAL 0)).
Proof. exact (eq_refl (m = (NUMERAL 0))). Qed.
Lemma lem129839 (k : nat) (m' : nat) (m : nat) : (term218 k m' m) = (term219 k m' m).
Proof. exact (MK_COMB (@lem129837 m k m') (@lem129838 m)). Qed.
Lemma lem129840 (k : nat) (m : nat) : (term220 k m) = (term221 k m).
Proof. exact (fun_ext (fun m' : nat => @lem129839 k m' m)). Qed.
Lemma lem129841 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129842 (k : nat) (m : nat) : (term210 k m) = (term222 k m).
Proof. exact (MK_COMB (@lem129841) (@lem129840 k m)). Qed.
Lemma lem129843 (k : nat) (m : nat) : ((term209 k m) = (term210 k m)) = ((term205 k m) = (term222 k m)).
Proof. exact (MK_COMB (@lem129834 k m) (@lem129842 k m)). Qed.
Lemma lem129844 (k : nat) (m : nat) : (term205 k m) = (term222 k m).
Proof. exact (EQ_MP (@lem129843 k m) (@lem129824 k m)). Qed.
Lemma lem129845 (m : nat) : (term207 m) = (term223 m).
Proof. exact (fun_ext (fun k : nat => @lem129844 k m)). Qed.
Lemma lem129846 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129847 (m : nat) : (term208 m) = (term224 m).
Proof. exact (MK_COMB (@lem129846) (@lem129845 m)). Qed.
Lemma lem129848 (m : nat) : (term181 m) = (term224 m).
Proof. exact (TRANS (@lem129820 m) (@lem129847 m)). Qed.
Lemma lem129849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem129850 (m : nat) : (term183 m) = (term225 m).
Proof. exact (MK_COMB (@lem129849) (@lem129848 m)). Qed.
Lemma lem129851 (m : nat) : (term178 m) = (term178 m).
Proof. exact (eq_refl (term178 m)). Qed.
Lemma lem129852 (m : nat) : (term185 m) = (term226 m).
Proof. exact (MK_COMB (@lem129850 m) (@lem129851 m)). Qed.
Lemma lem129854 {A : Type'} (P : A -> Prop) (Q : Prop) : (term227 A P Q) = (term228 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem129855 (P : nat -> Prop) (Q : Prop) : (term229 P Q) = (term230 P Q).
Proof. exact (@lem129854 nat P Q). Qed.
Lemma lem129856 (m : nat) : (term231 m) = (term232 m).
Proof. exact (@lem129855 (term223 m) (term178 m)). Qed.
Lemma lem129857 (k : nat) (m : nat) : (term233 m k) = (term222 k m).
Proof. exact (eq_refl (term233 m k)). Qed.
Lemma lem129858 (m : nat) : (term234 m) = (term223 m).
Proof. exact (fun_ext (fun k : nat => @lem129857 k m)). Qed.
Lemma lem129859 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129860 (m : nat) : (term235 m) = (term224 m).
Proof. exact (MK_COMB (@lem129859) (@lem129858 m)). Qed.
Lemma lem129861 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem129862 (m : nat) : (term236 m) = (term225 m).
Proof. exact (MK_COMB (@lem129861) (@lem129860 m)). Qed.
Lemma lem129863 (m : nat) : (term178 m) = (term178 m).
Proof. exact (eq_refl (term178 m)). Qed.
Lemma lem129864 (m : nat) : (term231 m) = (term226 m).
Proof. exact (MK_COMB (@lem129862 m) (@lem129863 m)). Qed.
Lemma lem129865 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem129866 (m : nat) : (term237 m) = (term238 m).
Proof. exact (MK_COMB (@lem129865) (@lem129864 m)). Qed.
Lemma lem129867 (k : nat) (m : nat) : (term233 m k) = (term222 k m).
Proof. exact (eq_refl (term233 m k)). Qed.
Lemma lem129868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem129869 (k : nat) (m : nat) : (term239 m k) = (term240 k m).
Proof. exact (MK_COMB (@lem129868) (@lem129867 k m)). Qed.
Lemma lem129870 (m : nat) : (term178 m) = (term178 m).
Proof. exact (eq_refl (term178 m)). Qed.
Lemma lem129871 (k : nat) (m : nat) : (term241 k m) = (term242 k m).
Proof. exact (MK_COMB (@lem129869 k m) (@lem129870 m)). Qed.
Lemma lem129872 (m : nat) : (term243 m) = (term244 m).
Proof. exact (fun_ext (fun k : nat => @lem129871 k m)). Qed.
Lemma lem129873 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129874 (m : nat) : (term232 m) = (term245 m).
Proof. exact (MK_COMB (@lem129873) (@lem129872 m)). Qed.
Lemma lem129875 (m : nat) : ((term231 m) = (term232 m)) = ((term226 m) = (term245 m)).
Proof. exact (MK_COMB (@lem129866 m) (@lem129874 m)). Qed.
Lemma lem129876 (m : nat) : (term226 m) = (term245 m).
Proof. exact (EQ_MP (@lem129875 m) (@lem129856 m)). Qed.
Lemma lem129878 {A : Type'} (P : A -> Prop) (Q : Prop) : (term227 A P Q) = (term228 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem129879 (P : nat -> Prop) (Q : Prop) : (term229 P Q) = (term230 P Q).
Proof. exact (@lem129878 nat P Q). Qed.
Lemma lem129880 (k : nat) (m : nat) : (term246 k m) = (term247 k m).
Proof. exact (@lem129879 (term221 k m) (term178 m)). Qed.
Lemma lem129881 (k : nat) (m' : nat) (m : nat) : (term248 k m m') = (term219 k m' m).
Proof. exact (eq_refl (term248 k m m')). Qed.
Lemma lem129882 (k : nat) (m : nat) : (term249 k m) = (term221 k m).
Proof. exact (fun_ext (fun m' : nat => @lem129881 k m' m)). Qed.
Lemma lem129883 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129884 (k : nat) (m : nat) : (term250 k m) = (term222 k m).
Proof. exact (MK_COMB (@lem129883) (@lem129882 k m)). Qed.
Lemma lem129885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem129886 (k : nat) (m : nat) : (term251 k m) = (term240 k m).
Proof. exact (MK_COMB (@lem129885) (@lem129884 k m)). Qed.
Lemma lem129887 (m : nat) : (term178 m) = (term178 m).
Proof. exact (eq_refl (term178 m)). Qed.
Lemma lem129888 (k : nat) (m : nat) : (term246 k m) = (term242 k m).
Proof. exact (MK_COMB (@lem129886 k m) (@lem129887 m)). Qed.
Lemma lem129889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem129890 (k : nat) (m : nat) : (term252 k m) = (term253 k m).
Proof. exact (MK_COMB (@lem129889) (@lem129888 k m)). Qed.
Lemma lem129891 (k : nat) (m' : nat) (m : nat) : (term248 k m m') = (term219 k m' m).
Proof. exact (eq_refl (term248 k m m')). Qed.
Lemma lem129892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem129893 (k : nat) (m' : nat) (m : nat) : (term254 k m m') = (term255 k m' m).
Proof. exact (MK_COMB (@lem129892) (@lem129891 k m' m)). Qed.
Lemma lem129894 (m : nat) : (term178 m) = (term178 m).
Proof. exact (eq_refl (term178 m)). Qed.
Lemma lem129895 (k : nat) (m' : nat) (m : nat) : (term256 k m' m) = (term257 k m' m).
Proof. exact (MK_COMB (@lem129893 k m' m) (@lem129894 m)). Qed.
Lemma lem129896 (k : nat) (m : nat) : (term258 k m) = (term259 k m).
Proof. exact (fun_ext (fun m' : nat => @lem129895 k m' m)). Qed.
Lemma lem129897 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129898 (k : nat) (m : nat) : (term247 k m) = (term260 k m).
Proof. exact (MK_COMB (@lem129897) (@lem129896 k m)). Qed.
Lemma lem129899 (k : nat) (m : nat) : ((term246 k m) = (term247 k m)) = ((term242 k m) = (term260 k m)).
Proof. exact (MK_COMB (@lem129890 k m) (@lem129898 k m)). Qed.
Lemma lem129900 (k : nat) (m : nat) : (term242 k m) = (term260 k m).
Proof. exact (EQ_MP (@lem129899 k m) (@lem129880 k m)). Qed.
Lemma lem129901 (m : nat) : (term244 m) = (term261 m).
Proof. exact (fun_ext (fun k : nat => @lem129900 k m)). Qed.
Lemma lem129902 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129903 (m : nat) : (term245 m) = (term262 m).
Proof. exact (MK_COMB (@lem129902) (@lem129901 m)). Qed.
Lemma lem129904 (m : nat) : (term226 m) = (term262 m).
Proof. exact (TRANS (@lem129876 m) (@lem129903 m)). Qed.
Lemma lem129905 (m : nat) : (term185 m) = (term262 m).
Proof. exact (TRANS (@lem129852 m) (@lem129904 m)). Qed.
Lemma lem129906 (m : nat) (n : nat) : (term186 m n) = (term186 m n).
Proof. exact (eq_refl (term186 m n)). Qed.
Lemma lem129907 (n : nat) (m : nat) : (term188 n m) = (term263 n m).
Proof. exact (MK_COMB (@lem129906 m n) (@lem129905 m)). Qed.
Lemma lem129909 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem129910 (P : Prop) (Q : nat -> Prop) : (term266 P Q) = (term267 P Q).
Proof. exact (@lem129909 nat P Q). Qed.
Lemma lem129911 (n : nat) (m : nat) : (term268 n m) = (term269 n m).
Proof. exact (@lem129910 (term270 m n) (term261 m)). Qed.
Lemma lem129912 (k : nat) (m : nat) : (term271 m k) = (term260 k m).
Proof. exact (eq_refl (term271 m k)). Qed.
Lemma lem129913 (m : nat) : (term272 m) = (term261 m).
Proof. exact (fun_ext (fun k : nat => @lem129912 k m)). Qed.
Lemma lem129914 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129915 (m : nat) : (term273 m) = (term262 m).
Proof. exact (MK_COMB (@lem129914) (@lem129913 m)). Qed.
Lemma lem129916 (m : nat) (n : nat) : (term186 m n) = (term186 m n).
Proof. exact (eq_refl (term186 m n)). Qed.
Lemma lem129917 (n : nat) (m : nat) : (term268 n m) = (term263 n m).
Proof. exact (MK_COMB (@lem129916 m n) (@lem129915 m)). Qed.
Lemma lem129918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem129919 (n : nat) (m : nat) : (term274 n m) = (term275 n m).
Proof. exact (MK_COMB (@lem129918) (@lem129917 n m)). Qed.
Lemma lem129920 (k : nat) (m : nat) : (term271 m k) = (term260 k m).
Proof. exact (eq_refl (term271 m k)). Qed.
Lemma lem129921 (m : nat) (n : nat) : (term186 m n) = (term186 m n).
Proof. exact (eq_refl (term186 m n)). Qed.
Lemma lem129922 (n : nat) (k : nat) (m : nat) : (term276 n m k) = (term277 n k m).
Proof. exact (MK_COMB (@lem129921 m n) (@lem129920 k m)). Qed.
Lemma lem129923 (n : nat) (m : nat) : (term278 n m) = (term279 n m).
Proof. exact (fun_ext (fun k : nat => @lem129922 n k m)). Qed.
Lemma lem129924 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129925 (n : nat) (m : nat) : (term269 n m) = (term280 n m).
Proof. exact (MK_COMB (@lem129924) (@lem129923 n m)). Qed.
Lemma lem129926 (n : nat) (m : nat) : ((term268 n m) = (term269 n m)) = ((term263 n m) = (term280 n m)).
Proof. exact (MK_COMB (@lem129919 n m) (@lem129925 n m)). Qed.
Lemma lem129927 (n : nat) (m : nat) : (term263 n m) = (term280 n m).
Proof. exact (EQ_MP (@lem129926 n m) (@lem129911 n m)). Qed.
Lemma lem129929 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem129930 (P : Prop) (Q : nat -> Prop) : (term266 P Q) = (term267 P Q).
Proof. exact (@lem129929 nat P Q). Qed.
Lemma lem129931 (n : nat) (k : nat) (m : nat) : (term281 n k m) = (term282 n k m).
Proof. exact (@lem129930 (term270 m n) (term259 k m)). Qed.
Lemma lem129932 (k : nat) (m' : nat) (m : nat) : (term283 k m m') = (term257 k m' m).
Proof. exact (eq_refl (term283 k m m')). Qed.
Lemma lem129933 (k : nat) (m : nat) : (term284 k m) = (term259 k m).
Proof. exact (fun_ext (fun m' : nat => @lem129932 k m' m)). Qed.
Lemma lem129934 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129935 (k : nat) (m : nat) : (term285 k m) = (term260 k m).
Proof. exact (MK_COMB (@lem129934) (@lem129933 k m)). Qed.
Lemma lem129936 (m : nat) (n : nat) : (term186 m n) = (term186 m n).
Proof. exact (eq_refl (term186 m n)). Qed.
Lemma lem129937 (n : nat) (k : nat) (m : nat) : (term281 n k m) = (term277 n k m).
Proof. exact (MK_COMB (@lem129936 m n) (@lem129935 k m)). Qed.
Lemma lem129938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem129939 (n : nat) (k : nat) (m : nat) : (term286 n k m) = (term287 n k m).
Proof. exact (MK_COMB (@lem129938) (@lem129937 n k m)). Qed.
Lemma lem129940 (k : nat) (m' : nat) (m : nat) : (term283 k m m') = (term257 k m' m).
Proof. exact (eq_refl (term283 k m m')). Qed.
Lemma lem129941 (m : nat) (n : nat) : (term186 m n) = (term186 m n).
Proof. exact (eq_refl (term186 m n)). Qed.
Lemma lem129942 (n : nat) (k : nat) (m' : nat) (m : nat) : (term288 n k m m') = (term289 n k m' m).
Proof. exact (MK_COMB (@lem129941 m n) (@lem129940 k m' m)). Qed.
Lemma lem129943 (n : nat) (k : nat) (m : nat) : (term290 n k m) = (term291 n k m).
Proof. exact (fun_ext (fun m' : nat => @lem129942 n k m' m)). Qed.
Lemma lem129944 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129945 (n : nat) (k : nat) (m : nat) : (term282 n k m) = (term292 n k m).
Proof. exact (MK_COMB (@lem129944) (@lem129943 n k m)). Qed.
Lemma lem129946 (n : nat) (k : nat) (m : nat) : ((term281 n k m) = (term282 n k m)) = ((term277 n k m) = (term292 n k m)).
Proof. exact (MK_COMB (@lem129939 n k m) (@lem129945 n k m)). Qed.
Lemma lem129947 (n : nat) (k : nat) (m : nat) : (term277 n k m) = (term292 n k m).
Proof. exact (EQ_MP (@lem129946 n k m) (@lem129931 n k m)). Qed.
Lemma lem129948 (n : nat) (m : nat) : (term279 n m) = (term293 n m).
Proof. exact (fun_ext (fun k : nat => @lem129947 n k m)). Qed.
Lemma lem129949 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129950 (n : nat) (m : nat) : (term280 n m) = (term294 n m).
Proof. exact (MK_COMB (@lem129949) (@lem129948 n m)). Qed.
Lemma lem129951 (n : nat) (m : nat) : (term263 n m) = (term294 n m).
Proof. exact (TRANS (@lem129927 n m) (@lem129950 n m)). Qed.
Lemma lem129952 (n : nat) (m : nat) : (term188 n m) = (term294 n m).
Proof. exact (TRANS (@lem129907 n m) (@lem129951 n m)). Qed.
Lemma lem129953 (n : nat) : (term189 n) = (term295 n).
Proof. exact (fun_ext (fun m : nat => @lem129952 n m)). Qed.
Lemma lem129954 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129955 (n : nat) : (term190 n) = (term296 n).
Proof. exact (MK_COMB (@lem129954) (@lem129953 n)). Qed.
Lemma lem129957 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem129958 (P : type1605) : (term299 P) = (term300 P).
Proof. exact (@lem129957 nat nat P). Qed.
Lemma lem129959 (n : nat) : (term301 n) = (term302 n).
Proof. exact (@lem129958 (term303 n)). Qed.
Lemma lem129960 (n : nat) (m : nat) : (term304 n m) = (term293 n m).
Proof. exact (eq_refl (term304 n m)). Qed.
Lemma lem129961 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem129962 (n : nat) (m : nat) (k : nat) : (term305 n m k) = (term306 n m k).
Proof. exact (MK_COMB (@lem129960 n m) (@lem129961 k)). Qed.
Lemma lem129963 (n : nat) (k : nat) (m : nat) : (term306 n m k) = (term292 n k m).
Proof. exact (eq_refl (term306 n m k)). Qed.
Lemma lem129964 (n : nat) (k : nat) (m : nat) : (term305 n m k) = (term292 n k m).
Proof. exact (TRANS (@lem129962 n m k) (@lem129963 n k m)). Qed.
Lemma lem129965 (n : nat) (m : nat) : (term307 n m) = (term293 n m).
Proof. exact (fun_ext (fun k : nat => @lem129964 n k m)). Qed.
Lemma lem129966 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129967 (n : nat) (m : nat) : (term308 n m) = (term294 n m).
Proof. exact (MK_COMB (@lem129966) (@lem129965 n m)). Qed.
Lemma lem129968 (n : nat) : (term309 n) = (term295 n).
Proof. exact (fun_ext (fun m : nat => @lem129967 n m)). Qed.
Lemma lem129969 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129970 (n : nat) : (term301 n) = (term296 n).
Proof. exact (MK_COMB (@lem129969) (@lem129968 n)). Qed.
Lemma lem129971 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem129972 (n : nat) : (term310 n) = (term311 n).
Proof. exact (MK_COMB (@lem129971) (@lem129970 n)). Qed.
Lemma lem129973 (n : nat) (m : nat) : (term304 n m) = (term293 n m).
Proof. exact (eq_refl (term304 n m)). Qed.
Lemma lem129974 (k : nat -> nat) (m : nat) : (k m) = (k m).
Proof. exact (eq_refl (k m)). Qed.
Lemma lem129975 (n : nat) (k : nat -> nat) (m : nat) : (term312 n k m) = (term313 n k m).
Proof. exact (MK_COMB (@lem129973 n m) (@lem129974 k m)). Qed.
Lemma lem129976 (n : nat) (k : nat -> nat) (m : nat) : (term313 n k m) = (term314 n k m).
Proof. exact (eq_refl (term313 n k m)). Qed.
Lemma lem129977 (n : nat) (k : nat -> nat) (m : nat) : (term312 n k m) = (term314 n k m).
Proof. exact (TRANS (@lem129975 n k m) (@lem129976 n k m)). Qed.
Lemma lem129978 (n : nat) (k : nat -> nat) : (term315 n k) = (term316 n k).
Proof. exact (fun_ext (fun m : nat => @lem129977 n k m)). Qed.
Lemma lem129979 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem129980 (n : nat) (k : nat -> nat) : (term317 n k) = (term318 n k).
Proof. exact (MK_COMB (@lem129979) (@lem129978 n k)). Qed.
Lemma lem129981 (n : nat) : (term319 n) = (term320 n).
Proof. exact (fun_ext (fun k : nat -> nat => @lem129980 n k)). Qed.
Lemma lem129982 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem129983 (n : nat) : (term302 n) = (term321 n).
Proof. exact (MK_COMB (@lem129982) (@lem129981 n)). Qed.
Lemma lem129984 (n : nat) : ((term301 n) = (term302 n)) = ((term296 n) = (term321 n)).
Proof. exact (MK_COMB (@lem129972 n) (@lem129983 n)). Qed.
Lemma lem129985 (n : nat) : (term296 n) = (term321 n).
Proof. exact (EQ_MP (@lem129984 n) (@lem129959 n)). Qed.
Lemma lem129987 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem129988 (P : type1605) : (term299 P) = (term300 P).
Proof. exact (@lem129987 nat nat P). Qed.
Lemma lem129989 (n : nat) (k : nat -> nat) : (term322 n k) = (term323 n k).
Proof. exact (@lem129988 (term324 n k)). Qed.
Lemma lem129990 (n : nat) (k : nat -> nat) (m : nat) : (term325 n k m) = (term326 n k m).
Proof. exact (eq_refl (term325 n k m)). Qed.
Lemma lem129991 (m' : nat) : m' = m'.
Proof. exact (eq_refl m'). Qed.
Lemma lem129992 (n : nat) (k : nat -> nat) (m : nat) (m' : nat) : (term327 n k m m') = (term328 n k m m').
Proof. exact (MK_COMB (@lem129990 n k m) (@lem129991 m')). Qed.
Lemma lem129993 (n : nat) (k : nat -> nat) (m' : nat) (m : nat) : (term328 n k m m') = (term329 n k m' m).
Proof. exact (eq_refl (term328 n k m m')). Qed.
Lemma lem129994 (n : nat) (k : nat -> nat) (m' : nat) (m : nat) : (term327 n k m m') = (term329 n k m' m).
Proof. exact (TRANS (@lem129992 n k m m') (@lem129993 n k m' m)). Qed.
Lemma lem129995 (n : nat) (k : nat -> nat) (m : nat) : (term330 n k m) = (term326 n k m).
Proof. exact (fun_ext (fun m' : nat => @lem129994 n k m' m)). Qed.
Lemma lem129996 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem129997 (n : nat) (k : nat -> nat) (m : nat) : (term331 n k m) = (term314 n k m).
Proof. exact (MK_COMB (@lem129996) (@lem129995 n k m)). Qed.
Lemma lem129998 (n : nat) (k : nat -> nat) : (term332 n k) = (term316 n k).
Proof. exact (fun_ext (fun m : nat => @lem129997 n k m)). Qed.
Lemma lem129999 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130000 (n : nat) (k : nat -> nat) : (term322 n k) = (term318 n k).
Proof. exact (MK_COMB (@lem129999) (@lem129998 n k)). Qed.
Lemma lem130001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem130002 (n : nat) (k : nat -> nat) : (term333 n k) = (term334 n k).
Proof. exact (MK_COMB (@lem130001) (@lem130000 n k)). Qed.
Lemma lem130003 (n : nat) (k : nat -> nat) (m : nat) : (term325 n k m) = (term326 n k m).
Proof. exact (eq_refl (term325 n k m)). Qed.
Lemma lem130004 (m' : nat -> nat) (m : nat) : (m' m) = (m' m).
Proof. exact (eq_refl (m' m)). Qed.
Lemma lem130005 (n : nat) (k : nat -> nat) (m' : nat -> nat) (m : nat) : (term335 n k m' m) = (term336 n k m' m).
Proof. exact (MK_COMB (@lem130003 n k m) (@lem130004 m' m)). Qed.
Lemma lem130006 (n : nat) (k : nat -> nat) (m' : nat -> nat) (m : nat) : (term336 n k m' m) = (term337 n k m' m).
Proof. exact (eq_refl (term336 n k m' m)). Qed.
Lemma lem130007 (n : nat) (k : nat -> nat) (m' : nat -> nat) (m : nat) : (term335 n k m' m) = (term337 n k m' m).
Proof. exact (TRANS (@lem130005 n k m' m) (@lem130006 n k m' m)). Qed.
Lemma lem130008 (n : nat) (k : nat -> nat) (m' : nat -> nat) : (term338 n k m') = (term339 n k m').
Proof. exact (fun_ext (fun m : nat => @lem130007 n k m' m)). Qed.
Lemma lem130009 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130010 (n : nat) (k : nat -> nat) (m' : nat -> nat) : (term340 n k m') = (term341 n k m').
Proof. exact (MK_COMB (@lem130009) (@lem130008 n k m')). Qed.
Lemma lem130011 (n : nat) (k : nat -> nat) : (term342 n k) = (term343 n k).
Proof. exact (fun_ext (fun m' : nat -> nat => @lem130010 n k m')). Qed.
Lemma lem130012 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem130013 (n : nat) (k : nat -> nat) : (term323 n k) = (term344 n k).
Proof. exact (MK_COMB (@lem130012) (@lem130011 n k)). Qed.
Lemma lem130014 (n : nat) (k : nat -> nat) : ((term322 n k) = (term323 n k)) = ((term318 n k) = (term344 n k)).
Proof. exact (MK_COMB (@lem130002 n k) (@lem130013 n k)). Qed.
Lemma lem130015 (n : nat) (k : nat -> nat) : (term318 n k) = (term344 n k).
Proof. exact (EQ_MP (@lem130014 n k) (@lem129989 n k)). Qed.
Lemma lem130016 (n : nat) : (term320 n) = (term345 n).
Proof. exact (fun_ext (fun k : nat -> nat => @lem130015 n k)). Qed.
Lemma lem130017 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem130018 (n : nat) : (term321 n) = (term346 n).
Proof. exact (MK_COMB (@lem130017) (@lem130016 n)). Qed.
Lemma lem130019 (n : nat) : (term296 n) = (term346 n).
Proof. exact (TRANS (@lem129985 n) (@lem130018 n)). Qed.
Lemma lem130021 (n : nat) : (term190 n) = (term346 n).
Proof. exact (TRANS (@lem129955 n) (@lem130019 n)). Qed.
Lemma lem130022 (n : nat) : (term59 n) = (term346 n).
Proof. exact (TRANS (@lem129663 n) (@lem130021 n)). Qed.
Lemma lem130023 (n : nat) (h1 : term59 n) : term346 n.
Proof. exact (EQ_MP (@lem130022 n) (@lem129596 n h1)). Qed.
Lemma lem130029 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem130038 (n : nat) (k : nat) (m : nat) : (term155 n k m) = (term156 n k m).
Proof. exact (@lem17045 (Coq.Arith.PeanoNat.Nat.Odd m) (n = (term157 k m))). Qed.
Lemma lem130041 (n : nat) (k : nat) (m : nat) : (term150 n k m) = (term150 n k m).
Proof. exact (eq_refl (term150 n k m)). Qed.
Lemma lem130042 (P : nat -> Prop) : (term158 P) = (term159 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem130043 (n : nat) (k : nat) : (term160 n k) = (term161 n k).
Proof. exact (@lem130042 (term151 n k)). Qed.
Lemma lem130044 (n : nat) (k : nat) (m : nat) : (term162 n k m) = (term150 n k m).
Proof. exact (eq_refl (term162 n k m)). Qed.
Lemma lem130045 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem130046 (n : nat) (k : nat) (m : nat) : (term163 n k m) = (term155 n k m).
Proof. exact (MK_COMB (@lem130045) (@lem130044 n k m)). Qed.
Lemma lem130047 (n : nat) (k : nat) (m : nat) : (term163 n k m) = (term156 n k m).
Proof. exact (TRANS (@lem130046 n k m) (@lem130038 n k m)). Qed.
Lemma lem130048 (n : nat) (k : nat) : (term164 n k) = (term165 n k).
Proof. exact (fun_ext (fun m : nat => @lem130047 n k m)). Qed.
Lemma lem130049 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130050 (n : nat) (k : nat) : (term161 n k) = (term166 n k).
Proof. exact (MK_COMB (@lem130049) (@lem130048 n k)). Qed.
Lemma lem130051 (n : nat) (k : nat) : (term160 n k) = (term166 n k).
Proof. exact (TRANS (@lem130043 n k) (@lem130050 n k)). Qed.
Lemma lem130052 (n : nat) (k : nat) : (term151 n k) = (term151 n k).
Proof. exact (fun_ext (fun m : nat => @lem130041 n k m)). Qed.
Lemma lem130053 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem130054 (n : nat) (k : nat) : (term152 n k) = (term152 n k).
Proof. exact (MK_COMB (@lem130053) (@lem130052 n k)). Qed.
Lemma lem130055 (P : nat -> Prop) : (term158 P) = (term159 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem130056 (n : nat) : (term167 n) = (term168 n).
Proof. exact (@lem130055 (term153 n)). Qed.
Lemma lem130057 (n : nat) (k : nat) : (term169 n k) = (term152 n k).
Proof. exact (eq_refl (term169 n k)). Qed.
Lemma lem130058 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem130059 (n : nat) (k : nat) : (term170 n k) = (term160 n k).
Proof. exact (MK_COMB (@lem130058) (@lem130057 n k)). Qed.
Lemma lem130060 (n : nat) (k : nat) : (term170 n k) = (term166 n k).
Proof. exact (TRANS (@lem130059 n k) (@lem130051 n k)). Qed.
Lemma lem130061 (n : nat) : (term171 n) = (term172 n).
Proof. exact (fun_ext (fun k : nat => @lem130060 n k)). Qed.
Lemma lem130062 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130063 (n : nat) : (term168 n) = (term173 n).
Proof. exact (MK_COMB (@lem130062) (@lem130061 n)). Qed.
Lemma lem130064 (n : nat) : (term167 n) = (term173 n).
Proof. exact (TRANS (@lem130056 n) (@lem130063 n)). Qed.
Lemma lem130065 (n : nat) : (term153 n) = (term153 n).
Proof. exact (fun_ext (fun k : nat => @lem130054 n k)). Qed.
Lemma lem130066 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem130067 (n : nat) : (term52 n) = (term52 n).
Proof. exact (MK_COMB (@lem130066) (@lem130065 n)). Qed.
Lemma lem130068 (n : nat) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem130071 (n : nat) : (term174 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem130072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130073 (n : nat) : (term347 n) = (term348 n).
Proof. exact (MK_COMB (@lem130072) (@lem130064 n)). Qed.
Lemma lem130074 (n : nat) : (term349 n) = (term350 n).
Proof. exact (MK_COMB (@lem130073 n) (@lem130068 n)). Qed.
Lemma lem130075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130076 (n : nat) : (term351 n) = (term351 n).
Proof. exact (MK_COMB (@lem130075) (@lem130067 n)). Qed.
Lemma lem130077 (n : nat) : (term352 n) = (term353 n).
Proof. exact (MK_COMB (@lem130076 n) (@lem130071 n)). Qed.
Lemma lem130078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem130079 (n : nat) : (term354 n) = (term355 n).
Proof. exact (MK_COMB (@lem130078) (@lem130077 n)). Qed.
Lemma lem130080 (n : nat) : (term356 n) = (term357 n).
Proof. exact (MK_COMB (@lem130079 n) (@lem130074 n)). Qed.
Lemma lem130081 (n : nat) : (term76 n) = (term356 n).
Proof. exact (@lem17646 (term52 n) (term37 n)). Qed.
Lemma lem130082 (n : nat) : (term76 n) = (term357 n).
Proof. exact (TRANS (@lem130081 n) (@lem130080 n)). Qed.
Lemma lem130169 {A : Type'} (P : A -> Prop) (Q : Prop) : (term227 A P Q) = (term228 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem130170 (P : nat -> Prop) (Q : Prop) : (term229 P Q) = (term230 P Q).
Proof. exact (@lem130169 nat P Q). Qed.
Lemma lem130171 (n : nat) : (term358 n) = (term359 n).
Proof. exact (@lem130170 (term153 n) (n = (NUMERAL 0))). Qed.
Lemma lem130172 (n : nat) (k : nat) : (term169 n k) = (term152 n k).
Proof. exact (eq_refl (term169 n k)). Qed.
Lemma lem130173 (n : nat) : (term197 n) = (term153 n).
Proof. exact (fun_ext (fun k : nat => @lem130172 n k)). Qed.
Lemma lem130174 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem130175 (n : nat) : (term198 n) = (term52 n).
Proof. exact (MK_COMB (@lem130174) (@lem130173 n)). Qed.
Lemma lem130176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130177 (n : nat) : (term360 n) = (term351 n).
Proof. exact (MK_COMB (@lem130176) (@lem130175 n)). Qed.
Lemma lem130178 (n : nat) : (n = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (n = (NUMERAL 0))). Qed.
Lemma lem130179 (n : nat) : (term358 n) = (term353 n).
Proof. exact (MK_COMB (@lem130177 n) (@lem130178 n)). Qed.
Lemma lem130180 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem130181 (n : nat) : (term361 n) = (term362 n).
Proof. exact (MK_COMB (@lem130180) (@lem130179 n)). Qed.
Lemma lem130182 (n : nat) (k : nat) : (term169 n k) = (term152 n k).
Proof. exact (eq_refl (term169 n k)). Qed.
Lemma lem130183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130184 (n : nat) (k : nat) : (term363 n k) = (term364 n k).
Proof. exact (MK_COMB (@lem130183) (@lem130182 n k)). Qed.
Lemma lem130185 (n : nat) : (n = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (n = (NUMERAL 0))). Qed.
Lemma lem130186 (k : nat) (n : nat) : (term365 k n) = (term366 k n).
Proof. exact (MK_COMB (@lem130184 n k) (@lem130185 n)). Qed.
Lemma lem130187 (n : nat) : (term367 n) = (term368 n).
Proof. exact (fun_ext (fun k : nat => @lem130186 k n)). Qed.
Lemma lem130188 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem130189 (n : nat) : (term359 n) = (term369 n).
Proof. exact (MK_COMB (@lem130188) (@lem130187 n)). Qed.
Lemma lem130190 (n : nat) : ((term358 n) = (term359 n)) = ((term353 n) = (term369 n)).
Proof. exact (MK_COMB (@lem130181 n) (@lem130189 n)). Qed.
Lemma lem130191 (n : nat) : (term353 n) = (term369 n).
Proof. exact (EQ_MP (@lem130190 n) (@lem130171 n)). Qed.
Lemma lem130193 {A : Type'} (P : A -> Prop) (Q : Prop) : (term227 A P Q) = (term228 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem130194 (P : nat -> Prop) (Q : Prop) : (term229 P Q) = (term230 P Q).
Proof. exact (@lem130193 nat P Q). Qed.
Lemma lem130195 (k : nat) (n : nat) : (term370 k n) = (term371 k n).
Proof. exact (@lem130194 (term151 n k) (n = (NUMERAL 0))). Qed.
Lemma lem130196 (n : nat) (k : nat) (m : nat) : (term162 n k m) = (term150 n k m).
Proof. exact (eq_refl (term162 n k m)). Qed.
Lemma lem130197 (n : nat) (k : nat) : (term211 n k) = (term151 n k).
Proof. exact (fun_ext (fun m : nat => @lem130196 n k m)). Qed.
Lemma lem130198 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem130199 (n : nat) (k : nat) : (term212 n k) = (term152 n k).
Proof. exact (MK_COMB (@lem130198) (@lem130197 n k)). Qed.
Lemma lem130200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130201 (n : nat) (k : nat) : (term372 n k) = (term364 n k).
Proof. exact (MK_COMB (@lem130200) (@lem130199 n k)). Qed.
Lemma lem130202 (n : nat) : (n = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (n = (NUMERAL 0))). Qed.
Lemma lem130203 (k : nat) (n : nat) : (term370 k n) = (term366 k n).
Proof. exact (MK_COMB (@lem130201 n k) (@lem130202 n)). Qed.
Lemma lem130204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem130205 (k : nat) (n : nat) : (term373 k n) = (term374 k n).
Proof. exact (MK_COMB (@lem130204) (@lem130203 k n)). Qed.
Lemma lem130206 (n : nat) (k : nat) (m : nat) : (term162 n k m) = (term150 n k m).
Proof. exact (eq_refl (term162 n k m)). Qed.
Lemma lem130207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130208 (n : nat) (k : nat) (m : nat) : (term375 n k m) = (term376 n k m).
Proof. exact (MK_COMB (@lem130207) (@lem130206 n k m)). Qed.
Lemma lem130209 (n : nat) : (n = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (n = (NUMERAL 0))). Qed.
Lemma lem130210 (k : nat) (m : nat) (n : nat) : (term377 k m n) = (term378 k m n).
Proof. exact (MK_COMB (@lem130208 n k m) (@lem130209 n)). Qed.
Lemma lem130211 (k : nat) (n : nat) : (term379 k n) = (term380 k n).
Proof. exact (fun_ext (fun m : nat => @lem130210 k m n)). Qed.
Lemma lem130212 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem130213 (k : nat) (n : nat) : (term371 k n) = (term381 k n).
Proof. exact (MK_COMB (@lem130212) (@lem130211 k n)). Qed.
Lemma lem130214 (k : nat) (n : nat) : ((term370 k n) = (term371 k n)) = ((term366 k n) = (term381 k n)).
Proof. exact (MK_COMB (@lem130205 k n) (@lem130213 k n)). Qed.
Lemma lem130215 (k : nat) (n : nat) : (term366 k n) = (term381 k n).
Proof. exact (EQ_MP (@lem130214 k n) (@lem130195 k n)). Qed.
Lemma lem130216 (n : nat) : (term368 n) = (term382 n).
Proof. exact (fun_ext (fun k : nat => @lem130215 k n)). Qed.
Lemma lem130217 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem130218 (n : nat) : (term369 n) = (term383 n).
Proof. exact (MK_COMB (@lem130217) (@lem130216 n)). Qed.
Lemma lem130219 (n : nat) : (term353 n) = (term383 n).
Proof. exact (TRANS (@lem130191 n) (@lem130218 n)). Qed.
Lemma lem130220 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem130221 (n : nat) : (term355 n) = (term384 n).
Proof. exact (MK_COMB (@lem130220) (@lem130219 n)). Qed.
Lemma lem130222 (n : nat) : (term350 n) = (term350 n).
Proof. exact (eq_refl (term350 n)). Qed.
Lemma lem130223 (n : nat) : (term357 n) = (term385 n).
Proof. exact (MK_COMB (@lem130221 n) (@lem130222 n)). Qed.
Lemma lem130225 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem130226 (P : nat -> Prop) (Q : Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem130225 nat P Q). Qed.
Lemma lem130227 (n : nat) : (term386 n) = (term387 n).
Proof. exact (@lem130226 (term382 n) (term350 n)). Qed.
Lemma lem130228 (k : nat) (n : nat) : (term388 n k) = (term381 k n).
Proof. exact (eq_refl (term388 n k)). Qed.
Lemma lem130229 (n : nat) : (term389 n) = (term382 n).
Proof. exact (fun_ext (fun k : nat => @lem130228 k n)). Qed.
Lemma lem130230 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem130231 (n : nat) : (term390 n) = (term383 n).
Proof. exact (MK_COMB (@lem130230) (@lem130229 n)). Qed.
Lemma lem130232 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem130233 (n : nat) : (term391 n) = (term384 n).
Proof. exact (MK_COMB (@lem130232) (@lem130231 n)). Qed.
Lemma lem130234 (n : nat) : (term350 n) = (term350 n).
Proof. exact (eq_refl (term350 n)). Qed.
Lemma lem130235 (n : nat) : (term386 n) = (term385 n).
Proof. exact (MK_COMB (@lem130233 n) (@lem130234 n)). Qed.
Lemma lem130236 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem130237 (n : nat) : (term392 n) = (term393 n).
Proof. exact (MK_COMB (@lem130236) (@lem130235 n)). Qed.
Lemma lem130238 (k : nat) (n : nat) : (term388 n k) = (term381 k n).
Proof. exact (eq_refl (term388 n k)). Qed.
Lemma lem130239 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem130240 (k : nat) (n : nat) : (term394 n k) = (term395 k n).
Proof. exact (MK_COMB (@lem130239) (@lem130238 k n)). Qed.
Lemma lem130241 (n : nat) : (term350 n) = (term350 n).
Proof. exact (eq_refl (term350 n)). Qed.
Lemma lem130242 (k : nat) (n : nat) : (term396 k n) = (term397 k n).
Proof. exact (MK_COMB (@lem130240 k n) (@lem130241 n)). Qed.
Lemma lem130243 (n : nat) : (term398 n) = (term399 n).
Proof. exact (fun_ext (fun k : nat => @lem130242 k n)). Qed.
Lemma lem130244 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem130245 (n : nat) : (term387 n) = (term400 n).
Proof. exact (MK_COMB (@lem130244) (@lem130243 n)). Qed.
Lemma lem130246 (n : nat) : ((term386 n) = (term387 n)) = ((term385 n) = (term400 n)).
Proof. exact (MK_COMB (@lem130237 n) (@lem130245 n)). Qed.
Lemma lem130247 (n : nat) : (term385 n) = (term400 n).
Proof. exact (EQ_MP (@lem130246 n) (@lem130227 n)). Qed.
Lemma lem130249 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem130250 (P : nat -> Prop) (Q : Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem130249 nat P Q). Qed.
Lemma lem130251 (k : nat) (n : nat) : (term401 k n) = (term402 k n).
Proof. exact (@lem130250 (term380 k n) (term350 n)). Qed.
Lemma lem130252 (k : nat) (m : nat) (n : nat) : (term403 k n m) = (term378 k m n).
Proof. exact (eq_refl (term403 k n m)). Qed.
Lemma lem130253 (k : nat) (n : nat) : (term404 k n) = (term380 k n).
Proof. exact (fun_ext (fun m : nat => @lem130252 k m n)). Qed.
Lemma lem130254 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem130255 (k : nat) (n : nat) : (term405 k n) = (term381 k n).
Proof. exact (MK_COMB (@lem130254) (@lem130253 k n)). Qed.
Lemma lem130256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem130257 (k : nat) (n : nat) : (term406 k n) = (term395 k n).
Proof. exact (MK_COMB (@lem130256) (@lem130255 k n)). Qed.
Lemma lem130258 (n : nat) : (term350 n) = (term350 n).
Proof. exact (eq_refl (term350 n)). Qed.
Lemma lem130259 (k : nat) (n : nat) : (term401 k n) = (term397 k n).
Proof. exact (MK_COMB (@lem130257 k n) (@lem130258 n)). Qed.
Lemma lem130260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem130261 (k : nat) (n : nat) : (term407 k n) = (term408 k n).
Proof. exact (MK_COMB (@lem130260) (@lem130259 k n)). Qed.
Lemma lem130262 (k : nat) (m : nat) (n : nat) : (term403 k n m) = (term378 k m n).
Proof. exact (eq_refl (term403 k n m)). Qed.
Lemma lem130263 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem130264 (k : nat) (m : nat) (n : nat) : (term409 k n m) = (term410 k m n).
Proof. exact (MK_COMB (@lem130263) (@lem130262 k m n)). Qed.
Lemma lem130265 (n : nat) : (term350 n) = (term350 n).
Proof. exact (eq_refl (term350 n)). Qed.
Lemma lem130266 (k : nat) (m : nat) (n : nat) : (term411 k m n) = (term412 k m n).
Proof. exact (MK_COMB (@lem130264 k m n) (@lem130265 n)). Qed.
Lemma lem130267 (k : nat) (n : nat) : (term413 k n) = (term414 k n).
Proof. exact (fun_ext (fun m : nat => @lem130266 k m n)). Qed.
Lemma lem130268 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem130269 (k : nat) (n : nat) : (term402 k n) = (term415 k n).
Proof. exact (MK_COMB (@lem130268) (@lem130267 k n)). Qed.
Lemma lem130270 (k : nat) (n : nat) : ((term401 k n) = (term402 k n)) = ((term397 k n) = (term415 k n)).
Proof. exact (MK_COMB (@lem130261 k n) (@lem130269 k n)). Qed.
Lemma lem130271 (k : nat) (n : nat) : (term397 k n) = (term415 k n).
Proof. exact (EQ_MP (@lem130270 k n) (@lem130251 k n)). Qed.
Lemma lem130272 (n : nat) : (term399 n) = (term416 n).
Proof. exact (fun_ext (fun k : nat => @lem130271 k n)). Qed.
Lemma lem130273 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem130274 (n : nat) : (term400 n) = (term417 n).
Proof. exact (MK_COMB (@lem130273) (@lem130272 n)). Qed.
Lemma lem130275 (n : nat) : (term385 n) = (term417 n).
Proof. exact (TRANS (@lem130247 n) (@lem130274 n)). Qed.
Lemma lem130277 (n : nat) : (term357 n) = (term417 n).
Proof. exact (TRANS (@lem130223 n) (@lem130275 n)). Qed.
Lemma lem130278 (n : nat) : (term76 n) = (term417 n).
Proof. exact (TRANS (@lem130082 n) (@lem130277 n)). Qed.
Lemma lem130279 (n : nat) (h1 : term76 n) : term417 n.
Proof. exact (EQ_MP (@lem130278 n) (@lem129598 n h1)). Qed.
Lemma lem130280 (n : nat) : ((term145 n) = (NUMERAL 0)) = ((term145 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term145 n) = (NUMERAL 0))). Qed.
Lemma lem130281 : term146 = term146.
Proof. exact (fun_ext (fun n : nat => @lem130280 n)). Qed.
Lemma lem130282 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130283 : term147 = term147.
Proof. exact (MK_COMB (@lem130282) (@lem130281)). Qed.
Lemma lem130284 (m : nat) : ((term34 m) = (NUMERAL 0)) = ((term34 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term34 m) = (NUMERAL 0))). Qed.
Lemma lem130285 : term143 = term143.
Proof. exact (fun_ext (fun m : nat => @lem130284 m)). Qed.
Lemma lem130286 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130287 : term32 = term32.
Proof. exact (MK_COMB (@lem130286) (@lem130285)). Qed.
Lemma lem130288 (n : nat) : ((term16 n) = n) = ((term16 n) = n).
Proof. exact (eq_refl ((term16 n) = n)). Qed.
Lemma lem130289 : term17 = term17.
Proof. exact (fun_ext (fun n : nat => @lem130288 n)). Qed.
Lemma lem130290 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130291 : term15 = term15.
Proof. exact (MK_COMB (@lem130290) (@lem130289)). Qed.
Lemma lem130292 (m : nat) : ((term137 m) = m) = ((term137 m) = m).
Proof. exact (eq_refl ((term137 m) = m)). Qed.
Lemma lem130293 : term138 = term138.
Proof. exact (fun_ext (fun m : nat => @lem130292 m)). Qed.
Lemma lem130294 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130295 : term139 = term139.
Proof. exact (MK_COMB (@lem130294) (@lem130293)). Qed.
Lemma lem130296 (m : nat) (n : nat) : ((term129 m n) = (term130 m n)) = ((term129 m n) = (term130 m n)).
Proof. exact (eq_refl ((term129 m n) = (term130 m n))). Qed.
Lemma lem130297 (m : nat) : (term131 m) = (term131 m).
Proof. exact (fun_ext (fun n : nat => @lem130296 m n)). Qed.
Lemma lem130298 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130299 (m : nat) : (term132 m) = (term132 m).
Proof. exact (MK_COMB (@lem130298) (@lem130297 m)). Qed.
Lemma lem130300 : term133 = term133.
Proof. exact (fun_ext (fun m : nat => @lem130299 m)). Qed.
Lemma lem130301 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130302 : term134 = term134.
Proof. exact (MK_COMB (@lem130301) (@lem130300)). Qed.
Lemma lem130303 (m : nat) (n : nat) : ((term123 m n) = (term124 m n)) = ((term123 m n) = (term124 m n)).
Proof. exact (eq_refl ((term123 m n) = (term124 m n))). Qed.
Lemma lem130304 (m : nat) : (term125 m) = (term125 m).
Proof. exact (fun_ext (fun n : nat => @lem130303 m n)). Qed.
Lemma lem130305 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130306 (m : nat) : (term126 m) = (term126 m).
Proof. exact (MK_COMB (@lem130305) (@lem130304 m)). Qed.
Lemma lem130307 : term127 = term127.
Proof. exact (fun_ext (fun m : nat => @lem130306 m)). Qed.
Lemma lem130308 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130309 : term128 = term128.
Proof. exact (MK_COMB (@lem130308) (@lem130307)). Qed.
Lemma lem130310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130311 : term135 = term135.
Proof. exact (MK_COMB (@lem130310) (@lem130302)). Qed.
Lemma lem130312 : term136 = term136.
Proof. exact (MK_COMB (@lem130311) (@lem130309)). Qed.
Lemma lem130313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130314 : term140 = term140.
Proof. exact (MK_COMB (@lem130313) (@lem130295)). Qed.
Lemma lem130315 : term141 = term141.
Proof. exact (MK_COMB (@lem130314) (@lem130312)). Qed.
Lemma lem130316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130317 : term142 = term142.
Proof. exact (MK_COMB (@lem130316) (@lem130291)). Qed.
Lemma lem130318 : term14 = term14.
Proof. exact (MK_COMB (@lem130317) (@lem130315)). Qed.
Lemma lem130319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130320 : term144 = term144.
Proof. exact (MK_COMB (@lem130319) (@lem130287)). Qed.
Lemma lem130321 : term13 = term13.
Proof. exact (MK_COMB (@lem130320) (@lem130318)). Qed.
Lemma lem130322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130323 : term148 = term148.
Proof. exact (MK_COMB (@lem130322) (@lem130283)). Qed.
Lemma lem130360 : term149 = term149.
Proof. exact (MK_COMB (@lem130323) (@lem130321)). Qed.
Lemma lem130361 (h1 : term149) : term149.
Proof. exact (EQ_MP (@lem130360) (@lem129599 h1)). Qed.
Lemma lem130362 (m : nat) : ((term117 m) = term118) = ((term117 m) = term118).
Proof. exact (eq_refl ((term117 m) = term118)). Qed.
Lemma lem130363 : term119 = term119.
Proof. exact (fun_ext (fun m : nat => @lem130362 m)). Qed.
Lemma lem130364 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130365 : term120 = term120.
Proof. exact (MK_COMB (@lem130364) (@lem130363)). Qed.
Lemma lem130366 (m : nat) (n : nat) : ((term111 m n) = (term112 m n)) = ((term111 m n) = (term112 m n)).
Proof. exact (eq_refl ((term111 m n) = (term112 m n))). Qed.
Lemma lem130367 (m : nat) : (term113 m) = (term113 m).
Proof. exact (fun_ext (fun n : nat => @lem130366 m n)). Qed.
Lemma lem130368 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130369 (m : nat) : (term114 m) = (term114 m).
Proof. exact (MK_COMB (@lem130368) (@lem130367 m)). Qed.
Lemma lem130370 : term115 = term115.
Proof. exact (fun_ext (fun m : nat => @lem130369 m)). Qed.
Lemma lem130371 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130372 : term116 = term116.
Proof. exact (MK_COMB (@lem130371) (@lem130370)). Qed.
Lemma lem130373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130374 : term121 = term121.
Proof. exact (MK_COMB (@lem130373) (@lem130365)). Qed.
Lemma lem130391 : term122 = term122.
Proof. exact (MK_COMB (@lem130374) (@lem130372)). Qed.
Lemma lem130392 (h1 : term122) : term122.
Proof. exact (EQ_MP (@lem130391) (@lem129600 h1)). Qed.
Lemma lem130399 (n : nat) : (term418 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (@lem16933 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem130402 (n : nat) : (term419 n) = (term419 n).
Proof. exact (eq_refl (term419 n)). Qed.
Lemma lem130404 (n : nat) : (term420 n) = (term420 n).
Proof. exact (eq_refl (term420 n)). Qed.
Lemma lem130405 (n : nat) : (term421 n) = (term422 n).
Proof. exact (MK_COMB (@lem130404 n) (@lem130399 n)). Qed.
Lemma lem130406 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130407 (n : nat) : (term423 n) = (term424 n).
Proof. exact (MK_COMB (@lem130406) (@lem130405 n)). Qed.
Lemma lem130408 (n : nat) : (term425 n) = (term426 n).
Proof. exact (MK_COMB (@lem130407 n) (@lem130402 n)). Qed.
Lemma lem130409 (n : nat) : ((term108 n) = (term109 n)) = (term425 n).
Proof. exact (@lem17784 (term108 n) (term109 n)). Qed.
Lemma lem130410 (n : nat) : ((term108 n) = (term109 n)) = (term426 n).
Proof. exact (TRANS (@lem130409 n) (@lem130408 n)). Qed.
Lemma lem130411 : term110 = term427.
Proof. exact (fun_ext (fun n : nat => @lem130410 n)). Qed.
Lemma lem130412 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130413 : term88 = term428.
Proof. exact (MK_COMB (@lem130412) (@lem130411)). Qed.
Lemma lem130415 : term87 = term87.
Proof. exact (eq_refl term87). Qed.
Lemma lem130416 : term89 = term429.
Proof. exact (MK_COMB (@lem130415) (@lem130413)). Qed.
Lemma lem130418 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term430 A P Q) = (term431 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem130419 (P : nat -> Prop) (Q : nat -> Prop) : (term432 P Q) = (term433 P Q).
Proof. exact (@lem130418 nat P Q). Qed.
Lemma lem130420 : term434 = term435.
Proof. exact (@lem130419 term436 term437). Qed.
Lemma lem130421 (n : nat) : (term438 n) = (term422 n).
Proof. exact (eq_refl (term438 n)). Qed.
Lemma lem130422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130423 (n : nat) : (term439 n) = (term424 n).
Proof. exact (MK_COMB (@lem130422) (@lem130421 n)). Qed.
Lemma lem130424 (n : nat) : (term440 n) = (term419 n).
Proof. exact (eq_refl (term440 n)). Qed.
Lemma lem130425 (n : nat) : (term441 n) = (term426 n).
Proof. exact (MK_COMB (@lem130423 n) (@lem130424 n)). Qed.
Lemma lem130426 : term442 = term427.
Proof. exact (fun_ext (fun n : nat => @lem130425 n)). Qed.
Lemma lem130427 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130428 : term434 = term428.
Proof. exact (MK_COMB (@lem130427) (@lem130426)). Qed.
Lemma lem130429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem130430 : term443 = term444.
Proof. exact (MK_COMB (@lem130429) (@lem130428)). Qed.
Lemma lem130431 (n : nat) : (term438 n) = (term422 n).
Proof. exact (eq_refl (term438 n)). Qed.
Lemma lem130432 : term445 = term436.
Proof. exact (fun_ext (fun n : nat => @lem130431 n)). Qed.
Lemma lem130433 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130434 : term446 = term447.
Proof. exact (MK_COMB (@lem130433) (@lem130432)). Qed.
Lemma lem130435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130436 : term448 = term449.
Proof. exact (MK_COMB (@lem130435) (@lem130434)). Qed.
Lemma lem130437 (n : nat) : (term440 n) = (term419 n).
Proof. exact (eq_refl (term440 n)). Qed.
Lemma lem130438 : term450 = term437.
Proof. exact (fun_ext (fun n : nat => @lem130437 n)). Qed.
Lemma lem130439 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130440 : term451 = term452.
Proof. exact (MK_COMB (@lem130439) (@lem130438)). Qed.
Lemma lem130441 : term435 = term453.
Proof. exact (MK_COMB (@lem130436) (@lem130440)). Qed.
Lemma lem130442 : (term434 = term435) = (term428 = term453).
Proof. exact (MK_COMB (@lem130430) (@lem130441)). Qed.
Lemma lem130443 : term428 = term453.
Proof. exact (EQ_MP (@lem130442) (@lem130420)). Qed.
Lemma lem130524 : term87 = term87.
Proof. exact (eq_refl term87). Qed.
Lemma lem130527 : term429 = term454.
Proof. exact (MK_COMB (@lem130524) (@lem130443)). Qed.
Lemma lem130528 : term89 = term454.
Proof. exact (TRANS (@lem130416) (@lem130527)). Qed.
Lemma lem130529 (h1 : term89) : term454.
Proof. exact (EQ_MP (@lem130528) (@lem129601 h1)). Qed.
Lemma lem130530 (k : nat) (n : nat) (h1 : term415 k n) : term415 k n.
Proof. exact (h1). Qed.
Lemma lem130531 (k : nat) (m : nat) (n : nat) (h1 : term412 k m n) : term412 k m n.
Proof. exact (h1). Qed.
Lemma lem130532 (n : nat) (k' : nat -> nat) (h1 : term344 n k') : term344 n k'.
Proof. exact (h1). Qed.
Lemma lem130537 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem130556 (m : nat) (n : nat) : ((term123 m n) = (term124 m n)) = ((term123 m n) = (term124 m n)).
Proof. exact (eq_refl ((term123 m n) = (term124 m n))). Qed.
Lemma lem130557 (m : nat) : (term125 m) = (term125 m).
Proof. exact (fun_ext (fun n : nat => @lem130556 m n)). Qed.
Lemma lem130558 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130559 (m : nat) : (term126 m) = (term126 m).
Proof. exact (MK_COMB (@lem130558) (@lem130557 m)). Qed.
Lemma lem130560 : term127 = term127.
Proof. exact (fun_ext (fun m : nat => @lem130559 m)). Qed.
Lemma lem130561 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130562 : term128 = term128.
Proof. exact (MK_COMB (@lem130561) (@lem130560)). Qed.
Lemma lem130581 (m : nat) (n : nat) : ((term129 m n) = (term130 m n)) = ((term129 m n) = (term130 m n)).
Proof. exact (eq_refl ((term129 m n) = (term130 m n))). Qed.
Lemma lem130582 (m : nat) : (term131 m) = (term131 m).
Proof. exact (fun_ext (fun n : nat => @lem130581 m n)). Qed.
Lemma lem130583 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130584 (m : nat) : (term132 m) = (term132 m).
Proof. exact (MK_COMB (@lem130583) (@lem130582 m)). Qed.
Lemma lem130585 : term133 = term133.
Proof. exact (fun_ext (fun m : nat => @lem130584 m)). Qed.
Lemma lem130586 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130587 : term134 = term134.
Proof. exact (MK_COMB (@lem130586) (@lem130585)). Qed.
Lemma lem130588 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130589 : term135 = term135.
Proof. exact (MK_COMB (@lem130588) (@lem130587)). Qed.
Lemma lem130590 : term136 = term136.
Proof. exact (MK_COMB (@lem130589) (@lem130562)). Qed.
Lemma lem130603 (m : nat) : ((term137 m) = m) = ((term137 m) = m).
Proof. exact (eq_refl ((term137 m) = m)). Qed.
Lemma lem130604 : term138 = term138.
Proof. exact (fun_ext (fun m : nat => @lem130603 m)). Qed.
Lemma lem130605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130606 : term139 = term139.
Proof. exact (MK_COMB (@lem130605) (@lem130604)). Qed.
Lemma lem130607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130608 : term140 = term140.
Proof. exact (MK_COMB (@lem130607) (@lem130606)). Qed.
Lemma lem130609 : term141 = term141.
Proof. exact (MK_COMB (@lem130608) (@lem130590)). Qed.
Lemma lem130622 (n : nat) : ((term16 n) = n) = ((term16 n) = n).
Proof. exact (eq_refl ((term16 n) = n)). Qed.
Lemma lem130623 : term17 = term17.
Proof. exact (fun_ext (fun n : nat => @lem130622 n)). Qed.
Lemma lem130624 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130625 : term15 = term15.
Proof. exact (MK_COMB (@lem130624) (@lem130623)). Qed.
Lemma lem130626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130627 : term142 = term142.
Proof. exact (MK_COMB (@lem130626) (@lem130625)). Qed.
Lemma lem130628 : term14 = term14.
Proof. exact (MK_COMB (@lem130627) (@lem130609)). Qed.
Lemma lem130641 (m : nat) : ((term34 m) = (NUMERAL 0)) = ((term34 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term34 m) = (NUMERAL 0))). Qed.
Lemma lem130642 : term143 = term143.
Proof. exact (fun_ext (fun m : nat => @lem130641 m)). Qed.
Lemma lem130643 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130644 : term32 = term32.
Proof. exact (MK_COMB (@lem130643) (@lem130642)). Qed.
Lemma lem130645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130646 : term144 = term144.
Proof. exact (MK_COMB (@lem130645) (@lem130644)). Qed.
Lemma lem130647 : term13 = term13.
Proof. exact (MK_COMB (@lem130646) (@lem130628)). Qed.
Lemma lem130660 (n : nat) : ((term145 n) = (NUMERAL 0)) = ((term145 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term145 n) = (NUMERAL 0))). Qed.
Lemma lem130661 : term146 = term146.
Proof. exact (fun_ext (fun n : nat => @lem130660 n)). Qed.
Lemma lem130662 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130663 : term147 = term147.
Proof. exact (MK_COMB (@lem130662) (@lem130661)). Qed.
Lemma lem130664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130665 : term148 = term148.
Proof. exact (MK_COMB (@lem130664) (@lem130663)). Qed.
Lemma lem130666 : term149 = term149.
Proof. exact (MK_COMB (@lem130665) (@lem130647)). Qed.
Lemma lem130667 (h1 : term149) : term149.
Proof. exact (EQ_MP (@lem130666) (@lem130361 h1)). Qed.
Lemma lem130686 (m : nat) (n : nat) : ((term111 m n) = (term112 m n)) = ((term111 m n) = (term112 m n)).
Proof. exact (eq_refl ((term111 m n) = (term112 m n))). Qed.
Lemma lem130687 (m : nat) : (term113 m) = (term113 m).
Proof. exact (fun_ext (fun n : nat => @lem130686 m n)). Qed.
Lemma lem130688 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130689 (m : nat) : (term114 m) = (term114 m).
Proof. exact (MK_COMB (@lem130688) (@lem130687 m)). Qed.
Lemma lem130690 : term115 = term115.
Proof. exact (fun_ext (fun m : nat => @lem130689 m)). Qed.
Lemma lem130691 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130692 : term116 = term116.
Proof. exact (MK_COMB (@lem130691) (@lem130690)). Qed.
Lemma lem130707 (m : nat) : ((term117 m) = term118) = ((term117 m) = term118).
Proof. exact (eq_refl ((term117 m) = term118)). Qed.
Lemma lem130708 : term119 = term119.
Proof. exact (fun_ext (fun m : nat => @lem130707 m)). Qed.
Lemma lem130709 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130710 : term120 = term120.
Proof. exact (MK_COMB (@lem130709) (@lem130708)). Qed.
Lemma lem130711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130712 : term121 = term121.
Proof. exact (MK_COMB (@lem130711) (@lem130710)). Qed.
Lemma lem130713 : term122 = term122.
Proof. exact (MK_COMB (@lem130712) (@lem130692)). Qed.
Lemma lem130714 (h1 : term122) : term122.
Proof. exact (EQ_MP (@lem130713) (@lem130392 h1)). Qed.
Lemma lem130729 (n : nat) : (term419 n) = (term419 n).
Proof. exact (eq_refl (term419 n)). Qed.
Lemma lem130730 : term437 = term437.
Proof. exact (fun_ext (fun n : nat => @lem130729 n)). Qed.
Lemma lem130731 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130732 : term452 = term452.
Proof. exact (MK_COMB (@lem130731) (@lem130730)). Qed.
Lemma lem130743 (n : nat) : (term422 n) = (term422 n).
Proof. exact (eq_refl (term422 n)). Qed.
Lemma lem130744 : term436 = term436.
Proof. exact (fun_ext (fun n : nat => @lem130743 n)). Qed.
Lemma lem130745 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130746 : term447 = term447.
Proof. exact (MK_COMB (@lem130745) (@lem130744)). Qed.
Lemma lem130747 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130748 : term449 = term449.
Proof. exact (MK_COMB (@lem130747) (@lem130746)). Qed.
Lemma lem130749 : term453 = term453.
Proof. exact (MK_COMB (@lem130748) (@lem130732)). Qed.
Lemma lem130758 : term87 = term87.
Proof. exact (eq_refl term87). Qed.
Lemma lem130759 : term454 = term454.
Proof. exact (MK_COMB (@lem130758) (@lem130749)). Qed.
Lemma lem130760 (h1 : term89) : term454.
Proof. exact (EQ_MP (@lem130759) (@lem130529 h1)). Qed.
Lemma lem130769 (n : nat) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem130798 (n : nat) (k : nat) (m : nat) : (term156 n k m) = (term156 n k m).
Proof. exact (eq_refl (term156 n k m)). Qed.
Lemma lem130799 (n : nat) (k : nat) : (term165 n k) = (term165 n k).
Proof. exact (fun_ext (fun m : nat => @lem130798 n k m)). Qed.
Lemma lem130800 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130801 (n : nat) (k : nat) : (term166 n k) = (term166 n k).
Proof. exact (MK_COMB (@lem130800) (@lem130799 n k)). Qed.
Lemma lem130802 (n : nat) : (term172 n) = (term172 n).
Proof. exact (fun_ext (fun k : nat => @lem130801 n k)). Qed.
Lemma lem130803 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem130804 (n : nat) : (term173 n) = (term173 n).
Proof. exact (MK_COMB (@lem130803) (@lem130802 n)). Qed.
Lemma lem130805 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem130806 (n : nat) : (term348 n) = (term348 n).
Proof. exact (MK_COMB (@lem130805) (@lem130804 n)). Qed.
Lemma lem130807 (n : nat) : (term350 n) = (term350 n).
Proof. exact (MK_COMB (@lem130806 n) (@lem130769 n)). Qed.
Lemma lem130844 (k : nat) (m : nat) (n : nat) : (term410 k m n) = (term410 k m n).
Proof. exact (eq_refl (term410 k m n)). Qed.
Lemma lem130845 (k : nat) (m : nat) (n : nat) : (term412 k m n) = (term412 k m n).
Proof. exact (MK_COMB (@lem130844 k m n) (@lem130807 n)). Qed.
Lemma lem130846 (k : nat) (m : nat) (n : nat) (h1 : term412 k m n) : term412 k m n.
Proof. exact (EQ_MP (@lem130845 k m n) (@lem130531 k m n h1)). Qed.
Lemma lem130957 (h1 : term122) : term120.
Proof. exact (proj1 (@lem130714 h1)). Qed.
Lemma lem130958 (h1 : term149) : term13.
Proof. exact (proj2 (@lem130667 h1)). Qed.
Lemma lem130960 (h1 : term149) : term14.
Proof. exact (proj2 (@lem130958 h1)). Qed.
Lemma lem130963 (h1 : term149) : term15.
Proof. exact (proj1 (@lem130960 h1)). Qed.
Lemma lem130968 (k : nat) (m : nat) (n : nat) (h1 : term378 k m n) : term378 k m n.
Proof. exact (h1). Qed.
Lemma lem130969 (n : nat) (h1 : term350 n) : term350 n.
Proof. exact (h1). Qed.
Lemma lem130971 (k : nat) (m : nat) (n : nat) (h1 : term378 k m n) : term150 n k m.
Proof. exact (proj1 (@lem130968 k m n h1)). Qed.
Lemma lem130975 (n : nat) (h1 : term350 n) : term173 n.
Proof. exact (proj1 (@lem130969 n h1)). Qed.
Lemma lem130979 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem131301 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem131544 (m : nat) : ((term117 m) = term118) = ((term117 m) = term118).
Proof. exact (eq_refl ((term117 m) = term118)). Qed.
Lemma lem131545 : term119 = term119.
Proof. exact (fun_ext (fun m : nat => @lem131544 m)). Qed.
Lemma lem131546 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem131548 : term120 = term120.
Proof. exact (MK_COMB (@lem131546) (@lem131545)). Qed.
Lemma lem131549 (h1 : term122) : term120.
Proof. exact (EQ_MP (@lem131548) (@lem130957 h1)). Qed.
Lemma lem131575 (n : nat) : ((term16 n) = n) = ((term16 n) = n).
Proof. exact (eq_refl ((term16 n) = n)). Qed.
Lemma lem131576 : term17 = term17.
Proof. exact (fun_ext (fun n : nat => @lem131575 n)). Qed.
Lemma lem131577 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem131579 : term15 = term15.
Proof. exact (MK_COMB (@lem131577) (@lem131576)). Qed.
Lemma lem131580 (h1 : term149) : term15.
Proof. exact (EQ_MP (@lem131579) (@lem130963 h1)). Qed.
Lemma lem131615 (n : nat) (k : nat) (m : nat) : (term156 n k m) = (term156 n k m).
Proof. exact (eq_refl (term156 n k m)). Qed.
Lemma lem131616 (n : nat) (k : nat) : (term165 n k) = (term165 n k).
Proof. exact (fun_ext (fun m : nat => @lem131615 n k m)). Qed.
Lemma lem131617 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem131618 (n : nat) (k : nat) : (term166 n k) = (term166 n k).
Proof. exact (MK_COMB (@lem131617) (@lem131616 n k)). Qed.
Lemma lem131619 (n : nat) : (term172 n) = (term172 n).
Proof. exact (fun_ext (fun k : nat => @lem131618 n k)). Qed.
Lemma lem131620 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem131622 (n : nat) : (term173 n) = (term173 n).
Proof. exact (MK_COMB (@lem131620) (@lem131619 n)). Qed.
Lemma lem131623 (n : nat) (h1 : term350 n) : term173 n.
Proof. exact (EQ_MP (@lem131622 n) (@lem130975 n h1)). Qed.
Lemma lem131691 (_2633 : nat) (h1 : term122) : term455 _2633.
Proof. exact (@lem131549 h1 _2633). Qed.
Lemma lem131692 (_2633 : nat) : (term455 _2633) = ((term117 _2633) = term118).
Proof. exact (eq_refl (term455 _2633)). Qed.
Lemma lem131706 (_2638 : nat) (h1 : term149) : term456 _2638.
Proof. exact (@lem131580 h1 _2638). Qed.
Lemma lem131707 (_2638 : nat) : (term456 _2638) = ((term16 _2638) = _2638).
Proof. exact (eq_refl (term456 _2638)). Qed.
Lemma lem131724 (_2644 : nat) (n : nat) (h1 : term350 n) : term457 n _2644.
Proof. exact (@lem131623 n h1 _2644). Qed.
Lemma lem131725 (n : nat) (_2644 : nat) : (term457 n _2644) = (term166 n _2644).
Proof. exact (eq_refl (term457 n _2644)). Qed.
Lemma lem131726 (_2644 : nat) (n : nat) (h1 : term350 n) : term166 n _2644.
Proof. exact (EQ_MP (@lem131725 n _2644) (@lem131724 _2644 n h1)). Qed.
Lemma lem131727 (_2644 : nat) (_2645 : nat) (n : nat) (h1 : term350 n) : term458 n _2644 _2645.
Proof. exact (@lem131726 _2644 n h1 _2645). Qed.
Lemma lem131728 (n : nat) (_2644 : nat) (_2645 : nat) : (term458 n _2644 _2645) = (term156 n _2644 _2645).
Proof. exact (eq_refl (term458 n _2644 _2645)). Qed.
Lemma lem131739 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem131771 (k : nat) (m : nat) (n : nat) (h1 : term378 k m n) : n = (NUMERAL 0).
Proof. exact (proj2 (@lem130968 k m n h1)). Qed.
Lemma lem131775 (k : nat) (m : nat) (n : nat) (h1 : term378 k m n) : n = (term157 k m).
Proof. exact (proj2 (@lem130971 k m n h1)). Qed.
Lemma lem131813 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem131849 (_2644 : nat) (_2645 : nat) (n : nat) (h1 : term350 n) : term156 n _2644 _2645.
Proof. exact (EQ_MP (@lem131728 n _2644 _2645) (@lem131727 _2644 _2645 n h1)). Qed.
Lemma lem131902 : term459 = term459.
Proof. exact (eq_refl term459). Qed.
Lemma lem131903 (k : nat) (m : nat) (n : nat) (h1 : term378 k m n) : (term460 n) = (term461 k m).
Proof. exact (MK_COMB (@lem131902) (@lem131775 k m n h1)). Qed.
Lemma lem131904 (k : nat) (m : nat) : (term461 k m) = (term462 k m).
Proof. exact (eq_refl (term461 k m)). Qed.
Lemma lem131905 (n : nat) : (term463 n) = (term463 n).
Proof. exact (eq_refl (term463 n)). Qed.
Lemma lem131906 (n : nat) (k : nat) (m : nat) : ((term460 n) = (term461 k m)) = ((term460 n) = (term462 k m)).
Proof. exact (MK_COMB (@lem131905 n) (@lem131904 k m)). Qed.
Lemma lem131907 (n : nat) : (term460 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (eq_refl (term460 n)). Qed.
Lemma lem131908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem131909 (n : nat) : (term463 n) = (term464 n).
Proof. exact (MK_COMB (@lem131908) (@lem131907 n)). Qed.
Lemma lem131910 (k : nat) (m : nat) : (term462 k m) = (term462 k m).
Proof. exact (eq_refl (term462 k m)). Qed.
Lemma lem131911 (n : nat) (k : nat) (m : nat) : ((term460 n) = (term462 k m)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term462 k m)).
Proof. exact (MK_COMB (@lem131909 n) (@lem131910 k m)). Qed.
Lemma lem131912 (n : nat) (k : nat) (m : nat) : ((term460 n) = (term461 k m)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term462 k m)).
Proof. exact (TRANS (@lem131906 n k m) (@lem131911 n k m)). Qed.
Lemma lem131913 (k : nat) (m : nat) (n : nat) (h1 : term378 k m n) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term462 k m).
Proof. exact (EQ_MP (@lem131912 n k m) (@lem131903 k m n h1)). Qed.
Lemma lem131928 (h1 : term89) : term85.
Proof. exact (proj1 (@lem130760 h1)). Qed.
Lemma lem132069 : term465 = term465.
Proof. exact (eq_refl term465). Qed.
Lemma lem132070 (k : nat) (m : nat) (n : nat) (h1 : term378 k m n) : (term466 n) = (term467 k m).
Proof. exact (MK_COMB (@lem132069) (@lem131775 k m n h1)). Qed.
Lemma lem132071 (k : nat) (m : nat) : (term467 k m) = ((term157 k m) = (NUMERAL 0)).
Proof. exact (eq_refl (term467 k m)). Qed.
Lemma lem132072 (n : nat) : (term468 n) = (term468 n).
Proof. exact (eq_refl (term468 n)). Qed.
Lemma lem132073 (n : nat) (k : nat) (m : nat) : ((term466 n) = (term467 k m)) = ((term466 n) = ((term157 k m) = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem132072 n) (@lem132071 k m)). Qed.
Lemma lem132074 (n : nat) : (term466 n) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (term466 n)). Qed.
Lemma lem132075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem132076 (n : nat) : (term468 n) = (term469 n).
Proof. exact (MK_COMB (@lem132075) (@lem132074 n)). Qed.
Lemma lem132077 (k : nat) (m : nat) : ((term157 k m) = (NUMERAL 0)) = ((term157 k m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term157 k m) = (NUMERAL 0))). Qed.
Lemma lem132078 (n : nat) (k : nat) (m : nat) : ((term466 n) = ((term157 k m) = (NUMERAL 0))) = ((n = (NUMERAL 0)) = ((term157 k m) = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem132076 n) (@lem132077 k m)). Qed.
Lemma lem132079 (n : nat) (k : nat) (m : nat) : ((term466 n) = (term467 k m)) = ((n = (NUMERAL 0)) = ((term157 k m) = (NUMERAL 0))).
Proof. exact (TRANS (@lem132073 n k m) (@lem132078 n k m)). Qed.
Lemma lem132080 (k : nat) (m : nat) (n : nat) (h1 : term378 k m n) : (n = (NUMERAL 0)) = ((term157 k m) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem132079 n k m) (@lem132070 k m n h1)). Qed.
Lemma lem132154 : Coq.Arith.PeanoNat.Nat.Odd = Coq.Arith.PeanoNat.Nat.Odd.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Odd). Qed.
Lemma lem132155 (_2686 : nat) (_2687 : nat) (h1 : _2686 = _2687) : _2686 = _2687.
Proof. exact (h1). Qed.
Lemma lem132156 (_2686 : nat) (_2687 : nat) (h1 : _2686 = _2687) : (Coq.Arith.PeanoNat.Nat.Odd _2686) = (Coq.Arith.PeanoNat.Nat.Odd _2687).
Proof. exact (MK_COMB (@lem132154) (@lem132155 _2686 _2687 h1)). Qed.
Lemma lem132158 (b : Prop) (a : Prop) : term470 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem132159 (_2687 : nat) (_2686 : nat) : term471 _2687 _2686.
Proof. exact (@lem132158 (Coq.Arith.PeanoNat.Nat.Odd _2687) (Coq.Arith.PeanoNat.Nat.Odd _2686)). Qed.
Lemma lem132160 (_2686 : nat) (_2687 : nat) (h1 : _2686 = _2687) : term472 _2687 _2686.
Proof. exact (@lem132159 _2687 _2686 (@lem132156 _2686 _2687 h1)). Qed.
Lemma lem132161 (_2687 : nat) (_2686 : nat) : term473 _2687 _2686.
Proof. exact (fun h0 : _2686 = _2687 => @lem132160 _2686 _2687 h0). Qed.
Lemma lem132163 (a : Prop) (b : Prop) : (a -> b) = (term474 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem132164 (_2687 : nat) (_2686 : nat) : (term473 _2687 _2686) = (term475 _2687 _2686).
Proof. exact (@lem132163 (_2686 = _2687) (term472 _2687 _2686)). Qed.
Lemma lem132165 (_2687 : nat) (_2686 : nat) : term475 _2687 _2686.
Proof. exact (EQ_MP (@lem132164 _2687 _2686) (@lem132161 _2687 _2686)). Qed.
Lemma lem132262 (k : nat) (m : nat) (n : nat) (h1 : term378 k m n) : (term157 k m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem132080 k m n h1) (@lem131771 k m n h1)). Qed.
Lemma lem132263 (k : nat) (m : nat) (n : nat) (h1 : term378 k m n) : term476 k m.
Proof. exact (fun h0 : term477 k m => @lem132262 k m n h1). Qed.
Lemma lem132265 (p : Prop) : (term478 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem132266 (k : nat) (m : nat) : (term476 k m) = ((term157 k m) = (NUMERAL 0)).
Proof. exact (@lem132265 ((term157 k m) = (NUMERAL 0))). Qed.
Lemma lem132267 (k : nat) (m : nat) (n : nat) (h1 : term378 k m n) : (term157 k m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem132266 k m) (@lem132263 k m n h1)). Qed.
Lemma lem132269 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term378 k m n) : term462 k m.
Proof. exact (EQ_MP (@lem131913 k m n h2) (@lem131739 n h1)). Qed.
Lemma lem132270 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term378 k m n) : term479 k m.
Proof. exact (fun h0 : term480 k m => @lem132269 k m n h1 h2). Qed.
Lemma lem132272 (p : Prop) : (term478 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem132273 (k : nat) (m : nat) : (term479 k m) = (term462 k m).
Proof. exact (@lem132272 (term462 k m)). Qed.
Lemma lem132274 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term378 k m n) : term462 k m.
Proof. exact (EQ_MP (@lem132273 k m) (@lem132270 k m n h1 h2)). Qed.
Lemma lem132280 (q : Prop) (p : Prop) (r : Prop) : (term481 p q r) = (term481 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem132281 (_2687 : nat) (_2686 : nat) : (term475 _2687 _2686) = (term482 _2687 _2686).
Proof. exact (@lem132280 (Coq.Arith.PeanoNat.Nat.Odd _2687) (term483 _2686 _2687) (term109 _2686)). Qed.
Lemma lem132299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem132300 (_2687 : nat) (_2686 : nat) : (term484 _2687 _2686) = (term485 _2687 _2686).
Proof. exact (MK_COMB (@lem132299) (@lem132281 _2687 _2686)). Qed.
Lemma lem132318 (_2687 : nat) (_2686 : nat) : (term482 _2687 _2686) = (term482 _2687 _2686).
Proof. exact (eq_refl (term482 _2687 _2686)). Qed.
Lemma lem132319 (_2687 : nat) (_2686 : nat) : ((term475 _2687 _2686) = (term482 _2687 _2686)) = ((term482 _2687 _2686) = (term482 _2687 _2686)).
Proof. exact (MK_COMB (@lem132300 _2687 _2686) (@lem132318 _2687 _2686)). Qed.
Lemma lem132321 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem132322 (x : Prop) : (x = x) = True.
Proof. exact (@lem132321 Prop x). Qed.
Lemma lem132323 (_2687 : nat) (_2686 : nat) : ((term482 _2687 _2686) = (term482 _2687 _2686)) = True.
Proof. exact (@lem132322 (term482 _2687 _2686)). Qed.
Lemma lem132324 (_2687 : nat) (_2686 : nat) : ((term475 _2687 _2686) = (term482 _2687 _2686)) = True.
Proof. exact (TRANS (@lem132319 _2687 _2686) (@lem132323 _2687 _2686)). Qed.
Lemma lem132325 (_2687 : nat) (_2686 : nat) : True = ((term475 _2687 _2686) = (term482 _2687 _2686)).
Proof. exact (SYM (@lem132324 _2687 _2686)). Qed.
Lemma lem132326 (_2687 : nat) (_2686 : nat) : (term475 _2687 _2686) = (term482 _2687 _2686).
Proof. exact (EQ_MP (@lem132325 _2687 _2686) (@lem0)). Qed.
Lemma lem132327 (_2687 : nat) (_2686 : nat) : term482 _2687 _2686.
Proof. exact (EQ_MP (@lem132326 _2687 _2686) (@lem132165 _2687 _2686)). Qed.
Lemma lem132329 (b : Prop) (a : Prop) : (a \/ b) = (term486 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem132330 (_2686 : nat) (_2687 : nat) : (term482 _2687 _2686) = (term487 _2686 _2687).
Proof. exact (@lem132329 (term488 _2687 _2686) (Coq.Arith.PeanoNat.Nat.Odd _2687)). Qed.
Lemma lem132332 (a : Prop) (b : Prop) : (term489 a b) = (term490 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem132333 (_2687 : nat) (_2686 : nat) : (term491 _2687 _2686) = (term492 _2687 _2686).
Proof. exact (@lem132332 (term483 _2686 _2687) (term109 _2686)). Qed.
Lemma lem132335 (a : Prop) : (term493 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem132336 (_2686 : nat) (_2687 : nat) : (term494 _2686 _2687) = (_2686 = _2687).
Proof. exact (@lem132335 (_2686 = _2687)). Qed.
Lemma lem132337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem132338 (_2686 : nat) (_2687 : nat) : (term495 _2686 _2687) = (term496 _2686 _2687).
Proof. exact (MK_COMB (@lem132337) (@lem132336 _2686 _2687)). Qed.
Lemma lem132340 (a : Prop) : (term493 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem132341 (_2686 : nat) : (term418 _2686) = (Coq.Arith.PeanoNat.Nat.Odd _2686).
Proof. exact (@lem132340 (Coq.Arith.PeanoNat.Nat.Odd _2686)). Qed.
Lemma lem132342 (_2687 : nat) (_2686 : nat) : (term492 _2687 _2686) = (term497 _2687 _2686).
Proof. exact (MK_COMB (@lem132338 _2686 _2687) (@lem132341 _2686)). Qed.
Lemma lem132343 (_2687 : nat) (_2686 : nat) : (term491 _2687 _2686) = (term497 _2687 _2686).
Proof. exact (TRANS (@lem132333 _2687 _2686) (@lem132342 _2687 _2686)). Qed.
Lemma lem132344 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem132345 (_2687 : nat) (_2686 : nat) : (term498 _2687 _2686) = (term499 _2687 _2686).
Proof. exact (MK_COMB (@lem132344) (@lem132343 _2687 _2686)). Qed.
Lemma lem132346 (_2687 : nat) : (Coq.Arith.PeanoNat.Nat.Odd _2687) = (Coq.Arith.PeanoNat.Nat.Odd _2687).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Odd _2687)). Qed.
Lemma lem132347 (_2686 : nat) (_2687 : nat) : (term487 _2686 _2687) = (term500 _2686 _2687).
Proof. exact (MK_COMB (@lem132345 _2687 _2686) (@lem132346 _2687)). Qed.
Lemma lem132348 (_2686 : nat) (_2687 : nat) : (term482 _2687 _2686) = (term500 _2686 _2687).
Proof. exact (TRANS (@lem132330 _2686 _2687) (@lem132347 _2686 _2687)). Qed.
Lemma lem132350 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term378 k m n) : term501 k m.
Proof. exact (conj (@lem132267 k m n h2) (@lem132274 k m n h1 h2)). Qed.
Lemma lem132352 (_2686 : nat) (_2687 : nat) : term500 _2686 _2687.
Proof. exact (EQ_MP (@lem132348 _2686 _2687) (@lem132327 _2687 _2686)). Qed.
Lemma lem132353 (k : nat) (m : nat) : term502 k m.
Proof. exact (@lem132352 (term157 k m) (NUMERAL 0)). Qed.
Lemma lem132356 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term378 k m n) : term84.
Proof. exact (@lem132353 k m (@lem132350 k m n h1 h2)). Qed.
Lemma lem132357 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term378 k m n) : term503.
Proof. exact (fun h0 : term85 => @lem132356 k m n h1 h2). Qed.
Lemma lem132359 (p : Prop) : (term478 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem132360 : term503 = term84.
Proof. exact (@lem132359 term84). Qed.
Lemma lem132361 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term378 k m n) : term84.
Proof. exact (EQ_MP (@lem132360) (@lem132357 k m n h1 h2)). Qed.
Lemma lem132364 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem132366 : term85 = term504.
Proof. exact (@lem132364 term84). Qed.
Lemma lem132369 (h1 : term89) : term504.
Proof. exact (EQ_MP (@lem132366) (@lem131928 h1)). Qed.
Lemma lem132372 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term89) (h3 : term378 k m n) : False.
Proof. exact (@lem132369 h2 (@lem132361 k m n h1 h3)). Qed.
Lemma lem132373 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term89) (h3 : term378 k m n) : term505.
Proof. exact (fun h0 : ~ False => @lem132372 k m n h1 h2 h3). Qed.
Lemma lem132375 (p : Prop) : (term478 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem132376 : term505 = False.
Proof. exact (@lem132375 False). Qed.
Lemma lem132448 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem132449 (_2728 : nat) (_2730 : nat) (h1 : _2728 = _2730) : _2728 = _2730.
Proof. exact (h1). Qed.
Lemma lem132450 (_2729 : nat) (_2731 : nat) (h1 : _2729 = _2731) : _2729 = _2731.
Proof. exact (h1). Qed.
Lemma lem132451 (_2728 : nat) (_2730 : nat) (h1 : _2728 = _2730) : (Nat.mul _2728) = (Nat.mul _2730).
Proof. exact (MK_COMB (@lem132448) (@lem132449 _2728 _2730 h1)). Qed.
Lemma lem132452 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) (h1 : _2728 = _2730) (h2 : _2729 = _2731) : (Nat.mul _2728 _2729) = (Nat.mul _2730 _2731).
Proof. exact (MK_COMB (@lem132451 _2728 _2730 h1) (@lem132450 _2729 _2731 h2)). Qed.
Lemma lem132453 (_2729 : nat) (_2731 : nat) (_2728 : nat) (_2730 : nat) (h1 : _2728 = _2730) : term506 _2728 _2729 _2730 _2731.
Proof. exact (fun h0 : _2729 = _2731 => @lem132452 _2728 _2730 _2729 _2731 h1 h0). Qed.
Lemma lem132455 (a : Prop) (b : Prop) : (a -> b) = (term474 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem132456 (_2728 : nat) (_2729 : nat) (_2730 : nat) (_2731 : nat) : (term506 _2728 _2729 _2730 _2731) = (term507 _2728 _2729 _2730 _2731).
Proof. exact (@lem132455 (_2729 = _2731) ((Nat.mul _2728 _2729) = (Nat.mul _2730 _2731))). Qed.
Lemma lem132457 (_2729 : nat) (_2731 : nat) (_2728 : nat) (_2730 : nat) (h1 : _2728 = _2730) : term507 _2728 _2729 _2730 _2731.
Proof. exact (EQ_MP (@lem132456 _2728 _2729 _2730 _2731) (@lem132453 _2729 _2731 _2728 _2730 h1)). Qed.
Lemma lem132458 (_2728 : nat) (_2729 : nat) (_2730 : nat) (_2731 : nat) : term508 _2728 _2729 _2730 _2731.
Proof. exact (fun h0 : _2728 = _2730 => @lem132457 _2729 _2731 _2728 _2730 h0). Qed.
Lemma lem132460 (a : Prop) (b : Prop) : (a -> b) = (term474 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem132461 (_2728 : nat) (_2729 : nat) (_2730 : nat) (_2731 : nat) : (term508 _2728 _2729 _2730 _2731) = (term509 _2728 _2729 _2730 _2731).
Proof. exact (@lem132460 (_2728 = _2730) (term507 _2728 _2729 _2730 _2731)). Qed.
Lemma lem132462 (_2728 : nat) (_2729 : nat) (_2730 : nat) (_2731 : nat) : term509 _2728 _2729 _2730 _2731.
Proof. exact (EQ_MP (@lem132461 _2728 _2729 _2730 _2731) (@lem132458 _2728 _2729 _2730 _2731)). Qed.
Lemma lem132503 (x : nat) (y : nat) (z : nat) : term510 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem132505 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem132506 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : term511 n.
Proof. exact (fun h0 : term109 n => @lem132505 n h1). Qed.
Lemma lem132508 (p : Prop) : (term478 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem132509 (n : nat) : (term511 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (@lem132508 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem132510 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (EQ_MP (@lem132509 n) (@lem132506 n h1)). Qed.
Lemma lem132512 (_2638 : nat) (h1 : term149) : (term16 _2638) = _2638.
Proof. exact (EQ_MP (@lem131707 _2638) (@lem131706 _2638 h1)). Qed.
Lemma lem132513 (n : nat) (h1 : term149) : (term16 n) = n.
Proof. exact (@lem132512 n h1). Qed.
Lemma lem132514 (n : nat) (h1 : term149) : term512 n.
Proof. exact (fun h0 : term513 n => @lem132513 n h1). Qed.
Lemma lem132516 (p : Prop) : (term478 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem132517 (n : nat) : (term512 n) = ((term16 n) = n).
Proof. exact (@lem132516 ((term16 n) = n)). Qed.
Lemma lem132518 (n : nat) (h1 : term149) : (term16 n) = n.
Proof. exact (EQ_MP (@lem132517 n) (@lem132514 n h1)). Qed.
Lemma lem132520 (_2633 : nat) (h1 : term122) : (term117 _2633) = term118.
Proof. exact (EQ_MP (@lem131692 _2633) (@lem131691 _2633 h1)). Qed.
Lemma lem132521 (h1 : term122) : term514 = term118.
Proof. exact (@lem132520 term8 h1). Qed.
Lemma lem132522 (h1 : term122) : term515.
Proof. exact (fun h0 : term516 => @lem132521 h1). Qed.
Lemma lem132524 (p : Prop) : (term478 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem132525 : term515 = (term514 = term118).
Proof. exact (@lem132524 (term514 = term118)). Qed.
Lemma lem132526 (h1 : term122) : term514 = term118.
Proof. exact (EQ_MP (@lem132525) (@lem132522 h1)). Qed.
Lemma lem132528 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem132529 (n : nat) : n = n.
Proof. exact (@lem132528 n). Qed.
Lemma lem132530 (n : nat) : term517 n.
Proof. exact (fun h0 : term518 n => @lem132529 n). Qed.
Lemma lem132532 (p : Prop) : (term478 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem132533 (n : nat) : (term517 n) = (n = n).
Proof. exact (@lem132532 (n = n)). Qed.
Lemma lem132534 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem132533 n) (@lem132530 n)). Qed.
Lemma lem132552 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem132553 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : (term507 _2728 _2729 _2730 _2731) = (term519 _2728 _2730 _2729 _2731).
Proof. exact (@lem132552 ((Nat.mul _2728 _2729) = (Nat.mul _2730 _2731)) (term483 _2729 _2731)). Qed.
Lemma lem132563 (_2728 : nat) (_2730 : nat) : (term520 _2728 _2730) = (term520 _2728 _2730).
Proof. exact (eq_refl (term520 _2728 _2730)). Qed.
Lemma lem132564 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : (term509 _2728 _2729 _2730 _2731) = (term521 _2728 _2730 _2729 _2731).
Proof. exact (MK_COMB (@lem132563 _2728 _2730) (@lem132553 _2728 _2730 _2729 _2731)). Qed.
Lemma lem132568 (q : Prop) (p : Prop) (r : Prop) : (term481 p q r) = (term481 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem132569 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : (term521 _2728 _2730 _2729 _2731) = (term522 _2728 _2730 _2729 _2731).
Proof. exact (@lem132568 ((Nat.mul _2728 _2729) = (Nat.mul _2730 _2731)) (term483 _2728 _2730) (term483 _2729 _2731)). Qed.
Lemma lem132591 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : (term509 _2728 _2729 _2730 _2731) = (term522 _2728 _2730 _2729 _2731).
Proof. exact (TRANS (@lem132564 _2728 _2730 _2729 _2731) (@lem132569 _2728 _2730 _2729 _2731)). Qed.
Lemma lem132592 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem132593 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : (term523 _2728 _2729 _2730 _2731) = (term524 _2728 _2730 _2729 _2731).
Proof. exact (MK_COMB (@lem132592) (@lem132591 _2728 _2730 _2729 _2731)). Qed.
Lemma lem132615 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : (term522 _2728 _2730 _2729 _2731) = (term522 _2728 _2730 _2729 _2731).
Proof. exact (eq_refl (term522 _2728 _2730 _2729 _2731)). Qed.
Lemma lem132616 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : ((term509 _2728 _2729 _2730 _2731) = (term522 _2728 _2730 _2729 _2731)) = ((term522 _2728 _2730 _2729 _2731) = (term522 _2728 _2730 _2729 _2731)).
Proof. exact (MK_COMB (@lem132593 _2728 _2730 _2729 _2731) (@lem132615 _2728 _2730 _2729 _2731)). Qed.
Lemma lem132618 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem132619 (x : Prop) : (x = x) = True.
Proof. exact (@lem132618 Prop x). Qed.
Lemma lem132620 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : ((term522 _2728 _2730 _2729 _2731) = (term522 _2728 _2730 _2729 _2731)) = True.
Proof. exact (@lem132619 (term522 _2728 _2730 _2729 _2731)). Qed.
Lemma lem132621 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : ((term509 _2728 _2729 _2730 _2731) = (term522 _2728 _2730 _2729 _2731)) = True.
Proof. exact (TRANS (@lem132616 _2728 _2730 _2729 _2731) (@lem132620 _2728 _2730 _2729 _2731)). Qed.
Lemma lem132622 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : True = ((term509 _2728 _2729 _2730 _2731) = (term522 _2728 _2730 _2729 _2731)).
Proof. exact (SYM (@lem132621 _2728 _2730 _2729 _2731)). Qed.
Lemma lem132623 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : (term509 _2728 _2729 _2730 _2731) = (term522 _2728 _2730 _2729 _2731).
Proof. exact (EQ_MP (@lem132622 _2728 _2730 _2729 _2731) (@lem0)). Qed.
Lemma lem132624 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : term522 _2728 _2730 _2729 _2731.
Proof. exact (EQ_MP (@lem132623 _2728 _2730 _2729 _2731) (@lem132462 _2728 _2729 _2730 _2731)). Qed.
Lemma lem132626 (b : Prop) (a : Prop) : (a \/ b) = (term486 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem132627 (_2728 : nat) (_2729 : nat) (_2730 : nat) (_2731 : nat) : (term522 _2728 _2730 _2729 _2731) = (term525 _2728 _2729 _2730 _2731).
Proof. exact (@lem132626 (term526 _2728 _2730 _2729 _2731) ((Nat.mul _2728 _2729) = (Nat.mul _2730 _2731))). Qed.
Lemma lem132629 (a : Prop) (b : Prop) : (term489 a b) = (term490 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem132630 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : (term527 _2728 _2730 _2729 _2731) = (term528 _2728 _2730 _2729 _2731).
Proof. exact (@lem132629 (term483 _2728 _2730) (term483 _2729 _2731)). Qed.
Lemma lem132632 (a : Prop) : (term493 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem132633 (_2728 : nat) (_2730 : nat) : (term494 _2728 _2730) = (_2728 = _2730).
Proof. exact (@lem132632 (_2728 = _2730)). Qed.
Lemma lem132634 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem132635 (_2728 : nat) (_2730 : nat) : (term495 _2728 _2730) = (term496 _2728 _2730).
Proof. exact (MK_COMB (@lem132634) (@lem132633 _2728 _2730)). Qed.
Lemma lem132637 (a : Prop) : (term493 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem132638 (_2729 : nat) (_2731 : nat) : (term494 _2729 _2731) = (_2729 = _2731).
Proof. exact (@lem132637 (_2729 = _2731)). Qed.
Lemma lem132639 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : (term528 _2728 _2730 _2729 _2731) = (term529 _2728 _2730 _2729 _2731).
Proof. exact (MK_COMB (@lem132635 _2728 _2730) (@lem132638 _2729 _2731)). Qed.
Lemma lem132640 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : (term527 _2728 _2730 _2729 _2731) = (term529 _2728 _2730 _2729 _2731).
Proof. exact (TRANS (@lem132630 _2728 _2730 _2729 _2731) (@lem132639 _2728 _2730 _2729 _2731)). Qed.
Lemma lem132641 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem132642 (_2728 : nat) (_2730 : nat) (_2729 : nat) (_2731 : nat) : (term530 _2728 _2730 _2729 _2731) = (term531 _2728 _2730 _2729 _2731).
Proof. exact (MK_COMB (@lem132641) (@lem132640 _2728 _2730 _2729 _2731)). Qed.
Lemma lem132643 (_2728 : nat) (_2729 : nat) (_2730 : nat) (_2731 : nat) : ((Nat.mul _2728 _2729) = (Nat.mul _2730 _2731)) = ((Nat.mul _2728 _2729) = (Nat.mul _2730 _2731)).
Proof. exact (eq_refl ((Nat.mul _2728 _2729) = (Nat.mul _2730 _2731))). Qed.
Lemma lem132644 (_2728 : nat) (_2729 : nat) (_2730 : nat) (_2731 : nat) : (term525 _2728 _2729 _2730 _2731) = (term532 _2728 _2729 _2730 _2731).
Proof. exact (MK_COMB (@lem132642 _2728 _2730 _2729 _2731) (@lem132643 _2728 _2729 _2730 _2731)). Qed.
Lemma lem132645 (_2728 : nat) (_2729 : nat) (_2730 : nat) (_2731 : nat) : (term522 _2728 _2730 _2729 _2731) = (term532 _2728 _2729 _2730 _2731).
Proof. exact (TRANS (@lem132627 _2728 _2729 _2730 _2731) (@lem132644 _2728 _2729 _2730 _2731)). Qed.
Lemma lem132647 (n : nat) (h1 : term122) : term533 n.
Proof. exact (conj (@lem132526 h1) (@lem132534 n)). Qed.
Lemma lem132649 (_2728 : nat) (_2729 : nat) (_2730 : nat) (_2731 : nat) : term532 _2728 _2729 _2730 _2731.
Proof. exact (EQ_MP (@lem132645 _2728 _2729 _2730 _2731) (@lem132624 _2728 _2730 _2729 _2731)). Qed.
Lemma lem132650 (n : nat) : term534 n.
Proof. exact (@lem132649 term514 n term118 n). Qed.
Lemma lem132653 (n : nat) (h1 : term122) : (term535 n) = (term16 n).
Proof. exact (@lem132650 n (@lem132647 n h1)). Qed.
Lemma lem132654 (n : nat) (h1 : term122) : term536 n.
Proof. exact (fun h0 : term537 n => @lem132653 n h1). Qed.
Lemma lem132656 (p : Prop) : (term478 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem132657 (n : nat) : (term536 n) = ((term535 n) = (term16 n)).
Proof. exact (@lem132656 ((term535 n) = (term16 n))). Qed.
Lemma lem132658 (n : nat) (h1 : term122) : (term535 n) = (term16 n).
Proof. exact (EQ_MP (@lem132657 n) (@lem132654 n h1)). Qed.
Lemma lem132660 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem132661 (n : nat) : (term535 n) = (term535 n).
Proof. exact (@lem132660 (term535 n)). Qed.
Lemma lem132662 (n : nat) : term538 n.
Proof. exact (fun h0 : term539 n => @lem132661 n). Qed.
Lemma lem132664 (p : Prop) : (term478 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem132665 (n : nat) : (term538 n) = ((term535 n) = (term535 n)).
Proof. exact (@lem132664 ((term535 n) = (term535 n))). Qed.
Lemma lem132666 (n : nat) : (term535 n) = (term535 n).
Proof. exact (EQ_MP (@lem132665 n) (@lem132662 n)). Qed.
Lemma lem132684 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem132685 (y : nat) (x : nat) (z : nat) : (term540 x y z) = (term541 y x z).
Proof. exact (@lem132684 (y = z) (term483 x z)). Qed.
Lemma lem132695 (x : nat) (y : nat) : (term520 x y) = (term520 x y).
Proof. exact (eq_refl (term520 x y)). Qed.
Lemma lem132696 (y : nat) (x : nat) (z : nat) : (term510 x y z) = (term542 y x z).
Proof. exact (MK_COMB (@lem132695 x y) (@lem132685 y x z)). Qed.
Lemma lem132700 (q : Prop) (p : Prop) (r : Prop) : (term481 p q r) = (term481 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem132701 (y : nat) (x : nat) (z : nat) : (term542 y x z) = (term543 y x z).
Proof. exact (@lem132700 (y = z) (term483 x y) (term483 x z)). Qed.
Lemma lem132723 (y : nat) (x : nat) (z : nat) : (term510 x y z) = (term543 y x z).
Proof. exact (TRANS (@lem132696 y x z) (@lem132701 y x z)). Qed.
Lemma lem132724 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem132725 (y : nat) (x : nat) (z : nat) : (term544 x y z) = (term545 y x z).
Proof. exact (MK_COMB (@lem132724) (@lem132723 y x z)). Qed.
Lemma lem132747 (y : nat) (x : nat) (z : nat) : (term543 y x z) = (term543 y x z).
Proof. exact (eq_refl (term543 y x z)). Qed.
Lemma lem132748 (y : nat) (x : nat) (z : nat) : ((term510 x y z) = (term543 y x z)) = ((term543 y x z) = (term543 y x z)).
Proof. exact (MK_COMB (@lem132725 y x z) (@lem132747 y x z)). Qed.
Lemma lem132750 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem132751 (x : Prop) : (x = x) = True.
Proof. exact (@lem132750 Prop x). Qed.
Lemma lem132752 (y : nat) (x : nat) (z : nat) : ((term543 y x z) = (term543 y x z)) = True.
Proof. exact (@lem132751 (term543 y x z)). Qed.
Lemma lem132753 (y : nat) (x : nat) (z : nat) : ((term510 x y z) = (term543 y x z)) = True.
Proof. exact (TRANS (@lem132748 y x z) (@lem132752 y x z)). Qed.
Lemma lem132754 (y : nat) (x : nat) (z : nat) : True = ((term510 x y z) = (term543 y x z)).
Proof. exact (SYM (@lem132753 y x z)). Qed.
Lemma lem132755 (y : nat) (x : nat) (z : nat) : (term510 x y z) = (term543 y x z).
Proof. exact (EQ_MP (@lem132754 y x z) (@lem0)). Qed.
Lemma lem132756 (y : nat) (x : nat) (z : nat) : term543 y x z.
Proof. exact (EQ_MP (@lem132755 y x z) (@lem132503 x y z)). Qed.
Lemma lem132758 (b : Prop) (a : Prop) : (a \/ b) = (term486 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem132759 (x : nat) (y : nat) (z : nat) : (term543 y x z) = (term546 x y z).
Proof. exact (@lem132758 (term547 y x z) (y = z)). Qed.
Lemma lem132761 (a : Prop) (b : Prop) : (term489 a b) = (term490 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem132762 (y : nat) (x : nat) (z : nat) : (term548 y x z) = (term549 y x z).
Proof. exact (@lem132761 (term483 x y) (term483 x z)). Qed.
Lemma lem132764 (a : Prop) : (term493 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem132765 (x : nat) (y : nat) : (term494 x y) = (x = y).
Proof. exact (@lem132764 (x = y)). Qed.
Lemma lem132766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem132767 (x : nat) (y : nat) : (term495 x y) = (term496 x y).
Proof. exact (MK_COMB (@lem132766) (@lem132765 x y)). Qed.
Lemma lem132769 (a : Prop) : (term493 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem132770 (x : nat) (z : nat) : (term494 x z) = (x = z).
Proof. exact (@lem132769 (x = z)). Qed.
Lemma lem132771 (y : nat) (x : nat) (z : nat) : (term549 y x z) = (term550 y x z).
Proof. exact (MK_COMB (@lem132767 x y) (@lem132770 x z)). Qed.
Lemma lem132772 (y : nat) (x : nat) (z : nat) : (term548 y x z) = (term550 y x z).
Proof. exact (TRANS (@lem132762 y x z) (@lem132771 y x z)). Qed.
Lemma lem132773 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem132774 (y : nat) (x : nat) (z : nat) : (term551 y x z) = (term552 y x z).
Proof. exact (MK_COMB (@lem132773) (@lem132772 y x z)). Qed.
Lemma lem132775 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem132776 (x : nat) (y : nat) (z : nat) : (term546 x y z) = (term553 x y z).
Proof. exact (MK_COMB (@lem132774 y x z) (@lem132775 y z)). Qed.
Lemma lem132777 (x : nat) (y : nat) (z : nat) : (term543 y x z) = (term553 x y z).
Proof. exact (TRANS (@lem132759 x y z) (@lem132776 x y z)). Qed.
Lemma lem132779 (n : nat) (h1 : term122) : term554 n.
Proof. exact (conj (@lem132658 n h1) (@lem132666 n)). Qed.
Lemma lem132781 (x : nat) (y : nat) (z : nat) : term553 x y z.
Proof. exact (EQ_MP (@lem132777 x y z) (@lem132756 y x z)). Qed.
Lemma lem132782 (n : nat) : term555 n.
Proof. exact (@lem132781 (term535 n) (term16 n) (term535 n)). Qed.
Lemma lem132785 (n : nat) (h1 : term122) : (term16 n) = (term535 n).
Proof. exact (@lem132782 n (@lem132779 n h1)). Qed.
Lemma lem132786 (n : nat) (h1 : term122) : term556 n.
Proof. exact (fun h0 : term557 n => @lem132785 n h1). Qed.
Lemma lem132788 (p : Prop) : (term478 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem132789 (n : nat) : (term556 n) = ((term16 n) = (term535 n)).
Proof. exact (@lem132788 ((term16 n) = (term535 n))). Qed.
Lemma lem132790 (n : nat) (h1 : term122) : (term16 n) = (term535 n).
Proof. exact (EQ_MP (@lem132789 n) (@lem132786 n h1)). Qed.
Lemma lem132791 (n : nat) (h1 : term149) (h2 : term122) : term558 n.
Proof. exact (conj (@lem132518 n h1) (@lem132790 n h2)). Qed.
Lemma lem132793 (x : nat) (y : nat) (z : nat) : term553 x y z.
Proof. exact (EQ_MP (@lem132777 x y z) (@lem132756 y x z)). Qed.
Lemma lem132794 (n : nat) : term559 n.
Proof. exact (@lem132793 (term16 n) n (term535 n)). Qed.
Lemma lem132797 (n : nat) (h1 : term149) (h2 : term122) : n = (term535 n).
Proof. exact (@lem132794 n (@lem132791 n h1 h2)). Qed.
Lemma lem132798 (n : nat) (h1 : term149) (h2 : term122) : term560 n.
Proof. exact (fun h0 : term561 n => @lem132797 n h1 h2). Qed.
Lemma lem132800 (p : Prop) : (term478 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem132801 (n : nat) : (term560 n) = (n = (term535 n)).
Proof. exact (@lem132800 (n = (term535 n))). Qed.
Lemma lem132802 (n : nat) (h1 : term149) (h2 : term122) : n = (term535 n).
Proof. exact (EQ_MP (@lem132801 n) (@lem132798 n h1 h2)). Qed.
Lemma lem132804 (a : Prop) (b : Prop) : (term562 a b) = (term563 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem132805 (n : nat) (_2644 : nat) (_2645 : nat) : (term156 n _2644 _2645) = (term155 n _2644 _2645).
Proof. exact (@lem132804 (Coq.Arith.PeanoNat.Nat.Odd _2645) (n = (term157 _2644 _2645))). Qed.
Lemma lem132807 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem132808 (n : nat) (_2644 : nat) (_2645 : nat) : (term155 n _2644 _2645) = (term564 n _2644 _2645).
Proof. exact (@lem132807 (term150 n _2644 _2645)). Qed.
Lemma lem132809 (n : nat) (_2644 : nat) (_2645 : nat) : (term156 n _2644 _2645) = (term564 n _2644 _2645).
Proof. exact (TRANS (@lem132805 n _2644 _2645) (@lem132808 n _2644 _2645)). Qed.
Lemma lem132811 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term149) (h3 : term122) : term565 n.
Proof. exact (conj (@lem132510 n h1) (@lem132802 n h2 h3)). Qed.
Lemma lem132813 (_2644 : nat) (_2645 : nat) (n : nat) (h1 : term350 n) : term564 n _2644 _2645.
Proof. exact (EQ_MP (@lem132809 n _2644 _2645) (@lem131849 _2644 _2645 n h1)). Qed.
Lemma lem132814 (n : nat) (h1 : term350 n) : term566 n.
Proof. exact (@lem132813 (NUMERAL 0) n n h1). Qed.
Lemma lem132817 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term350 n) (h3 : term149) (h4 : term122) : False.
Proof. exact (@lem132814 n h2 (@lem132811 n h1 h3 h4)). Qed.
Lemma lem132818 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term350 n) (h3 : term149) (h4 : term122) : term505.
Proof. exact (fun h0 : ~ False => @lem132817 n h1 h2 h3 h4). Qed.
Lemma lem132820 (p : Prop) : (term478 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem132821 : term505 = False.
Proof. exact (@lem132820 False). Qed.
Lemma lem132822 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term350 n) (h3 : term149) (h4 : term122) : False.
Proof. exact (EQ_MP (@lem132821) (@lem132818 n h1 h2 h3 h4)). Qed.
Lemma lem132823 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term89) (h3 : term378 k m n) : False.
Proof. exact (EQ_MP (@lem132376) (@lem132373 k m n h1 h2 h3)). Qed.
Lemma lem132824 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term350 n) (h3 : term149) (h4 : term122) : (Coq.Arith.PeanoNat.Nat.Odd n) = False.
Proof. exact (prop_ext (fun h5 : Coq.Arith.PeanoNat.Nat.Odd n => @lem132822 n h1 h2 h3 h4) (fun h5 : False => @lem131813 n h1)). Qed.
Lemma lem132825 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term350 n) (h3 : term149) (h4 : term122) : False.
Proof. exact (EQ_MP (@lem132824 n h1 h2 h3 h4) (@lem131813 n h1)). Qed.
Lemma lem132826 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term89) (h3 : term378 k m n) : (Coq.Arith.PeanoNat.Nat.Odd n) = False.
Proof. exact (prop_ext (fun h4 : Coq.Arith.PeanoNat.Nat.Odd n => @lem132823 k m n h1 h2 h3) (fun h4 : False => @lem131739 n h1)). Qed.
Lemma lem132827 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term89) (h3 : term378 k m n) : False.
Proof. exact (EQ_MP (@lem132826 k m n h1 h2 h3) (@lem131739 n h1)). Qed.
Lemma lem132828 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term350 n) (h3 : term149) (h4 : term122) : (Coq.Arith.PeanoNat.Nat.Odd n) = False.
Proof. exact (prop_ext (fun h5 : Coq.Arith.PeanoNat.Nat.Odd n => @lem132825 n h1 h2 h3 h4) (fun h5 : False => @lem131301 n h1)). Qed.
Lemma lem132829 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term350 n) (h3 : term149) (h4 : term122) : False.
Proof. exact (EQ_MP (@lem132828 n h1 h2 h3 h4) (@lem131301 n h1)). Qed.
Lemma lem132830 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term89) (h3 : term378 k m n) : (Coq.Arith.PeanoNat.Nat.Odd n) = False.
Proof. exact (prop_ext (fun h4 : Coq.Arith.PeanoNat.Nat.Odd n => @lem132827 k m n h1 h2 h3) (fun h4 : False => @lem130979 n h1)). Qed.
Lemma lem132831 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term89) (h3 : term378 k m n) : False.
Proof. exact (EQ_MP (@lem132830 k m n h1 h2 h3) (@lem130979 n h1)). Qed.
Lemma lem132832 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term350 n) (h3 : term149) (h4 : term122) : (Coq.Arith.PeanoNat.Nat.Odd n) = False.
Proof. exact (prop_ext (fun h5 : Coq.Arith.PeanoNat.Nat.Odd n => @lem132829 n h1 h2 h3 h4) (fun h5 : False => @lem131301 n h1)). Qed.
Lemma lem132833 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term350 n) (h3 : term149) (h4 : term122) : False.
Proof. exact (EQ_MP (@lem132832 n h1 h2 h3 h4) (@lem131301 n h1)). Qed.
Lemma lem132834 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term89) (h3 : term378 k m n) : (Coq.Arith.PeanoNat.Nat.Odd n) = False.
Proof. exact (prop_ext (fun h4 : Coq.Arith.PeanoNat.Nat.Odd n => @lem132831 k m n h1 h2 h3) (fun h4 : False => @lem130979 n h1)). Qed.
Lemma lem132835 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term89) (h3 : term378 k m n) : False.
Proof. exact (EQ_MP (@lem132834 k m n h1 h2 h3) (@lem130979 n h1)). Qed.
Lemma lem132836 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term149) (h3 : term122) (h4 : term89) (h5 : term412 k m n) : False.
Proof. exact (or_elim (@lem130846 k m n h5) (fun h0 : term378 k m n => @lem132835 k m n h1 h4 h0) (fun h0 : term350 n => @lem132833 n h1 h0 h2 h3)). Qed.
Lemma lem132837 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term149) (h3 : term122) (h4 : term89) (h5 : term412 k m n) : (term412 k m n) = False.
Proof. exact (prop_ext (fun h6 : term412 k m n => @lem132836 k m n h1 h2 h3 h4 h5) (fun h6 : False => @lem130846 k m n h5)). Qed.
Lemma lem132838 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term149) (h3 : term122) (h4 : term89) (h5 : term412 k m n) : False.
Proof. exact (EQ_MP (@lem132837 k m n h1 h2 h3 h4 h5) (@lem130846 k m n h5)). Qed.
Lemma lem132839 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term149) (h3 : term122) (h4 : term89) (h5 : term412 k m n) : term122 = False.
Proof. exact (prop_ext (fun h6 : term122 => @lem132838 k m n h1 h2 h3 h4 h5) (fun h6 : False => @lem130714 h3)). Qed.
Lemma lem132840 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term149) (h3 : term122) (h4 : term89) (h5 : term412 k m n) : False.
Proof. exact (EQ_MP (@lem132839 k m n h1 h2 h3 h4 h5) (@lem130714 h3)). Qed.
Lemma lem132841 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term149) (h3 : term122) (h4 : term89) (h5 : term412 k m n) : term149 = False.
Proof. exact (prop_ext (fun h6 : term149 => @lem132840 k m n h1 h2 h3 h4 h5) (fun h6 : False => @lem130667 h2)). Qed.
Lemma lem132842 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term149) (h3 : term122) (h4 : term89) (h5 : term412 k m n) : False.
Proof. exact (EQ_MP (@lem132841 k m n h1 h2 h3 h4 h5) (@lem130667 h2)). Qed.
Lemma lem132843 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term149) (h3 : term122) (h4 : term89) (h5 : term412 k m n) : (Coq.Arith.PeanoNat.Nat.Odd n) = False.
Proof. exact (prop_ext (fun h6 : Coq.Arith.PeanoNat.Nat.Odd n => @lem132842 k m n h1 h2 h3 h4 h5) (fun h6 : False => @lem130537 n h1)). Qed.
Lemma lem132844 (k : nat) (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term149) (h3 : term122) (h4 : term89) (h5 : term412 k m n) : False.
Proof. exact (EQ_MP (@lem132843 k m n h1 h2 h3 h4 h5) (@lem130537 n h1)). Qed.
Lemma lem132845 (k' : nat -> nat) (k : nat) (m : nat) (n : nat) (h1 : term344 n k') (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term149) (h4 : term122) (h5 : term89) (h6 : term412 k m n) : False.
Proof. exact (ex_elim (@lem130532 n k' h1) (fun m' : nat -> nat => fun h0 : term343 n k' m' => @lem132844 k m n h2 h3 h4 h5 h6)). Qed.
Lemma lem132846 (k : nat) (m : nat) (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term149) (h4 : term122) (h5 : term89) (h6 : term412 k m n) : False.
Proof. exact (ex_elim (@lem130023 n h1) (fun k' : nat -> nat => fun h0 : term345 n k' => @lem132845 k' k m n h0 h2 h3 h4 h5 h6)). Qed.
Lemma lem132847 (k : nat) (n : nat) (h1 : term59 n) (h2 : term415 k n) (h3 : Coq.Arith.PeanoNat.Nat.Odd n) (h4 : term149) (h5 : term122) (h6 : term89) : False.
Proof. exact (ex_elim (@lem130530 k n h2) (fun m : nat => fun h0 : term414 k n m => @lem132846 k m n h1 h3 h4 h5 h6 h0)). Qed.
Lemma lem132848 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) (h4 : term149) (h5 : term122) (h6 : term89) : False.
Proof. exact (ex_elim (@lem130279 n h3) (fun k : nat => fun h0 : term416 n k => @lem132847 k n h1 h0 h2 h4 h5 h6)). Qed.
Lemma lem132849 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) (h4 : term149) (h5 : term122) (h6 : term89) : term122 = False.
Proof. exact (prop_ext (fun h7 : term122 => @lem132848 n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem130392 h5)). Qed.
Lemma lem132850 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) (h4 : term149) (h5 : term122) (h6 : term89) : False.
Proof. exact (EQ_MP (@lem132849 n h1 h2 h3 h4 h5 h6) (@lem130392 h5)). Qed.
Lemma lem132851 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) (h4 : term149) (h5 : term122) (h6 : term89) : term149 = False.
Proof. exact (prop_ext (fun h7 : term149 => @lem132850 n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem130361 h4)). Qed.
Lemma lem132852 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) (h4 : term149) (h5 : term122) (h6 : term89) : False.
Proof. exact (EQ_MP (@lem132851 n h1 h2 h3 h4 h5 h6) (@lem130361 h4)). Qed.
Lemma lem132853 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) (h4 : term149) (h5 : term122) (h6 : term89) : (Coq.Arith.PeanoNat.Nat.Odd n) = False.
Proof. exact (prop_ext (fun h7 : Coq.Arith.PeanoNat.Nat.Odd n => @lem132852 n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem130029 n h2)). Qed.
Lemma lem132854 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) (h4 : term149) (h5 : term122) (h6 : term89) : False.
Proof. exact (EQ_MP (@lem132853 n h1 h2 h3 h4 h5 h6) (@lem130029 n h2)). Qed.
Lemma lem132855 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) (h4 : term149) (h5 : term122) : term567.
Proof. exact (fun h0 : term89 => @lem132854 n h1 h2 h3 h4 h5 h0). Qed.
Lemma lem132856 : term567 = term90.
Proof. exact (@lem69 term89). Qed.
Lemma lem132857 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) (h4 : term149) (h5 : term122) : term90.
Proof. exact (EQ_MP (@lem132856) (@lem132855 n h1 h2 h3 h4 h5)). Qed.
Lemma lem132858 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) (h4 : term149) : term93.
Proof. exact (fun h0 : term122 => @lem132857 n h1 h2 h3 h4 h0). Qed.
Lemma lem132859 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) : term96.
Proof. exact (fun h0 : term149 => @lem132858 n h1 h2 h3 h0). Qed.
Lemma lem132860 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) : term99 n.
Proof. exact (fun h0 : term76 n => @lem132859 n h1 h2 h0). Qed.
Lemma lem132861 (n : nat) (h1 : term59 n) : term102 n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Odd n => @lem132860 n h1 h0). Qed.
Lemma lem132862 (n : nat) : term103 n.
Proof. exact (fun h0 : term59 n => @lem132861 n h0). Qed.
Lemma lem132867 : term107.
Proof. exact (fun n : nat => @lem132862 n). Qed.
Lemma lem132868 : term106.
Proof. exact (EQ_MP (@lem129595) (@lem132867)). Qed.
Lemma lem132869 (n : nat) : term568 n.
Proof. exact (@lem132868 n). Qed.
Lemma lem132870 (n : nat) : (term568 n) = (term77 n).
Proof. exact (eq_refl (term568 n)). Qed.
Lemma lem132871 (n : nat) : term77 n.
Proof. exact (EQ_MP (@lem132870 n) (@lem132869 n)). Qed.
Lemma lem132873 (n : nat) : term77 n.
Proof. exact (@lem129118 n (@lem132871 n)). Qed.
Lemma lem132874 (n : nat) (h1 : term59 n) : term101 n.
Proof. exact (@lem132873 n (@lem129098 n h1)). Qed.
Lemma lem132875 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) : term98 n.
Proof. exact (@lem132874 n h1 (@lem129057 n h2)). Qed.
Lemma lem132876 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) : term95.
Proof. exact (@lem132875 n h1 h2 (@lem129103 n h3)). Qed.
Lemma lem132877 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) : term92.
Proof. exact (@lem132876 n h1 h2 h3 (@lem81645)). Qed.
Lemma lem132878 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) : term81.
Proof. exact (@lem132877 n h1 h2 h3 (@lem86202)). Qed.
Lemma lem132879 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) : False.
Proof. exact (@lem132878 n h1 h2 h3 (@lem124619)). Qed.
Lemma lem132880 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) : (term76 n) = False.
Proof. exact (prop_ext (fun h4 : term76 n => @lem132879 n h1 h2 h3) (fun h4 : False => @lem129103 n h3)). Qed.
Lemma lem132881 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) (h3 : term76 n) : False.
Proof. exact (EQ_MP (@lem132880 n h1 h2 h3) (@lem129103 n h3)). Qed.
Lemma lem132882 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) : term75 n.
Proof. exact (fun h0 : term76 n => @lem132881 n h1 h2 h0). Qed.
Lemma lem132883 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Odd n) : (term52 n) = (term37 n).
Proof. exact (EQ_MP (@lem129102 n) (@lem132882 n h1 h2)). Qed.
Lemma lem132885 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (term39 n).
Proof. exact (EQ_MP (@lem129041 n) (@lem129040 n)). Qed.
Lemma lem132886 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : term39 n.
Proof. exact (EQ_MP (@lem132885 n) (@lem129056 n h1)). Qed.
Lemma lem132887 (n : nat) (h1 : term39 n) : term39 n.
Proof. exact (h1). Qed.
Lemma lem132888 (n : nat) (m : nat) (h1 : n = (term569 m)) : n = (term569 m).
Proof. exact (h1). Qed.
Lemma lem132889 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem132890 (n : nat) (m : nat) (h1 : n = (term569 m)) : (term51 n) = (term570 m).
Proof. exact (MK_COMB (@lem132889) (@lem132888 n m h1)). Qed.
Lemma lem132891 (m : nat) : (term570 m) = ((term571 m) = (term572 m)).
Proof. exact (eq_refl (term570 m)). Qed.
Lemma lem132892 (n : nat) : (term573 n) = (term573 n).
Proof. exact (eq_refl (term573 n)). Qed.
Lemma lem132893 (n : nat) (m : nat) : ((term51 n) = (term570 m)) = ((term51 n) = ((term571 m) = (term572 m))).
Proof. exact (MK_COMB (@lem132892 n) (@lem132891 m)). Qed.
Lemma lem132894 (n : nat) : (term51 n) = ((term52 n) = (term37 n)).
Proof. exact (eq_refl (term51 n)). Qed.
Lemma lem132895 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem132896 (n : nat) : (term573 n) = (term574 n).
Proof. exact (MK_COMB (@lem132895) (@lem132894 n)). Qed.
Lemma lem132897 (m : nat) : ((term571 m) = (term572 m)) = ((term571 m) = (term572 m)).
Proof. exact (eq_refl ((term571 m) = (term572 m))). Qed.
Lemma lem132898 (n : nat) (m : nat) : ((term51 n) = ((term571 m) = (term572 m))) = (((term52 n) = (term37 n)) = ((term571 m) = (term572 m))).
Proof. exact (MK_COMB (@lem132896 n) (@lem132897 m)). Qed.
Lemma lem132899 (n : nat) (m : nat) : ((term51 n) = (term570 m)) = (((term52 n) = (term37 n)) = ((term571 m) = (term572 m))).
Proof. exact (TRANS (@lem132893 n m) (@lem132898 n m)). Qed.
Lemma lem132900 (n : nat) (m : nat) (h1 : n = (term569 m)) : ((term52 n) = (term37 n)) = ((term571 m) = (term572 m)).
Proof. exact (EQ_MP (@lem132899 n m) (@lem132890 n m h1)). Qed.
Lemma lem132901 (n : nat) (m : nat) (h1 : n = (term569 m)) : ((term571 m) = (term572 m)) = ((term52 n) = (term37 n)).
Proof. exact (SYM (@lem132900 n m h1)). Qed.
Lemma lem132902 : term575 = term575.
Proof. exact (eq_refl term575). Qed.
Lemma lem132903 (n : nat) (m : nat) (h1 : n = (term569 m)) : (term576 n) = (term577 m).
Proof. exact (MK_COMB (@lem132902) (@lem132888 n m h1)). Qed.
Lemma lem132904 (m : nat) : (term577 m) = (term578 m).
Proof. exact (eq_refl (term577 m)). Qed.
Lemma lem132905 (n : nat) : (term579 n) = (term579 n).
Proof. exact (eq_refl (term579 n)). Qed.
Lemma lem132906 (n : nat) (m : nat) : ((term576 n) = (term577 m)) = ((term576 n) = (term578 m)).
Proof. exact (MK_COMB (@lem132905 n) (@lem132904 m)). Qed.
Lemma lem132907 (n : nat) : (term576 n) = (term59 n).
Proof. exact (eq_refl (term576 n)). Qed.
Lemma lem132908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem132909 (n : nat) : (term579 n) = (term580 n).
Proof. exact (MK_COMB (@lem132908) (@lem132907 n)). Qed.
Lemma lem132910 (m : nat) : (term578 m) = (term578 m).
Proof. exact (eq_refl (term578 m)). Qed.
Lemma lem132911 (n : nat) (m : nat) : ((term576 n) = (term578 m)) = ((term59 n) = (term578 m)).
Proof. exact (MK_COMB (@lem132909 n) (@lem132910 m)). Qed.
Lemma lem132912 (n : nat) (m : nat) : ((term576 n) = (term577 m)) = ((term59 n) = (term578 m)).
Proof. exact (TRANS (@lem132906 n m) (@lem132911 n m)). Qed.
Lemma lem132913 (n : nat) (m : nat) (h1 : n = (term569 m)) : (term59 n) = (term578 m).
Proof. exact (EQ_MP (@lem132912 n m) (@lem132903 n m h1)). Qed.
Lemma lem132914 (n : nat) (m : nat) (h1 : term59 n) (h2 : n = (term569 m)) : term578 m.
Proof. exact (EQ_MP (@lem132913 n m h2) (@lem129098 n h1)). Qed.
Lemma lem132915 (n : nat) (m : nat) (h1 : term59 n) (h2 : n = (term569 m)) : term581 m.
Proof. exact (@lem132914 n m h1 h2 m). Qed.
Lemma lem132916 (m : nat) : (term581 m) = (term582 m).
Proof. exact (eq_refl (term581 m)). Qed.
Lemma lem132917 (n : nat) (m : nat) (h1 : term59 n) (h2 : n = (term569 m)) : term582 m.
Proof. exact (EQ_MP (@lem132916 m) (@lem132915 n m h1 h2)). Qed.
Lemma lem132918 (m : nat) : term21 m.
Proof. exact (@lem83870 m). Qed.
Lemma lem132919 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem132920 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem132919 m) (@lem132918 m)). Qed.
Lemma lem132921 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem132920 m n). Qed.
Lemma lem132922 (m : nat) (n : nat) : (term23 m n) = (((Nat.mul m n) = (NUMERAL 0)) = (term24 m n)).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem132929 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem132930 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem132931 (m : nat) (h1 : m = (NUMERAL 0)) : (Peano.lt m) = term583.
Proof. exact (MK_COMB (@lem132930) (@lem132929 m h1)). Qed.
Lemma lem132933 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem132934 : term584 = term584.
Proof. exact (eq_refl term584). Qed.
Lemma lem132935 (m : nat) (h1 : m = (NUMERAL 0)) : (term569 m) = term585.
Proof. exact (MK_COMB (@lem132934) (@lem132933 m h1)). Qed.
Lemma lem132936 (m : nat) (h1 : m = (NUMERAL 0)) : (term586 m) = term587.
Proof. exact (MK_COMB (@lem132931 m h1) (@lem132935 m h1)). Qed.
Lemma lem132937 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem132938 (m : nat) (h1 : m = (NUMERAL 0)) : (term588 m) = term589.
Proof. exact (MK_COMB (@lem132937) (@lem132936 m h1)). Qed.
Lemma lem132954 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem132955 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem132956 (m : nat) (h1 : m = (NUMERAL 0)) : (@eq nat m) = term590.
Proof. exact (MK_COMB (@lem132955) (@lem132954 m h1)). Qed.
Lemma lem132957 (k : nat) (m'' : nat) : (term157 k m'') = (term157 k m'').
Proof. exact (eq_refl (term157 k m'')). Qed.
Lemma lem132958 (k : nat) (m'' : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (m = (term157 k m'')) = ((NUMERAL 0) = (term157 k m'')).
Proof. exact (MK_COMB (@lem132956 m h1) (@lem132957 k m'')). Qed.
Lemma lem132961 (m'' : nat) : (term591 m'') = (term591 m'').
Proof. exact (eq_refl (term591 m'')). Qed.
Lemma lem132962 (k : nat) (m'' : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term150 m k m'') = (term592 k m'').
Proof. exact (MK_COMB (@lem132961 m'') (@lem132958 k m'' m h1)). Qed.
Lemma lem132965 (k : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term151 m k) = (term593 k).
Proof. exact (fun_ext (fun m'' : nat => @lem132962 k m'' m h1)). Qed.
Lemma lem132966 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem132967 (k : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term152 m k) = (term594 k).
Proof. exact (MK_COMB (@lem132966) (@lem132965 k m h1)). Qed.
Lemma lem132972 (m : nat) (h1 : m = (NUMERAL 0)) : (term153 m) = term595.
Proof. exact (fun_ext (fun k : nat => @lem132967 k m h1)). Qed.
Lemma lem132973 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem132974 (m : nat) (h1 : m = (NUMERAL 0)) : (term52 m) = term596.
Proof. exact (MK_COMB (@lem132973) (@lem132972 m h1)). Qed.
Lemma lem132979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem132980 (m : nat) (h1 : m = (NUMERAL 0)) : (term154 m) = term597.
Proof. exact (MK_COMB (@lem132979) (@lem132974 m h1)). Qed.
Lemma lem132984 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem132985 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem132986 (m : nat) (h1 : m = (NUMERAL 0)) : (@eq nat m) = term590.
Proof. exact (MK_COMB (@lem132985) (@lem132984 m h1)). Qed.
Lemma lem132987 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem132988 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem132986 m h1) (@lem132987)). Qed.
Lemma lem132990 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem132991 (x : nat) : (x = x) = True.
Proof. exact (@lem132990 nat x). Qed.
Lemma lem132992 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem132991 (NUMERAL 0)). Qed.
Lemma lem132993 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem132988 m h1) (@lem132992)). Qed.
Lemma lem132994 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem132995 (m : nat) (h1 : m = (NUMERAL 0)) : (term37 m) = (~ True).
Proof. exact (MK_COMB (@lem132994) (@lem132993 m h1)). Qed.
Lemma lem132997 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem132998 (m : nat) (h1 : m = (NUMERAL 0)) : (term37 m) = False.
Proof. exact (TRANS (@lem132995 m h1) (@lem132997)). Qed.
Lemma lem132999 (m : nat) (h1 : m = (NUMERAL 0)) : ((term52 m) = (term37 m)) = (term596 = False).
Proof. exact (MK_COMB (@lem132980 m h1) (@lem132998 m h1)). Qed.
Lemma lem133001 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem133002 : (term596 = False) = term598.
Proof. exact (@lem133001 term596). Qed.
Lemma lem133015 (m : nat) (h1 : m = (NUMERAL 0)) : ((term52 m) = (term37 m)) = term598.
Proof. exact (TRANS (@lem132999 m h1) (@lem133002)). Qed.
Lemma lem133016 (m : nat) (h1 : m = (NUMERAL 0)) : (term582 m) = term599.
Proof. exact (MK_COMB (@lem132938 m h1) (@lem133015 m h1)). Qed.
Lemma lem133019 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem133020 (m : nat) (h1 : m = (NUMERAL 0)) : (term600 m) = term601.
Proof. exact (MK_COMB (@lem133019) (@lem133016 m h1)). Qed.
Lemma lem133036 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem133037 : term584 = term584.
Proof. exact (eq_refl term584). Qed.
Lemma lem133038 (m : nat) (h1 : m = (NUMERAL 0)) : (term569 m) = term585.
Proof. exact (MK_COMB (@lem133037) (@lem133036 m h1)). Qed.
Lemma lem133039 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem133040 (m : nat) (h1 : m = (NUMERAL 0)) : (term602 m) = term603.
Proof. exact (MK_COMB (@lem133039) (@lem133038 m h1)). Qed.
Lemma lem133041 (k : nat) (m' : nat) : (term157 k m') = (term157 k m').
Proof. exact (eq_refl (term157 k m')). Qed.
Lemma lem133042 (k : nat) (m' : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((term569 m) = (term157 k m')) = (term585 = (term157 k m')).
Proof. exact (MK_COMB (@lem133040 m h1) (@lem133041 k m')). Qed.
Lemma lem133045 (m' : nat) : (term591 m') = (term591 m').
Proof. exact (eq_refl (term591 m')). Qed.
Lemma lem133046 (k : nat) (m' : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term604 m k m') = (term605 k m').
Proof. exact (MK_COMB (@lem133045 m') (@lem133042 k m' m h1)). Qed.
Lemma lem133049 (k : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term606 m k) = (term607 k).
Proof. exact (fun_ext (fun m' : nat => @lem133046 k m' m h1)). Qed.
Lemma lem133050 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem133051 (k : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term608 m k) = (term609 k).
Proof. exact (MK_COMB (@lem133050) (@lem133049 k m h1)). Qed.
Lemma lem133056 (m : nat) (h1 : m = (NUMERAL 0)) : (term610 m) = term611.
Proof. exact (fun_ext (fun k : nat => @lem133051 k m h1)). Qed.
Lemma lem133057 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem133058 (m : nat) (h1 : m = (NUMERAL 0)) : (term571 m) = term612.
Proof. exact (MK_COMB (@lem133057) (@lem133056 m h1)). Qed.
Lemma lem133063 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem133064 (m : nat) (h1 : m = (NUMERAL 0)) : (term613 m) = term614.
Proof. exact (MK_COMB (@lem133063) (@lem133058 m h1)). Qed.
Lemma lem133066 (m : nat) (n : nat) : ((Nat.mul m n) = (NUMERAL 0)) = (term24 m n).
Proof. exact (EQ_MP (@lem132922 m n) (@lem132921 m n)). Qed.
Lemma lem133067 (m : nat) : ((term569 m) = (NUMERAL 0)) = (term615 m).
Proof. exact (@lem133066 term8 m). Qed.
Lemma lem133075 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem133076 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem133077 (m : nat) (h1 : m = (NUMERAL 0)) : (@eq nat m) = term590.
Proof. exact (MK_COMB (@lem133076) (@lem133075 m h1)). Qed.
Lemma lem133078 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem133079 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem133077 m h1) (@lem133078)). Qed.
Lemma lem133081 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem133082 (x : nat) : (x = x) = True.
Proof. exact (@lem133081 nat x). Qed.
Lemma lem133083 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem133082 (NUMERAL 0)). Qed.
Lemma lem133084 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem133079 m h1) (@lem133083)). Qed.
Lemma lem133085 : term616 = term616.
Proof. exact (eq_refl term616). Qed.
Lemma lem133086 (m : nat) (h1 : m = (NUMERAL 0)) : (term615 m) = term617.
Proof. exact (MK_COMB (@lem133085) (@lem133084 m h1)). Qed.
Lemma lem133088 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem133089 : term617 = True.
Proof. exact (@lem133088 (term8 = (NUMERAL 0))). Qed.
Lemma lem133090 (m : nat) (h1 : m = (NUMERAL 0)) : (term615 m) = True.
Proof. exact (TRANS (@lem133086 m h1) (@lem133089)). Qed.
Lemma lem133091 (m : nat) (h1 : m = (NUMERAL 0)) : ((term569 m) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem133067 m) (@lem133090 m h1)). Qed.
Lemma lem133092 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem133093 (m : nat) (h1 : m = (NUMERAL 0)) : (term572 m) = (~ True).
Proof. exact (MK_COMB (@lem133092) (@lem133091 m h1)). Qed.
Lemma lem133095 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem133096 (m : nat) (h1 : m = (NUMERAL 0)) : (term572 m) = False.
Proof. exact (TRANS (@lem133093 m h1) (@lem133095)). Qed.
Lemma lem133097 (m : nat) (h1 : m = (NUMERAL 0)) : ((term571 m) = (term572 m)) = (term612 = False).
Proof. exact (MK_COMB (@lem133064 m h1) (@lem133096 m h1)). Qed.
Lemma lem133099 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem133100 : (term612 = False) = term618.
Proof. exact (@lem133099 term612). Qed.
Lemma lem133113 (m : nat) (h1 : m = (NUMERAL 0)) : ((term571 m) = (term572 m)) = term618.
Proof. exact (TRANS (@lem133097 m h1) (@lem133100)). Qed.
Lemma lem133114 (m : nat) (h1 : m = (NUMERAL 0)) : (term619 m) = term620.
Proof. exact (MK_COMB (@lem133020 m h1) (@lem133113 m h1)). Qed.
Lemma lem133117 (m : nat) (h1 : m = (NUMERAL 0)) : term620 = (term619 m).
Proof. exact (SYM (@lem133114 m h1)). Qed.
Lemma lem133118 (m : nat) : term21 m.
Proof. exact (@lem83870 m). Qed.
Lemma lem133119 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem133120 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem133119 m) (@lem133118 m)). Qed.
Lemma lem133121 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem133120 m n). Qed.
Lemma lem133122 (m : nat) (n : nat) : (term23 m n) = (((Nat.mul m n) = (NUMERAL 0)) = (term24 m n)).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem133124 (m : nat) : term621 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem133156 (m : nat) (h1 : term37 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem133124 m (@lem129039 m h1)). Qed.
Lemma lem133157 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem133158 (m : nat) (h1 : term37 m) : (term37 m) = (~ False).
Proof. exact (MK_COMB (@lem133157) (@lem133156 m h1)). Qed.
Lemma lem133160 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem133161 (m : nat) (h1 : term37 m) : (term37 m) = True.
Proof. exact (TRANS (@lem133158 m h1) (@lem133160)). Qed.
Lemma lem133162 (m : nat) : (term154 m) = (term154 m).
Proof. exact (eq_refl (term154 m)). Qed.
Lemma lem133163 (m : nat) (h1 : term37 m) : ((term52 m) = (term37 m)) = ((term52 m) = True).
Proof. exact (MK_COMB (@lem133162 m) (@lem133161 m h1)). Qed.
Lemma lem133165 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem133166 (m : nat) : ((term52 m) = True) = (term52 m).
Proof. exact (@lem133165 (term52 m)). Qed.
Lemma lem133179 (m : nat) (h1 : term37 m) : ((term52 m) = (term37 m)) = (term52 m).
Proof. exact (TRANS (@lem133163 m h1) (@lem133166 m)). Qed.
Lemma lem133180 (m : nat) : (term588 m) = (term588 m).
Proof. exact (eq_refl (term588 m)). Qed.
Lemma lem133181 (m : nat) (h1 : term37 m) : (term582 m) = (term622 m).
Proof. exact (MK_COMB (@lem133180 m) (@lem133179 m h1)). Qed.
Lemma lem133184 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem133185 (m : nat) (h1 : term37 m) : (term600 m) = (term623 m).
Proof. exact (MK_COMB (@lem133184) (@lem133181 m h1)). Qed.
Lemma lem133201 (m : nat) (n : nat) : ((Nat.mul m n) = (NUMERAL 0)) = (term24 m n).
Proof. exact (EQ_MP (@lem133122 m n) (@lem133121 m n)). Qed.
Lemma lem133202 (m : nat) : ((term569 m) = (NUMERAL 0)) = (term615 m).
Proof. exact (@lem133201 term8 m). Qed.
Lemma lem133208 (m : nat) (h1 : term37 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem133124 m (@lem129039 m h1)). Qed.
Lemma lem133209 : term616 = term616.
Proof. exact (eq_refl term616). Qed.
Lemma lem133210 (m : nat) (h1 : term37 m) : (term615 m) = term624.
Proof. exact (MK_COMB (@lem133209) (@lem133208 m h1)). Qed.
Lemma lem133212 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem133213 : term624 = (term8 = (NUMERAL 0)).
Proof. exact (@lem133212 (term8 = (NUMERAL 0))). Qed.
Lemma lem133216 (m : nat) (h1 : term37 m) : (term615 m) = (term8 = (NUMERAL 0)).
Proof. exact (TRANS (@lem133210 m h1) (@lem133213)). Qed.
Lemma lem133217 (m : nat) (h1 : term37 m) : ((term569 m) = (NUMERAL 0)) = (term8 = (NUMERAL 0)).
Proof. exact (TRANS (@lem133202 m) (@lem133216 m h1)). Qed.
Lemma lem133218 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem133219 (m : nat) (h1 : term37 m) : (term572 m) = term625.
Proof. exact (MK_COMB (@lem133218) (@lem133217 m h1)). Qed.
Lemma lem133220 (m : nat) : (term613 m) = (term613 m).
Proof. exact (eq_refl (term613 m)). Qed.
Lemma lem133221 (m : nat) (h1 : term37 m) : ((term571 m) = (term572 m)) = ((term571 m) = term625).
Proof. exact (MK_COMB (@lem133220 m) (@lem133219 m h1)). Qed.
Lemma lem133224 (m : nat) (h1 : term37 m) : (term619 m) = (term626 m).
Proof. exact (MK_COMB (@lem133185 m h1) (@lem133221 m h1)). Qed.
Lemma lem133227 (m : nat) (h1 : term37 m) : (term626 m) = (term619 m).
Proof. exact (SYM (@lem133224 m h1)). Qed.
Lemma lem133233 (m : nat) : (term34 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem129029 m) (@lem129028 m)). Qed.
Lemma lem133234 : term585 = (NUMERAL 0).
Proof. exact (@lem133233 term8). Qed.
Lemma lem133235 : term583 = term583.
Proof. exact (eq_refl term583). Qed.
Lemma lem133236 : term587 = term627.
Proof. exact (MK_COMB (@lem133235) (@lem133234)). Qed.
Lemma lem133238 (m : nat) : (term31 m) = False.
Proof. exact (EQ_MP (@lem128999 m) (@lem128998 m)). Qed.
Lemma lem133239 : term627 = False.
Proof. exact (@lem133238 (NUMERAL 0)). Qed.
Lemma lem133240 : term587 = False.
Proof. exact (TRANS (@lem133236) (@lem133239)). Qed.
Lemma lem133241 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem133242 : term589 = (imp False).
Proof. exact (MK_COMB (@lem133241) (@lem133240)). Qed.
Lemma lem133255 : term598 = term598.
Proof. exact (eq_refl term598). Qed.
Lemma lem133256 : term599 = term628.
Proof. exact (MK_COMB (@lem133242) (@lem133255)). Qed.
Lemma lem133258 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem133259 : term628 = True.
Proof. exact (@lem133258 term598). Qed.
Lemma lem133260 : term599 = True.
Proof. exact (TRANS (@lem133256) (@lem133259)). Qed.
Lemma lem133261 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem133262 : term601 = (imp True).
Proof. exact (MK_COMB (@lem133261) (@lem133260)). Qed.
Lemma lem133276 (m : nat) : (term34 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem129029 m) (@lem129028 m)). Qed.
Lemma lem133277 : term585 = (NUMERAL 0).
Proof. exact (@lem133276 term8). Qed.
Lemma lem133278 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem133279 : term603 = term590.
Proof. exact (MK_COMB (@lem133278) (@lem133277)). Qed.
Lemma lem133280 (k : nat) (m' : nat) : (term157 k m') = (term157 k m').
Proof. exact (eq_refl (term157 k m')). Qed.
Lemma lem133281 (k : nat) (m' : nat) : (term585 = (term157 k m')) = ((NUMERAL 0) = (term157 k m')).
Proof. exact (MK_COMB (@lem133279) (@lem133280 k m')). Qed.
Lemma lem133284 (m' : nat) : (term591 m') = (term591 m').
Proof. exact (eq_refl (term591 m')). Qed.
Lemma lem133285 (k : nat) (m' : nat) : (term605 k m') = (term592 k m').
Proof. exact (MK_COMB (@lem133284 m') (@lem133281 k m')). Qed.
Lemma lem133288 (k : nat) : (term607 k) = (term593 k).
Proof. exact (fun_ext (fun m' : nat => @lem133285 k m')). Qed.
Lemma lem133289 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem133290 (k : nat) : (term609 k) = (term594 k).
Proof. exact (MK_COMB (@lem133289) (@lem133288 k)). Qed.
Lemma lem133295 : term611 = term595.
Proof. exact (fun_ext (fun k : nat => @lem133290 k)). Qed.
Lemma lem133296 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem133297 : term612 = term596.
Proof. exact (MK_COMB (@lem133296) (@lem133295)). Qed.
Lemma lem133302 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem133303 : term618 = term598.
Proof. exact (MK_COMB (@lem133302) (@lem133297)). Qed.
Lemma lem133304 : term620 = term629.
Proof. exact (MK_COMB (@lem133262) (@lem133303)). Qed.
Lemma lem133306 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem133307 : term629 = term598.
Proof. exact (@lem133306 term598). Qed.
Lemma lem133320 : term620 = term598.
Proof. exact (TRANS (@lem133304) (@lem133307)). Qed.
Lemma lem133321 : term598 = term620.
Proof. exact (SYM (@lem133320)). Qed.
Lemma lem133327 (k : nat) (m' : nat) (h1 : (NUMERAL 0) = (term157 k m')) : (NUMERAL 0) = (term157 k m').
Proof. exact (h1). Qed.
Lemma lem133328 (k : nat) (m' : nat) (h1 : (NUMERAL 0) = (term157 k m')) : (term157 k m') = (NUMERAL 0).
Proof. exact (SYM (@lem133327 k m' h1)). Qed.
Lemma lem133329 (k : nat) (m' : nat) (h1 : (term157 k m') = (NUMERAL 0)) : (term157 k m') = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem133330 (k : nat) (m' : nat) (h1 : (term157 k m') = (NUMERAL 0)) : (NUMERAL 0) = (term157 k m').
Proof. exact (SYM (@lem133329 k m' h1)). Qed.
Lemma lem133331 (k : nat) (m' : nat) : ((NUMERAL 0) = (term157 k m')) = ((term157 k m') = (NUMERAL 0)).
Proof. exact (prop_ext (fun h1 : (NUMERAL 0) = (term157 k m') => @lem133328 k m' h1) (fun h1 : (term157 k m') = (NUMERAL 0) => @lem133330 k m' h1)). Qed.
Lemma lem133332 (m' : nat) : (term591 m') = (term591 m').
Proof. exact (eq_refl (term591 m')). Qed.
Lemma lem133333 (k : nat) (m' : nat) : (term592 k m') = (term630 k m').
Proof. exact (MK_COMB (@lem133332 m') (@lem133331 k m')). Qed.
Lemma lem133334 (k : nat) : (term593 k) = (term631 k).
Proof. exact (fun_ext (fun m' : nat => @lem133333 k m')). Qed.
Lemma lem133335 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem133336 (k : nat) : (term594 k) = (term632 k).
Proof. exact (MK_COMB (@lem133335) (@lem133334 k)). Qed.
Lemma lem133337 : term595 = term633.
Proof. exact (fun_ext (fun k : nat => @lem133336 k)). Qed.
Lemma lem133338 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem133339 : term596 = term634.
Proof. exact (MK_COMB (@lem133338) (@lem133337)). Qed.
Lemma lem133340 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem133341 : term598 = term635.
Proof. exact (MK_COMB (@lem133340) (@lem133339)). Qed.
Lemma lem133342 : term635 = term598.
Proof. exact (SYM (@lem133341)). Qed.
Lemma lem133354 (m : nat) (n : nat) : ((Nat.mul m n) = (NUMERAL 0)) = (term24 m n).
Proof. exact (EQ_MP (@lem128982 m n) (@lem128981 m n)). Qed.
Lemma lem133355 (k : nat) (m' : nat) : ((term157 k m') = (NUMERAL 0)) = (term636 k m').
Proof. exact (@lem133354 (term637 k) m'). Qed.
Lemma lem133359 (m : nat) (n : nat) : ((Nat.pow m n) = (NUMERAL 0)) = (term28 m n).
Proof. exact (EQ_MP (@lem128988 m n) (@lem128987 m n)). Qed.
Lemma lem133360 (k : nat) : ((term637 k) = (NUMERAL 0)) = (term638 k).
Proof. exact (@lem133359 term8 k). Qed.
Lemma lem133366 : term8 = term9.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem133367 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem133368 : term639 = term640.
Proof. exact (MK_COMB (@lem133367) (@lem133366)). Qed.
Lemma lem133369 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem133370 : (term8 = (NUMERAL 0)) = (term9 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem133368) (@lem133369)). Qed.
Lemma lem133372 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem128965 n (@lem128964 n)). Qed.
Lemma lem133373 : (term9 = (NUMERAL 0)) = False.
Proof. exact (@lem133372 term118). Qed.
Lemma lem133374 : (term8 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem133370) (@lem133373)). Qed.
Lemma lem133375 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem133376 : term641 = (and False).
Proof. exact (MK_COMB (@lem133375) (@lem133374)). Qed.
Lemma lem133379 (k : nat) : (term37 k) = (term37 k).
Proof. exact (eq_refl (term37 k)). Qed.
Lemma lem133380 (k : nat) : (term638 k) = (term642 k).
Proof. exact (MK_COMB (@lem133376) (@lem133379 k)). Qed.
Lemma lem133382 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem133383 (k : nat) : (term642 k) = False.
Proof. exact (@lem133382 (term37 k)). Qed.
Lemma lem133384 (k : nat) : (term638 k) = False.
Proof. exact (TRANS (@lem133380 k) (@lem133383 k)). Qed.
Lemma lem133385 (k : nat) : ((term637 k) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem133360 k) (@lem133384 k)). Qed.
Lemma lem133386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem133387 (k : nat) : (term643 k) = (or False).
Proof. exact (MK_COMB (@lem133386) (@lem133385 k)). Qed.
Lemma lem133390 (m' : nat) : (m' = (NUMERAL 0)) = (m' = (NUMERAL 0)).
Proof. exact (eq_refl (m' = (NUMERAL 0))). Qed.
Lemma lem133391 (k : nat) (m' : nat) : (term636 k m') = (term644 m').
Proof. exact (MK_COMB (@lem133387 k) (@lem133390 m')). Qed.
Lemma lem133393 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem133394 (m' : nat) : (term644 m') = (m' = (NUMERAL 0)).
Proof. exact (@lem133393 (m' = (NUMERAL 0))). Qed.
Lemma lem133397 (k : nat) (m' : nat) : (term636 k m') = (m' = (NUMERAL 0)).
Proof. exact (TRANS (@lem133391 k m') (@lem133394 m')). Qed.
Lemma lem133398 (k : nat) (m' : nat) : ((term157 k m') = (NUMERAL 0)) = (m' = (NUMERAL 0)).
Proof. exact (TRANS (@lem133355 k m') (@lem133397 k m')). Qed.
Lemma lem133399 (m' : nat) : (term591 m') = (term591 m').
Proof. exact (eq_refl (term591 m')). Qed.
Lemma lem133400 (k : nat) (m' : nat) : (term630 k m') = (term645 m').
Proof. exact (MK_COMB (@lem133399 m') (@lem133398 k m')). Qed.
Lemma lem133403 (k : nat) : (term631 k) = term646.
Proof. exact (fun_ext (fun m' : nat => @lem133400 k m')). Qed.
Lemma lem133404 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem133405 (k : nat) : (term632 k) = term647.
Proof. exact (MK_COMB (@lem133404) (@lem133403 k)). Qed.
Lemma lem133410 : term633 = term648.
Proof. exact (fun_ext (fun k : nat => @lem133405 k)). Qed.
Lemma lem133411 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem133412 : term634 = term649.
Proof. exact (MK_COMB (@lem133411) (@lem133410)). Qed.
Lemma lem133414 {A : Type'} (t : Prop) : (term650 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem133415 (t : Prop) : (term651 t) = t.
Proof. exact (@lem133414 nat t). Qed.
Lemma lem133416 : term649 = term647.
Proof. exact (@lem133415 term647). Qed.
Lemma lem133425 : term634 = term647.
Proof. exact (TRANS (@lem133412) (@lem133416)). Qed.
Lemma lem133426 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem133427 : term635 = term652.
Proof. exact (MK_COMB (@lem133426) (@lem133425)). Qed.
Lemma lem133428 : term652 = term635.
Proof. exact (SYM (@lem133427)). Qed.
Lemma lem133429 (h1 : term647) : term647.
Proof. exact (h1). Qed.
Lemma lem133432 (h1 : term653) : term653.
Proof. exact (h1). Qed.
Lemma lem133433 : term654.
Proof. exact (fun h0 : term653 => @lem133432 h0). Qed.
Lemma lem133434 (h1 : term654) : term654.
Proof. exact (h1). Qed.
Lemma lem133435 (h1 : term653) : term653.
Proof. exact (h1). Qed.
Lemma lem133436 (h1 : term653) (h2 : term654) : term653.
Proof. exact (@lem133434 h2 (@lem133435 h1)). Qed.
Lemma lem133437 (h1 : term653) : term655.
Proof. exact (fun h0 : term654 => @lem133436 h1 h0). Qed.
Lemma lem133438 (h1 : term654) : term654.
Proof. exact (h1). Qed.
Lemma lem133439 (h1 : term653) (h2 : term654) : term653.
Proof. exact (@lem133437 h1 (@lem133438 h2)). Qed.
Lemma lem133440 (h1 : term654) : term654.
Proof. exact (fun h0 : term653 => @lem133439 h0 h1). Qed.
Lemma lem133441 : term656.
Proof. exact (fun h0 : term654 => @lem133440 h0). Qed.
Lemma lem133444 : term654.
Proof. exact (@lem133441 (@lem133433)). Qed.
Lemma lem133478 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem133479 : term81 = term82.
Proof. exact (@lem133478 term83). Qed.
Lemma lem133483 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem133484 : (term84 = False) = term85.
Proof. exact (@lem133483 term84). Qed.
Lemma lem133485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem133486 : term86 = term87.
Proof. exact (MK_COMB (@lem133485) (@lem133484)). Qed.
Lemma lem133491 : term88 = term88.
Proof. exact (eq_refl term88). Qed.
Lemma lem133492 : term83 = term89.
Proof. exact (MK_COMB (@lem133486) (@lem133491)). Qed.
Lemma lem133495 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem133496 : term82 = term90.
Proof. exact (MK_COMB (@lem133495) (@lem133492)). Qed.
Lemma lem133497 : term81 = term90.
Proof. exact (TRANS (@lem133479) (@lem133496)). Qed.
Lemma lem133498 : term657 = term657.
Proof. exact (eq_refl term657). Qed.
Lemma lem133505 : term653 = term658.
Proof. exact (MK_COMB (@lem133498) (@lem133497)). Qed.
Lemma lem133512 (n : nat) : ((term108 n) = (term109 n)) = ((term108 n) = (term109 n)).
Proof. exact (eq_refl ((term108 n) = (term109 n))). Qed.
Lemma lem133513 : term110 = term110.
Proof. exact (fun_ext (fun n : nat => @lem133512 n)). Qed.
Lemma lem133514 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem133515 : term88 = term88.
Proof. exact (MK_COMB (@lem133514) (@lem133513)). Qed.
Lemma lem133520 : term87 = term87.
Proof. exact (eq_refl term87). Qed.
Lemma lem133521 : term89 = term89.
Proof. exact (MK_COMB (@lem133520) (@lem133515)). Qed.
Lemma lem133522 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem133523 : term90 = term90.
Proof. exact (MK_COMB (@lem133522) (@lem133521)). Qed.
Lemma lem133528 (m' : nat) : (term645 m') = (term645 m').
Proof. exact (eq_refl (term645 m')). Qed.
Lemma lem133529 : term646 = term646.
Proof. exact (fun_ext (fun m' : nat => @lem133528 m')). Qed.
Lemma lem133530 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem133531 : term647 = term647.
Proof. exact (MK_COMB (@lem133530) (@lem133529)). Qed.
Lemma lem133532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem133533 : term657 = term657.
Proof. exact (MK_COMB (@lem133532) (@lem133531)). Qed.
Lemma lem133534 : term658 = term658.
Proof. exact (MK_COMB (@lem133533) (@lem133523)). Qed.
Lemma lem133555 : term653 = term658.
Proof. exact (TRANS (@lem133505) (@lem133534)). Qed.
Lemma lem133556 : term658 = term653.
Proof. exact (SYM (@lem133555)). Qed.
Lemma lem133557 (h1 : term647) : term647.
Proof. exact (h1). Qed.
Lemma lem133558 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem133563 (m' : nat) : (term645 m') = (term645 m').
Proof. exact (eq_refl (term645 m')). Qed.
Lemma lem133564 : term646 = term646.
Proof. exact (fun_ext (fun m' : nat => @lem133563 m')). Qed.
Lemma lem133565 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem133598 : term647 = term647.
Proof. exact (MK_COMB (@lem133565) (@lem133564)). Qed.
Lemma lem133599 (h1 : term647) : term647.
Proof. exact (EQ_MP (@lem133598) (@lem133557 h1)). Qed.
Lemma lem133606 (n : nat) : (term418 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (@lem16933 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem133609 (n : nat) : (term419 n) = (term419 n).
Proof. exact (eq_refl (term419 n)). Qed.
Lemma lem133611 (n : nat) : (term420 n) = (term420 n).
Proof. exact (eq_refl (term420 n)). Qed.
Lemma lem133612 (n : nat) : (term421 n) = (term422 n).
Proof. exact (MK_COMB (@lem133611 n) (@lem133606 n)). Qed.
Lemma lem133613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem133614 (n : nat) : (term423 n) = (term424 n).
Proof. exact (MK_COMB (@lem133613) (@lem133612 n)). Qed.
Lemma lem133615 (n : nat) : (term425 n) = (term426 n).
Proof. exact (MK_COMB (@lem133614 n) (@lem133609 n)). Qed.
Lemma lem133616 (n : nat) : ((term108 n) = (term109 n)) = (term425 n).
Proof. exact (@lem17784 (term108 n) (term109 n)). Qed.
Lemma lem133617 (n : nat) : ((term108 n) = (term109 n)) = (term426 n).
Proof. exact (TRANS (@lem133616 n) (@lem133615 n)). Qed.
Lemma lem133618 : term110 = term427.
Proof. exact (fun_ext (fun n : nat => @lem133617 n)). Qed.
Lemma lem133619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem133620 : term88 = term428.
Proof. exact (MK_COMB (@lem133619) (@lem133618)). Qed.
Lemma lem133622 : term87 = term87.
Proof. exact (eq_refl term87). Qed.
Lemma lem133623 : term89 = term429.
Proof. exact (MK_COMB (@lem133622) (@lem133620)). Qed.
Lemma lem133625 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term430 A P Q) = (term431 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem133626 (P : nat -> Prop) (Q : nat -> Prop) : (term432 P Q) = (term433 P Q).
Proof. exact (@lem133625 nat P Q). Qed.
Lemma lem133627 : term434 = term435.
Proof. exact (@lem133626 term436 term437). Qed.
Lemma lem133628 (n : nat) : (term438 n) = (term422 n).
Proof. exact (eq_refl (term438 n)). Qed.
Lemma lem133629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem133630 (n : nat) : (term439 n) = (term424 n).
Proof. exact (MK_COMB (@lem133629) (@lem133628 n)). Qed.
Lemma lem133631 (n : nat) : (term440 n) = (term419 n).
Proof. exact (eq_refl (term440 n)). Qed.
Lemma lem133632 (n : nat) : (term441 n) = (term426 n).
Proof. exact (MK_COMB (@lem133630 n) (@lem133631 n)). Qed.
Lemma lem133633 : term442 = term427.
Proof. exact (fun_ext (fun n : nat => @lem133632 n)). Qed.
Lemma lem133634 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem133635 : term434 = term428.
Proof. exact (MK_COMB (@lem133634) (@lem133633)). Qed.
Lemma lem133636 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem133637 : term443 = term444.
Proof. exact (MK_COMB (@lem133636) (@lem133635)). Qed.
Lemma lem133638 (n : nat) : (term438 n) = (term422 n).
Proof. exact (eq_refl (term438 n)). Qed.
Lemma lem133639 : term445 = term436.
Proof. exact (fun_ext (fun n : nat => @lem133638 n)). Qed.
Lemma lem133640 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem133641 : term446 = term447.
Proof. exact (MK_COMB (@lem133640) (@lem133639)). Qed.
Lemma lem133642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem133643 : term448 = term449.
Proof. exact (MK_COMB (@lem133642) (@lem133641)). Qed.
Lemma lem133644 (n : nat) : (term440 n) = (term419 n).
Proof. exact (eq_refl (term440 n)). Qed.
Lemma lem133645 : term450 = term437.
Proof. exact (fun_ext (fun n : nat => @lem133644 n)). Qed.
Lemma lem133646 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem133647 : term451 = term452.
Proof. exact (MK_COMB (@lem133646) (@lem133645)). Qed.
Lemma lem133648 : term435 = term453.
Proof. exact (MK_COMB (@lem133643) (@lem133647)). Qed.
Lemma lem133649 : (term434 = term435) = (term428 = term453).
Proof. exact (MK_COMB (@lem133637) (@lem133648)). Qed.
Lemma lem133650 : term428 = term453.
Proof. exact (EQ_MP (@lem133649) (@lem133627)). Qed.
Lemma lem133731 : term87 = term87.
Proof. exact (eq_refl term87). Qed.
Lemma lem133734 : term429 = term454.
Proof. exact (MK_COMB (@lem133731) (@lem133650)). Qed.
Lemma lem133735 : term89 = term454.
Proof. exact (TRANS (@lem133623) (@lem133734)). Qed.
Lemma lem133736 (h1 : term89) : term454.
Proof. exact (EQ_MP (@lem133735) (@lem133558 h1)). Qed.
Lemma lem133752 (n : nat) : (term419 n) = (term419 n).
Proof. exact (eq_refl (term419 n)). Qed.
Lemma lem133753 : term437 = term437.
Proof. exact (fun_ext (fun n : nat => @lem133752 n)). Qed.
Lemma lem133754 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem133755 : term452 = term452.
Proof. exact (MK_COMB (@lem133754) (@lem133753)). Qed.
Lemma lem133766 (n : nat) : (term422 n) = (term422 n).
Proof. exact (eq_refl (term422 n)). Qed.
Lemma lem133767 : term436 = term436.
Proof. exact (fun_ext (fun n : nat => @lem133766 n)). Qed.
Lemma lem133768 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem133769 : term447 = term447.
Proof. exact (MK_COMB (@lem133768) (@lem133767)). Qed.
Lemma lem133770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem133771 : term449 = term449.
Proof. exact (MK_COMB (@lem133770) (@lem133769)). Qed.
Lemma lem133772 : term453 = term453.
Proof. exact (MK_COMB (@lem133771) (@lem133755)). Qed.
Lemma lem133781 : term87 = term87.
Proof. exact (eq_refl term87). Qed.
Lemma lem133782 : term454 = term454.
Proof. exact (MK_COMB (@lem133781) (@lem133772)). Qed.
Lemma lem133783 (h1 : term89) : term454.
Proof. exact (EQ_MP (@lem133782) (@lem133736 h1)). Qed.
Lemma lem133797 (m' : nat) (h1 : term645 m') : term645 m'.
Proof. exact (h1). Qed.
Lemma lem133849 (m' : nat) (h1 : term645 m') : Coq.Arith.PeanoNat.Nat.Odd m'.
Proof. exact (proj1 (@lem133797 m' h1)). Qed.
Lemma lem133851 (m' : nat) (h1 : term645 m') : m' = (NUMERAL 0).
Proof. exact (proj2 (@lem133797 m' h1)). Qed.
Lemma lem133880 : term459 = term459.
Proof. exact (eq_refl term459). Qed.
Lemma lem133881 (m' : nat) (h1 : term645 m') : (term460 m') = term659.
Proof. exact (MK_COMB (@lem133880) (@lem133851 m' h1)). Qed.
Lemma lem133882 : term659 = term84.
Proof. exact (eq_refl term659). Qed.
Lemma lem133883 (m' : nat) : (term463 m') = (term463 m').
Proof. exact (eq_refl (term463 m')). Qed.
Lemma lem133884 (m' : nat) : ((term460 m') = term659) = ((term460 m') = term84).
Proof. exact (MK_COMB (@lem133883 m') (@lem133882)). Qed.
Lemma lem133885 (m' : nat) : (term460 m') = (Coq.Arith.PeanoNat.Nat.Odd m').
Proof. exact (eq_refl (term460 m')). Qed.
Lemma lem133886 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem133887 (m' : nat) : (term463 m') = (term464 m').
Proof. exact (MK_COMB (@lem133886) (@lem133885 m')). Qed.
Lemma lem133888 : term84 = term84.
Proof. exact (eq_refl term84). Qed.
Lemma lem133889 (m' : nat) : ((term460 m') = term84) = ((Coq.Arith.PeanoNat.Nat.Odd m') = term84).
Proof. exact (MK_COMB (@lem133887 m') (@lem133888)). Qed.
Lemma lem133890 (m' : nat) : ((term460 m') = term659) = ((Coq.Arith.PeanoNat.Nat.Odd m') = term84).
Proof. exact (TRANS (@lem133884 m') (@lem133889 m')). Qed.
Lemma lem133891 (m' : nat) (h1 : term645 m') : (Coq.Arith.PeanoNat.Nat.Odd m') = term84.
Proof. exact (EQ_MP (@lem133890 m') (@lem133881 m' h1)). Qed.
Lemma lem133906 (h1 : term89) : term85.
Proof. exact (proj1 (@lem133783 h1)). Qed.
Lemma lem133936 (m' : nat) (h1 : term645 m') : term84.
Proof. exact (EQ_MP (@lem133891 m' h1) (@lem133849 m' h1)). Qed.
Lemma lem133937 (m' : nat) (h1 : term645 m') : term503.
Proof. exact (fun h0 : term85 => @lem133936 m' h1). Qed.
Lemma lem133939 (p : Prop) : (term478 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem133940 : term503 = term84.
Proof. exact (@lem133939 term84). Qed.
Lemma lem133941 (m' : nat) (h1 : term645 m') : term84.
Proof. exact (EQ_MP (@lem133940) (@lem133937 m' h1)). Qed.
Lemma lem133944 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem133946 : term85 = term504.
Proof. exact (@lem133944 term84). Qed.
Lemma lem133949 (h1 : term89) : term504.
Proof. exact (EQ_MP (@lem133946) (@lem133906 h1)). Qed.
Lemma lem133952 (m' : nat) (h1 : term645 m') (h2 : term89) : False.
Proof. exact (@lem133949 h2 (@lem133941 m' h1)). Qed.
Lemma lem133953 (m' : nat) (h1 : term645 m') (h2 : term89) : term505.
Proof. exact (fun h0 : ~ False => @lem133952 m' h1 h2). Qed.
Lemma lem133955 (p : Prop) : (term478 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem133956 : term505 = False.
Proof. exact (@lem133955 False). Qed.
Lemma lem133958 (m' : nat) (h1 : term645 m') (h2 : term89) : False.
Proof. exact (EQ_MP (@lem133956) (@lem133953 m' h1 h2)). Qed.
Lemma lem133959 (m' : nat) (h1 : term645 m') (h2 : term89) : (term645 m') = False.
Proof. exact (prop_ext (fun h3 : term645 m' => @lem133958 m' h1 h2) (fun h3 : False => @lem133797 m' h1)). Qed.
Lemma lem133960 (m' : nat) (h1 : term645 m') (h2 : term89) : False.
Proof. exact (EQ_MP (@lem133959 m' h1 h2) (@lem133797 m' h1)). Qed.
Lemma lem133961 (h1 : term647) (h2 : term89) : False.
Proof. exact (ex_elim (@lem133599 h1) (fun m' : nat => fun h0 : term646 m' => @lem133960 m' h0 h2)). Qed.
Lemma lem133962 (h1 : term647) (h2 : term89) : term647 = False.
Proof. exact (prop_ext (fun h3 : term647 => @lem133961 h1 h2) (fun h3 : False => @lem133599 h1)). Qed.
Lemma lem133963 (h1 : term647) (h2 : term89) : False.
Proof. exact (EQ_MP (@lem133962 h1 h2) (@lem133599 h1)). Qed.
Lemma lem133964 (h1 : term647) : term567.
Proof. exact (fun h0 : term89 => @lem133963 h1 h0). Qed.
Lemma lem133965 : term567 = term90.
Proof. exact (@lem69 term89). Qed.
Lemma lem133966 (h1 : term647) : term90.
Proof. exact (EQ_MP (@lem133965) (@lem133964 h1)). Qed.
Lemma lem133967 : term658.
Proof. exact (fun h0 : term647 => @lem133966 h0). Qed.
Lemma lem133968 : term653.
Proof. exact (EQ_MP (@lem133556) (@lem133967)). Qed.
Lemma lem133970 : term653.
Proof. exact (@lem133444 (@lem133968)). Qed.
Lemma lem133971 (h1 : term647) : term81.
Proof. exact (@lem133970 (@lem133429 h1)). Qed.
Lemma lem133972 (h1 : term647) : False.
Proof. exact (@lem133971 h1 (@lem124619)). Qed.
Lemma lem133973 (h1 : term647) : term647 = False.
Proof. exact (prop_ext (fun h2 : term647 => @lem133972 h1) (fun h2 : False => @lem133429 h1)). Qed.
Lemma lem133974 (h1 : term647) : False.
Proof. exact (EQ_MP (@lem133973 h1) (@lem133429 h1)). Qed.
Lemma lem133975 : term660.
Proof. exact (fun h0 : term647 => @lem133974 h0). Qed.
Lemma lem133976 : term660 = term652.
Proof. exact (@lem69 term647). Qed.
Lemma lem133977 : term652.
Proof. exact (EQ_MP (@lem133976) (@lem133975)). Qed.
Lemma lem133978 : term635.
Proof. exact (EQ_MP (@lem133428) (@lem133977)). Qed.
Lemma lem133979 : term598.
Proof. exact (EQ_MP (@lem133342) (@lem133978)). Qed.
Lemma lem133980 : term620.
Proof. exact (EQ_MP (@lem133321) (@lem133979)). Qed.
Lemma lem133982 (p : Prop) (q : Prop) (r : Prop) : term661 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem133983 (m : nat) : term662 m.
Proof. exact (@lem133982 (term586 m) (term52 m) ((term571 m) = term625)). Qed.
Lemma lem133985 (n : nat) : n = (term16 n).
Proof. exact (EQ_MP (@lem128950 n) (@lem128949 n)). Qed.
Lemma lem133986 (m : nat) : m = (term16 m).
Proof. exact (@lem133985 m). Qed.
Lemma lem133987 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem133988 (m : nat) : (Peano.lt m) = (term663 m).
Proof. exact (MK_COMB (@lem133987) (@lem133986 m)). Qed.
Lemma lem133989 (m : nat) : (term569 m) = (term569 m).
Proof. exact (eq_refl (term569 m)). Qed.
Lemma lem133990 (m : nat) : (term586 m) = (term664 m).
Proof. exact (MK_COMB (@lem133988 m) (@lem133989 m)). Qed.
Lemma lem133991 (m : nat) : (term664 m) = (term586 m).
Proof. exact (SYM (@lem133990 m)). Qed.
Lemma lem133992 : term665.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem133993 (m : nat) : term666 m.
Proof. exact (@lem133992 m). Qed.
Lemma lem133994 (m : nat) : (term666 m) = (term667 m).
Proof. exact (eq_refl (term666 m)). Qed.
Lemma lem133995 (m : nat) : term667 m.
Proof. exact (EQ_MP (@lem133994 m) (@lem133993 m)). Qed.
Lemma lem133996 (m : nat) (n : nat) : term668 m n.
Proof. exact (@lem133995 m n). Qed.
Lemma lem133997 (m : nat) (n : nat) : (term668 m n) = ((term669 m n) = (term670 m n)).
Proof. exact (eq_refl (term668 m n)). Qed.
Lemma lem134003 (m : nat) : term671 m.
Proof. exact (@lem105963 m). Qed.
Lemma lem134004 (m : nat) : (term671 m) = (term672 m).
Proof. exact (eq_refl (term671 m)). Qed.
Lemma lem134005 (m : nat) : term672 m.
Proof. exact (EQ_MP (@lem134004 m) (@lem134003 m)). Qed.
Lemma lem134006 (m : nat) (n : nat) : term673 m n.
Proof. exact (@lem134005 m n). Qed.
Lemma lem134007 (m : nat) (n : nat) : (term673 m n) = (term674 m n).
Proof. exact (eq_refl (term673 m n)). Qed.
Lemma lem134008 (m : nat) (n : nat) : term674 m n.
Proof. exact (EQ_MP (@lem134007 m n) (@lem134006 m n)). Qed.
Lemma lem134009 (m : nat) (n : nat) (p : nat) : term675 m n p.
Proof. exact (@lem134008 m n p). Qed.
Lemma lem134010 (m : nat) (n : nat) (p : nat) : (term675 m n p) = ((term676 m n p) = (term677 m n p)).
Proof. exact (eq_refl (term675 m n p)). Qed.
Lemma lem134012 (m : nat) : term621 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem134026 (m : nat) (n : nat) (p : nat) : (term676 m n p) = (term677 m n p).
Proof. exact (EQ_MP (@lem134010 m n p) (@lem134009 m n p)). Qed.
Lemma lem134027 (m : nat) : (term664 m) = (term678 m).
Proof. exact (@lem134026 term118 term8 m). Qed.
Lemma lem134031 : term8 = term9.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem134032 : term679 = term679.
Proof. exact (eq_refl term679). Qed.
Lemma lem134033 : term680 = term681.
Proof. exact (MK_COMB (@lem134032) (@lem134031)). Qed.
Lemma lem134035 (m : nat) (n : nat) : (term669 m n) = (term670 m n).
Proof. exact (EQ_MP (@lem133997 m n) (@lem133996 m n)). Qed.
Lemma lem134036 : term681 = term682.
Proof. exact (@lem134035 term118 term118). Qed.
Lemma lem134040 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem134041 (x : nat) : (x = x) = True.
Proof. exact (@lem134040 nat x). Qed.
Lemma lem134042 : (term118 = term118) = True.
Proof. exact (@lem134041 term118). Qed.
Lemma lem134043 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem134044 : term683 = (or True).
Proof. exact (MK_COMB (@lem134043) (@lem134042)). Qed.
Lemma lem134045 : term684 = term684.
Proof. exact (eq_refl term684). Qed.
Lemma lem134046 : term682 = term685.
Proof. exact (MK_COMB (@lem134044) (@lem134045)). Qed.
Lemma lem134048 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem134049 : term685 = True.
Proof. exact (@lem134048 term684). Qed.
Lemma lem134050 : term682 = True.
Proof. exact (TRANS (@lem134046) (@lem134049)). Qed.
Lemma lem134051 : term681 = True.
Proof. exact (TRANS (@lem134036) (@lem134050)). Qed.
Lemma lem134052 : term680 = True.
Proof. exact (TRANS (@lem134033) (@lem134051)). Qed.
Lemma lem134053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem134054 : term686 = (and True).
Proof. exact (MK_COMB (@lem134053) (@lem134052)). Qed.
Lemma lem134056 (m : nat) (h1 : term37 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem134012 m (@lem129039 m h1)). Qed.
Lemma lem134057 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem134058 (m : nat) (h1 : term37 m) : (term37 m) = (~ False).
Proof. exact (MK_COMB (@lem134057) (@lem134056 m h1)). Qed.
Lemma lem134060 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem134061 (m : nat) (h1 : term37 m) : (term37 m) = True.
Proof. exact (TRANS (@lem134058 m h1) (@lem134060)). Qed.
Lemma lem134062 (m : nat) (h1 : term37 m) : (term678 m) = (True /\ True).
Proof. exact (MK_COMB (@lem134054) (@lem134061 m h1)). Qed.
Lemma lem134064 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem134065 : (True /\ True) = True.
Proof. exact (@lem134064 True). Qed.
Lemma lem134066 (m : nat) (h1 : term37 m) : (term678 m) = True.
Proof. exact (TRANS (@lem134062 m h1) (@lem134065)). Qed.
Lemma lem134067 (m : nat) (h1 : term37 m) : (term664 m) = True.
Proof. exact (TRANS (@lem134027 m) (@lem134066 m h1)). Qed.
Lemma lem134068 (m : nat) (h1 : term37 m) : True = (term664 m).
Proof. exact (SYM (@lem134067 m h1)). Qed.
Lemma lem134069 (m : nat) (h1 : term37 m) : term664 m.
Proof. exact (EQ_MP (@lem134068 m h1) (@lem0)). Qed.
Lemma lem134070 (m : nat) (h1 : term37 m) : term586 m.
Proof. exact (EQ_MP (@lem133991 m) (@lem134069 m h1)). Qed.
Lemma lem134086 : term8 = term9.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem134087 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem134088 : term687 = term688.
Proof. exact (MK_COMB (@lem134087) (@lem134086)). Qed.
Lemma lem134089 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem134090 (k : nat) : (term637 k) = (term689 k).
Proof. exact (MK_COMB (@lem134088) (@lem134089 k)). Qed.
Lemma lem134091 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem134092 (k : nat) : (term690 k) = (term691 k).
Proof. exact (MK_COMB (@lem134091) (@lem134090 k)). Qed.
Lemma lem134093 (m'' : nat) : m'' = m''.
Proof. exact (eq_refl m''). Qed.
Lemma lem134094 (k : nat) (m'' : nat) : (term157 k m'') = (term692 k m'').
Proof. exact (MK_COMB (@lem134092 k) (@lem134093 m'')). Qed.
Lemma lem134095 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem134096 (m : nat) (k : nat) (m'' : nat) : (m = (term157 k m'')) = (m = (term692 k m'')).
Proof. exact (MK_COMB (@lem134095 m) (@lem134094 k m'')). Qed.
Lemma lem134099 (m'' : nat) : (term591 m'') = (term591 m'').
Proof. exact (eq_refl (term591 m'')). Qed.
Lemma lem134100 (m : nat) (k : nat) (m'' : nat) : (term150 m k m'') = (term693 m k m'').
Proof. exact (MK_COMB (@lem134099 m'') (@lem134096 m k m'')). Qed.
Lemma lem134103 (m : nat) (k : nat) : (term151 m k) = (term694 m k).
Proof. exact (fun_ext (fun m'' : nat => @lem134100 m k m'')). Qed.
Lemma lem134104 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134105 (m : nat) (k : nat) : (term152 m k) = (term695 m k).
Proof. exact (MK_COMB (@lem134104) (@lem134103 m k)). Qed.
Lemma lem134110 (m : nat) : (term153 m) = (term696 m).
Proof. exact (fun_ext (fun k : nat => @lem134105 m k)). Qed.
Lemma lem134111 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134112 (m : nat) : (term52 m) = (term697 m).
Proof. exact (MK_COMB (@lem134111) (@lem134110 m)). Qed.
Lemma lem134117 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem134118 (m : nat) : (term698 m) = (term699 m).
Proof. exact (MK_COMB (@lem134117) (@lem134112 m)). Qed.
Lemma lem134134 : term8 = term9.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem134135 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem134136 : term584 = term700.
Proof. exact (MK_COMB (@lem134135) (@lem134134)). Qed.
Lemma lem134137 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem134138 (m : nat) : (term569 m) = (term701 m).
Proof. exact (MK_COMB (@lem134136) (@lem134137 m)). Qed.
Lemma lem134139 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem134140 (m : nat) : (term602 m) = (term702 m).
Proof. exact (MK_COMB (@lem134139) (@lem134138 m)). Qed.
Lemma lem134142 : term8 = term9.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem134143 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem134144 : term687 = term688.
Proof. exact (MK_COMB (@lem134143) (@lem134142)). Qed.
Lemma lem134145 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem134146 (k : nat) : (term637 k) = (term689 k).
Proof. exact (MK_COMB (@lem134144) (@lem134145 k)). Qed.
Lemma lem134147 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem134148 (k : nat) : (term690 k) = (term691 k).
Proof. exact (MK_COMB (@lem134147) (@lem134146 k)). Qed.
Lemma lem134149 (m' : nat) : m' = m'.
Proof. exact (eq_refl m'). Qed.
Lemma lem134150 (k : nat) (m' : nat) : (term157 k m') = (term692 k m').
Proof. exact (MK_COMB (@lem134148 k) (@lem134149 m')). Qed.
Lemma lem134151 (m : nat) (k : nat) (m' : nat) : ((term569 m) = (term157 k m')) = ((term701 m) = (term692 k m')).
Proof. exact (MK_COMB (@lem134140 m) (@lem134150 k m')). Qed.
Lemma lem134154 (m' : nat) : (term591 m') = (term591 m').
Proof. exact (eq_refl (term591 m')). Qed.
Lemma lem134155 (m : nat) (k : nat) (m' : nat) : (term604 m k m') = (term703 m k m').
Proof. exact (MK_COMB (@lem134154 m') (@lem134151 m k m')). Qed.
Lemma lem134158 (m : nat) (k : nat) : (term606 m k) = (term704 m k).
Proof. exact (fun_ext (fun m' : nat => @lem134155 m k m')). Qed.
Lemma lem134159 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134160 (m : nat) (k : nat) : (term608 m k) = (term705 m k).
Proof. exact (MK_COMB (@lem134159) (@lem134158 m k)). Qed.
Lemma lem134165 (m : nat) : (term610 m) = (term706 m).
Proof. exact (fun_ext (fun k : nat => @lem134160 m k)). Qed.
Lemma lem134166 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134167 (m : nat) : (term571 m) = (term707 m).
Proof. exact (MK_COMB (@lem134166) (@lem134165 m)). Qed.
Lemma lem134172 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem134173 (m : nat) : (term613 m) = (term708 m).
Proof. exact (MK_COMB (@lem134172) (@lem134167 m)). Qed.
Lemma lem134177 : term8 = term9.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem134178 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem134179 : term639 = term640.
Proof. exact (MK_COMB (@lem134178) (@lem134177)). Qed.
Lemma lem134180 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem134181 : (term8 = (NUMERAL 0)) = (term9 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem134179) (@lem134180)). Qed.
Lemma lem134183 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem128916 n (@lem128915 n)). Qed.
Lemma lem134184 : (term9 = (NUMERAL 0)) = False.
Proof. exact (@lem134183 term118). Qed.
Lemma lem134185 : (term8 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem134181) (@lem134184)). Qed.
Lemma lem134186 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem134187 : term625 = (~ False).
Proof. exact (MK_COMB (@lem134186) (@lem134185)). Qed.
Lemma lem134189 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem134190 : term625 = True.
Proof. exact (TRANS (@lem134187) (@lem134189)). Qed.
Lemma lem134191 (m : nat) : ((term571 m) = term625) = ((term707 m) = True).
Proof. exact (MK_COMB (@lem134173 m) (@lem134190)). Qed.
Lemma lem134193 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem134194 (m : nat) : ((term707 m) = True) = (term707 m).
Proof. exact (@lem134193 (term707 m)). Qed.
Lemma lem134207 (m : nat) : ((term571 m) = term625) = (term707 m).
Proof. exact (TRANS (@lem134191 m) (@lem134194 m)). Qed.
Lemma lem134208 (m : nat) : (term709 m) = (term710 m).
Proof. exact (MK_COMB (@lem134118 m) (@lem134207 m)). Qed.
Lemma lem134211 (m : nat) : (term710 m) = (term709 m).
Proof. exact (SYM (@lem134208 m)). Qed.
Lemma lem134227 : term9 = term8.
Proof. exact (EQ_MP (@lem128911) (@lem80551)). Qed.
Lemma lem134228 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem134229 : term688 = term687.
Proof. exact (MK_COMB (@lem134228) (@lem134227)). Qed.
Lemma lem134230 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem134231 (k : nat) : (term689 k) = (term637 k).
Proof. exact (MK_COMB (@lem134229) (@lem134230 k)). Qed.
Lemma lem134232 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem134233 (k : nat) : (term691 k) = (term690 k).
Proof. exact (MK_COMB (@lem134232) (@lem134231 k)). Qed.
Lemma lem134234 (m'' : nat) : m'' = m''.
Proof. exact (eq_refl m''). Qed.
Lemma lem134235 (k : nat) (m'' : nat) : (term692 k m'') = (term157 k m'').
Proof. exact (MK_COMB (@lem134233 k) (@lem134234 m'')). Qed.
Lemma lem134236 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem134237 (m : nat) (k : nat) (m'' : nat) : (m = (term692 k m'')) = (m = (term157 k m'')).
Proof. exact (MK_COMB (@lem134236 m) (@lem134235 k m'')). Qed.
Lemma lem134240 (m'' : nat) : (term591 m'') = (term591 m'').
Proof. exact (eq_refl (term591 m'')). Qed.
Lemma lem134241 (m : nat) (k : nat) (m'' : nat) : (term693 m k m'') = (term150 m k m'').
Proof. exact (MK_COMB (@lem134240 m'') (@lem134237 m k m'')). Qed.
Lemma lem134244 (m : nat) (k : nat) : (term694 m k) = (term151 m k).
Proof. exact (fun_ext (fun m'' : nat => @lem134241 m k m'')). Qed.
Lemma lem134245 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134246 (m : nat) (k : nat) : (term695 m k) = (term152 m k).
Proof. exact (MK_COMB (@lem134245) (@lem134244 m k)). Qed.
Lemma lem134251 (m : nat) : (term696 m) = (term153 m).
Proof. exact (fun_ext (fun k : nat => @lem134246 m k)). Qed.
Lemma lem134252 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134253 (m : nat) : (term697 m) = (term52 m).
Proof. exact (MK_COMB (@lem134252) (@lem134251 m)). Qed.
Lemma lem134258 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem134259 (m : nat) : (term699 m) = (term698 m).
Proof. exact (MK_COMB (@lem134258) (@lem134253 m)). Qed.
Lemma lem134273 : term9 = term8.
Proof. exact (EQ_MP (@lem128911) (@lem80551)). Qed.
Lemma lem134274 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem134275 : term700 = term584.
Proof. exact (MK_COMB (@lem134274) (@lem134273)). Qed.
Lemma lem134276 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem134277 (m : nat) : (term701 m) = (term569 m).
Proof. exact (MK_COMB (@lem134275) (@lem134276 m)). Qed.
Lemma lem134278 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem134279 (m : nat) : (term702 m) = (term602 m).
Proof. exact (MK_COMB (@lem134278) (@lem134277 m)). Qed.
Lemma lem134281 : term9 = term8.
Proof. exact (EQ_MP (@lem128911) (@lem80551)). Qed.
Lemma lem134282 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem134283 : term688 = term687.
Proof. exact (MK_COMB (@lem134282) (@lem134281)). Qed.
Lemma lem134284 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem134285 (k : nat) : (term689 k) = (term637 k).
Proof. exact (MK_COMB (@lem134283) (@lem134284 k)). Qed.
Lemma lem134286 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem134287 (k : nat) : (term691 k) = (term690 k).
Proof. exact (MK_COMB (@lem134286) (@lem134285 k)). Qed.
Lemma lem134288 (m' : nat) : m' = m'.
Proof. exact (eq_refl m'). Qed.
Lemma lem134289 (k : nat) (m' : nat) : (term692 k m') = (term157 k m').
Proof. exact (MK_COMB (@lem134287 k) (@lem134288 m')). Qed.
Lemma lem134290 (m : nat) (k : nat) (m' : nat) : ((term701 m) = (term692 k m')) = ((term569 m) = (term157 k m')).
Proof. exact (MK_COMB (@lem134279 m) (@lem134289 k m')). Qed.
Lemma lem134293 (m' : nat) : (term591 m') = (term591 m').
Proof. exact (eq_refl (term591 m')). Qed.
Lemma lem134294 (m : nat) (k : nat) (m' : nat) : (term703 m k m') = (term604 m k m').
Proof. exact (MK_COMB (@lem134293 m') (@lem134290 m k m')). Qed.
Lemma lem134297 (m : nat) (k : nat) : (term704 m k) = (term606 m k).
Proof. exact (fun_ext (fun m' : nat => @lem134294 m k m')). Qed.
Lemma lem134298 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134299 (m : nat) (k : nat) : (term705 m k) = (term608 m k).
Proof. exact (MK_COMB (@lem134298) (@lem134297 m k)). Qed.
Lemma lem134304 (m : nat) : (term706 m) = (term610 m).
Proof. exact (fun_ext (fun k : nat => @lem134299 m k)). Qed.
Lemma lem134305 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134306 (m : nat) : (term707 m) = (term571 m).
Proof. exact (MK_COMB (@lem134305) (@lem134304 m)). Qed.
Lemma lem134311 (m : nat) : (term710 m) = (term711 m).
Proof. exact (MK_COMB (@lem134259 m) (@lem134306 m)). Qed.
Lemma lem134314 (m : nat) : (term711 m) = (term710 m).
Proof. exact (SYM (@lem134311 m)). Qed.
Lemma lem134318 {A B : Type'} (P : type1413 A B) : (term6 A B P) = (term7 A B P).
Proof. exact (EQ_MP (@lem128905 A B P) (@lem128904 A B P)). Qed.
Lemma lem134319 (P : type1605) : (term712 P) = (term713 P).
Proof. exact (@lem134318 nat nat P). Qed.
Lemma lem134320 (m : nat) : (term714 m) = (term715 m).
Proof. exact (@lem134319 (term716 m)). Qed.
Lemma lem134321 (m : nat) (k : nat) : (term717 m k) = (term151 m k).
Proof. exact (eq_refl (term717 m k)). Qed.
Lemma lem134322 (m'' : nat) : m'' = m''.
Proof. exact (eq_refl m''). Qed.
Lemma lem134323 (m : nat) (k : nat) (m'' : nat) : (term718 m k m'') = (term162 m k m'').
Proof. exact (MK_COMB (@lem134321 m k) (@lem134322 m'')). Qed.
Lemma lem134324 (m : nat) (k : nat) (m'' : nat) : (term162 m k m'') = (term150 m k m'').
Proof. exact (eq_refl (term162 m k m'')). Qed.
Lemma lem134325 (m : nat) (k : nat) (m'' : nat) : (term718 m k m'') = (term150 m k m'').
Proof. exact (TRANS (@lem134323 m k m'') (@lem134324 m k m'')). Qed.
Lemma lem134326 (m : nat) (k : nat) : (term719 m k) = (term151 m k).
Proof. exact (fun_ext (fun m'' : nat => @lem134325 m k m'')). Qed.
Lemma lem134327 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134328 (m : nat) (k : nat) : (term720 m k) = (term152 m k).
Proof. exact (MK_COMB (@lem134327) (@lem134326 m k)). Qed.
Lemma lem134329 (m : nat) : (term721 m) = (term153 m).
Proof. exact (fun_ext (fun k : nat => @lem134328 m k)). Qed.
Lemma lem134330 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134331 (m : nat) : (term714 m) = (term52 m).
Proof. exact (MK_COMB (@lem134330) (@lem134329 m)). Qed.
Lemma lem134332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem134333 (m : nat) : (term722 m) = (term154 m).
Proof. exact (MK_COMB (@lem134332) (@lem134331 m)). Qed.
Lemma lem134334 (m : nat) (k : nat) : (term717 m k) = (term151 m k).
Proof. exact (eq_refl (term717 m k)). Qed.
Lemma lem134335 (m'' : nat) : m'' = m''.
Proof. exact (eq_refl m''). Qed.
Lemma lem134336 (m : nat) (k : nat) (m'' : nat) : (term718 m k m'') = (term162 m k m'').
Proof. exact (MK_COMB (@lem134334 m k) (@lem134335 m'')). Qed.
Lemma lem134337 (m : nat) (k : nat) (m'' : nat) : (term162 m k m'') = (term150 m k m'').
Proof. exact (eq_refl (term162 m k m'')). Qed.
Lemma lem134338 (m : nat) (k : nat) (m'' : nat) : (term718 m k m'') = (term150 m k m'').
Proof. exact (TRANS (@lem134336 m k m'') (@lem134337 m k m'')). Qed.
Lemma lem134339 (m : nat) (m'' : nat) : (term723 m m'') = (term724 m m'').
Proof. exact (fun_ext (fun k : nat => @lem134338 m k m'')). Qed.
Lemma lem134340 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134341 (m : nat) (m'' : nat) : (term725 m m'') = (term726 m m'').
Proof. exact (MK_COMB (@lem134340) (@lem134339 m m'')). Qed.
Lemma lem134342 (m : nat) : (term727 m) = (term728 m).
Proof. exact (fun_ext (fun m'' : nat => @lem134341 m m'')). Qed.
Lemma lem134343 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134344 (m : nat) : (term715 m) = (term729 m).
Proof. exact (MK_COMB (@lem134343) (@lem134342 m)). Qed.
Lemma lem134345 (m : nat) : ((term714 m) = (term715 m)) = ((term52 m) = (term729 m)).
Proof. exact (MK_COMB (@lem134333 m) (@lem134344 m)). Qed.
Lemma lem134346 (m : nat) : (term52 m) = (term729 m).
Proof. exact (EQ_MP (@lem134345 m) (@lem134320 m)). Qed.
Lemma lem134347 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem134348 (m : nat) : (term698 m) = (term730 m).
Proof. exact (MK_COMB (@lem134347) (@lem134346 m)). Qed.
Lemma lem134350 {A B : Type'} (P : type1413 A B) : (term6 A B P) = (term7 A B P).
Proof. exact (EQ_MP (@lem128905 A B P) (@lem128904 A B P)). Qed.
Lemma lem134351 (P : type1605) : (term712 P) = (term713 P).
Proof. exact (@lem134350 nat nat P). Qed.
Lemma lem134352 (m : nat) : (term731 m) = (term732 m).
Proof. exact (@lem134351 (term733 m)). Qed.
Lemma lem134353 (m : nat) (k : nat) : (term734 m k) = (term606 m k).
Proof. exact (eq_refl (term734 m k)). Qed.
Lemma lem134354 (m' : nat) : m' = m'.
Proof. exact (eq_refl m'). Qed.
Lemma lem134355 (m : nat) (k : nat) (m' : nat) : (term735 m k m') = (term736 m k m').
Proof. exact (MK_COMB (@lem134353 m k) (@lem134354 m')). Qed.
Lemma lem134356 (m : nat) (k : nat) (m' : nat) : (term736 m k m') = (term604 m k m').
Proof. exact (eq_refl (term736 m k m')). Qed.
Lemma lem134357 (m : nat) (k : nat) (m' : nat) : (term735 m k m') = (term604 m k m').
Proof. exact (TRANS (@lem134355 m k m') (@lem134356 m k m')). Qed.
Lemma lem134358 (m : nat) (k : nat) : (term737 m k) = (term606 m k).
Proof. exact (fun_ext (fun m' : nat => @lem134357 m k m')). Qed.
Lemma lem134359 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134360 (m : nat) (k : nat) : (term738 m k) = (term608 m k).
Proof. exact (MK_COMB (@lem134359) (@lem134358 m k)). Qed.
Lemma lem134361 (m : nat) : (term739 m) = (term610 m).
Proof. exact (fun_ext (fun k : nat => @lem134360 m k)). Qed.
Lemma lem134362 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134363 (m : nat) : (term731 m) = (term571 m).
Proof. exact (MK_COMB (@lem134362) (@lem134361 m)). Qed.
Lemma lem134364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem134365 (m : nat) : (term740 m) = (term613 m).
Proof. exact (MK_COMB (@lem134364) (@lem134363 m)). Qed.
Lemma lem134366 (m : nat) (k : nat) : (term734 m k) = (term606 m k).
Proof. exact (eq_refl (term734 m k)). Qed.
Lemma lem134367 (m' : nat) : m' = m'.
Proof. exact (eq_refl m'). Qed.
Lemma lem134368 (m : nat) (k : nat) (m' : nat) : (term735 m k m') = (term736 m k m').
Proof. exact (MK_COMB (@lem134366 m k) (@lem134367 m')). Qed.
Lemma lem134369 (m : nat) (k : nat) (m' : nat) : (term736 m k m') = (term604 m k m').
Proof. exact (eq_refl (term736 m k m')). Qed.
Lemma lem134370 (m : nat) (k : nat) (m' : nat) : (term735 m k m') = (term604 m k m').
Proof. exact (TRANS (@lem134368 m k m') (@lem134369 m k m')). Qed.
Lemma lem134371 (m : nat) (m' : nat) : (term741 m m') = (term742 m m').
Proof. exact (fun_ext (fun k : nat => @lem134370 m k m')). Qed.
Lemma lem134372 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134373 (m : nat) (m' : nat) : (term743 m m') = (term744 m m').
Proof. exact (MK_COMB (@lem134372) (@lem134371 m m')). Qed.
Lemma lem134374 (m : nat) : (term745 m) = (term746 m).
Proof. exact (fun_ext (fun m' : nat => @lem134373 m m')). Qed.
Lemma lem134375 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134376 (m : nat) : (term732 m) = (term747 m).
Proof. exact (MK_COMB (@lem134375) (@lem134374 m)). Qed.
Lemma lem134377 (m : nat) : ((term731 m) = (term732 m)) = ((term571 m) = (term747 m)).
Proof. exact (MK_COMB (@lem134365 m) (@lem134376 m)). Qed.
Lemma lem134378 (m : nat) : (term571 m) = (term747 m).
Proof. exact (EQ_MP (@lem134377 m) (@lem134352 m)). Qed.
Lemma lem134379 (m : nat) : (term711 m) = (term748 m).
Proof. exact (MK_COMB (@lem134348 m) (@lem134378 m)). Qed.
Lemma lem134380 (m : nat) : (term748 m) = (term711 m).
Proof. exact (SYM (@lem134379 m)). Qed.
Lemma lem134382 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term0 A P Q.
Proof. exact (@lem128902 A P Q (@lem7401 A P Q)). Qed.
Lemma lem134383 (P : nat -> Prop) (Q : nat -> Prop) : term749 P Q.
Proof. exact (@lem134382 nat P Q). Qed.
Lemma lem134384 (m : nat) : term750 m.
Proof. exact (@lem134383 (term728 m) (term746 m)). Qed.
Lemma lem134385 (m : nat) (m'' : nat) : (term751 m m'') = (term726 m m'').
Proof. exact (eq_refl (term751 m m'')). Qed.
Lemma lem134386 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem134387 (m : nat) (m'' : nat) : (term752 m m'') = (term753 m m'').
Proof. exact (MK_COMB (@lem134386) (@lem134385 m m'')). Qed.
Lemma lem134388 (m : nat) (m'' : nat) : (term754 m m'') = (term744 m m'').
Proof. exact (eq_refl (term754 m m'')). Qed.
Lemma lem134389 (m : nat) (m'' : nat) : (term755 m m'') = (term756 m m'').
Proof. exact (MK_COMB (@lem134387 m m'') (@lem134388 m m'')). Qed.
Lemma lem134390 (m : nat) : (term757 m) = (term758 m).
Proof. exact (fun_ext (fun m'' : nat => @lem134389 m m'')). Qed.
Lemma lem134391 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem134392 (m : nat) : (term759 m) = (term760 m).
Proof. exact (MK_COMB (@lem134391) (@lem134390 m)). Qed.
Lemma lem134393 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem134394 (m : nat) : (term761 m) = (term762 m).
Proof. exact (MK_COMB (@lem134393) (@lem134392 m)). Qed.
Lemma lem134395 (m : nat) (m'' : nat) : (term751 m m'') = (term726 m m'').
Proof. exact (eq_refl (term751 m m'')). Qed.
Lemma lem134396 (m : nat) : (term763 m) = (term728 m).
Proof. exact (fun_ext (fun m'' : nat => @lem134395 m m'')). Qed.
Lemma lem134397 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134398 (m : nat) : (term764 m) = (term729 m).
Proof. exact (MK_COMB (@lem134397) (@lem134396 m)). Qed.
Lemma lem134399 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem134400 (m : nat) : (term765 m) = (term730 m).
Proof. exact (MK_COMB (@lem134399) (@lem134398 m)). Qed.
Lemma lem134401 (m : nat) (m'' : nat) : (term754 m m'') = (term744 m m'').
Proof. exact (eq_refl (term754 m m'')). Qed.
Lemma lem134402 (m : nat) : (term766 m) = (term746 m).
Proof. exact (fun_ext (fun m'' : nat => @lem134401 m m'')). Qed.
Lemma lem134403 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem134404 (m : nat) : (term767 m) = (term747 m).
Proof. exact (MK_COMB (@lem134403) (@lem134402 m)). Qed.
Lemma lem134405 (m : nat) : (term768 m) = (term748 m).
Proof. exact (MK_COMB (@lem134400 m) (@lem134404 m)). Qed.
Lemma lem134406 (m : nat) : (term750 m) = (term769 m).
Proof. exact (MK_COMB (@lem134394 m) (@lem134405 m)). Qed.
Lemma lem134407 (m : nat) : term769 m.
Proof. exact (EQ_MP (@lem134406 m) (@lem134384 m)). Qed.
Lemma lem134410 (m : nat) : (term770 m) = (term770 m).
Proof. exact (eq_refl (term770 m)). Qed.
Lemma lem134411 (m : nat) : (term770 m) = (term769 m).
Proof. exact (eq_refl (term770 m)). Qed.
Lemma lem134412 (m : nat) : (term771 m) = (term771 m).
Proof. exact (eq_refl (term771 m)). Qed.
Lemma lem134413 (m : nat) : ((term770 m) = (term770 m)) = ((term770 m) = (term769 m)).
Proof. exact (MK_COMB (@lem134412 m) (@lem134411 m)). Qed.
Lemma lem134414 (m : nat) : (term770 m) = (term769 m).
Proof. exact (eq_refl (term770 m)). Qed.
Lemma lem134415 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem134416 (m : nat) : (term771 m) = (term772 m).
Proof. exact (MK_COMB (@lem134415) (@lem134414 m)). Qed.
Lemma lem134417 (m : nat) : (term769 m) = (term769 m).
Proof. exact (eq_refl (term769 m)). Qed.
Lemma lem134418 (m : nat) : ((term770 m) = (term769 m)) = ((term769 m) = (term769 m)).
Proof. exact (MK_COMB (@lem134416 m) (@lem134417 m)). Qed.
Lemma lem134419 (m : nat) : ((term770 m) = (term770 m)) = ((term769 m) = (term769 m)).
Proof. exact (TRANS (@lem134413 m) (@lem134418 m)). Qed.
Lemma lem134420 (m : nat) : (term769 m) = (term769 m).
Proof. exact (EQ_MP (@lem134419 m) (@lem134410 m)). Qed.
Lemma lem134421 (m : nat) : term769 m.
Proof. exact (EQ_MP (@lem134420 m) (@lem134407 m)). Qed.
Lemma lem134422 (m : nat) (p : nat) (h1 : term726 m p) : term726 m p.
Proof. exact (h1). Qed.
Lemma lem134423 (m : nat) (k : nat) (p : nat) (h1 : term150 m k p) : term150 m k p.
Proof. exact (h1). Qed.
Lemma lem134424 (m : nat) (k : nat) (p : nat) (h1 : m = (term157 k p)) : m = (term157 k p).
Proof. exact (h1). Qed.
Lemma lem134425 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) : Coq.Arith.PeanoNat.Nat.Odd p.
Proof. exact (h1). Qed.
Lemma lem134426 (m : nat) : term773 m.
Proof. exact (@lem82357 m). Qed.
Lemma lem134427 (m : nat) : (term773 m) = (term774 m).
Proof. exact (eq_refl (term773 m)). Qed.
Lemma lem134428 (m : nat) : term774 m.
Proof. exact (EQ_MP (@lem134427 m) (@lem134426 m)). Qed.
Lemma lem134429 (m : nat) (n : nat) : term775 m n.
Proof. exact (@lem134428 m n). Qed.
Lemma lem134430 (m : nat) (n : nat) : (term775 m n) = (term776 m n).
Proof. exact (eq_refl (term775 m n)). Qed.
Lemma lem134431 (m : nat) (n : nat) : term776 m n.
Proof. exact (EQ_MP (@lem134430 m n) (@lem134429 m n)). Qed.
Lemma lem134432 (m : nat) (n : nat) (p : nat) : term777 m n p.
Proof. exact (@lem134431 m n p). Qed.
Lemma lem134433 (m : nat) (n : nat) (p : nat) : (term777 m n p) = ((term778 m n p) = (term779 m n p)).
Proof. exact (eq_refl (term777 m n p)). Qed.
Lemma lem134435 : term116.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem134436 (m : nat) : term780 m.
Proof. exact (@lem134435 m). Qed.
Lemma lem134437 (m : nat) : (term780 m) = (term114 m).
Proof. exact (eq_refl (term780 m)). Qed.
Lemma lem134438 (m : nat) : term114 m.
Proof. exact (EQ_MP (@lem134437 m) (@lem134436 m)). Qed.
Lemma lem134439 (m : nat) (n : nat) : term781 m n.
Proof. exact (@lem134438 m n). Qed.
Lemma lem134440 (m : nat) (n : nat) : (term781 m n) = ((term111 m n) = (term112 m n)).
Proof. exact (eq_refl (term781 m n)). Qed.
Lemma lem134459 (p : nat) : (Coq.Arith.PeanoNat.Nat.Odd p) = ((Coq.Arith.PeanoNat.Nat.Odd p) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Odd p)). Qed.
Lemma lem134464 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) : (Coq.Arith.PeanoNat.Nat.Odd p) = True.
Proof. exact (EQ_MP (@lem134459 p) (@lem134425 p h1)). Qed.
Lemma lem134465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem134466 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) : (term591 p) = (and True).
Proof. exact (MK_COMB (@lem134465) (@lem134464 p h1)). Qed.
Lemma lem134470 (m : nat) (k : nat) (p : nat) (h1 : m = (term157 k p)) : m = (term157 k p).
Proof. exact (h1). Qed.
Lemma lem134471 : term584 = term584.
Proof. exact (eq_refl term584). Qed.
Lemma lem134472 (m : nat) (k : nat) (p : nat) (h1 : m = (term157 k p)) : (term569 m) = (term782 k p).
Proof. exact (MK_COMB (@lem134471) (@lem134470 m k p h1)). Qed.
Lemma lem134474 (m : nat) (n : nat) (p : nat) : (term778 m n p) = (term779 m n p).
Proof. exact (EQ_MP (@lem134433 m n p) (@lem134432 m n p)). Qed.
Lemma lem134475 (k : nat) (p : nat) : (term782 k p) = (term783 k p).
Proof. exact (@lem134474 term8 (term637 k) p). Qed.
Lemma lem134476 (m : nat) (k : nat) (p : nat) (h1 : m = (term157 k p)) : (term569 m) = (term783 k p).
Proof. exact (TRANS (@lem134472 m k p h1) (@lem134475 k p)). Qed.
Lemma lem134477 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem134478 (m : nat) (k : nat) (p : nat) (h1 : m = (term157 k p)) : (term602 m) = (term784 k p).
Proof. exact (MK_COMB (@lem134477) (@lem134476 m k p h1)). Qed.
Lemma lem134480 (m : nat) (n : nat) : (term111 m n) = (term112 m n).
Proof. exact (EQ_MP (@lem134440 m n) (@lem134439 m n)). Qed.
Lemma lem134481 (k : nat) : (term785 k) = (term786 k).
Proof. exact (@lem134480 term8 k). Qed.
Lemma lem134482 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem134483 (k : nat) : (term787 k) = (term788 k).
Proof. exact (MK_COMB (@lem134482) (@lem134481 k)). Qed.
Lemma lem134484 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem134485 (k : nat) (p : nat) : (term789 k p) = (term783 k p).
Proof. exact (MK_COMB (@lem134483 k) (@lem134484 p)). Qed.
Lemma lem134486 (m : nat) (k : nat) (p : nat) (h1 : m = (term157 k p)) : ((term569 m) = (term789 k p)) = ((term783 k p) = (term783 k p)).
Proof. exact (MK_COMB (@lem134478 m k p h1) (@lem134485 k p)). Qed.
Lemma lem134488 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem134489 (x : nat) : (x = x) = True.
Proof. exact (@lem134488 nat x). Qed.
Lemma lem134490 (k : nat) (p : nat) : ((term783 k p) = (term783 k p)) = True.
Proof. exact (@lem134489 (term783 k p)). Qed.
Lemma lem134491 (m : nat) (k : nat) (p : nat) (h1 : m = (term157 k p)) : ((term569 m) = (term789 k p)) = True.
Proof. exact (TRANS (@lem134486 m k p h1) (@lem134490 k p)). Qed.
Lemma lem134492 (m : nat) (k : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) (h2 : m = (term157 k p)) : (term790 m k p) = (True /\ True).
Proof. exact (MK_COMB (@lem134466 p h1) (@lem134491 m k p h2)). Qed.
Lemma lem134494 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem134495 : (True /\ True) = True.
Proof. exact (@lem134494 True). Qed.
Lemma lem134496 (m : nat) (k : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) (h2 : m = (term157 k p)) : (term790 m k p) = True.
Proof. exact (TRANS (@lem134492 m k p h1 h2) (@lem134495)). Qed.
Lemma lem134497 (m : nat) (k : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) (h2 : m = (term157 k p)) : True = (term790 m k p).
Proof. exact (SYM (@lem134496 m k p h1 h2)). Qed.
Lemma lem134498 (m : nat) (k : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) (h2 : m = (term157 k p)) : term790 m k p.
Proof. exact (EQ_MP (@lem134497 m k p h1 h2) (@lem0)). Qed.
Lemma lem134499 (m : nat) (k : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) (h2 : m = (term157 k p)) : term744 m p.
Proof. exact (ex_intro (term742 m p) (S k) (@lem134498 m k p h1 h2)). Qed.
Lemma lem134500 (m : nat) (k : nat) (p : nat) (h1 : term150 m k p) : m = (term157 k p).
Proof. exact (proj2 (@lem134423 m k p h1)). Qed.
Lemma lem134501 (m : nat) (k : nat) (p : nat) (h1 : term150 m k p) : Coq.Arith.PeanoNat.Nat.Odd p.
Proof. exact (proj1 (@lem134423 m k p h1)). Qed.
Lemma lem134502 (m : nat) (k : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) (h2 : m = (term157 k p)) : (m = (term157 k p)) = (term744 m p).
Proof. exact (prop_ext (fun h3 : m = (term157 k p) => @lem134499 m k p h1 h2) (fun h3 : term744 m p => @lem134424 m k p h2)). Qed.
Lemma lem134503 (m : nat) (k : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) (h2 : m = (term157 k p)) : term744 m p.
Proof. exact (EQ_MP (@lem134502 m k p h1 h2) (@lem134424 m k p h2)). Qed.
Lemma lem134504 (m : nat) (k : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) (h2 : m = (term157 k p)) : (Coq.Arith.PeanoNat.Nat.Odd p) = (term744 m p).
Proof. exact (prop_ext (fun h3 : Coq.Arith.PeanoNat.Nat.Odd p => @lem134503 m k p h1 h2) (fun h3 : term744 m p => @lem134425 p h1)). Qed.
Lemma lem134505 (m : nat) (k : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) (h2 : m = (term157 k p)) : term744 m p.
Proof. exact (EQ_MP (@lem134504 m k p h1 h2) (@lem134425 p h1)). Qed.
Lemma lem134506 (m : nat) (k : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) (h2 : term150 m k p) : (m = (term157 k p)) = (term744 m p).
Proof. exact (prop_ext (fun h3 : m = (term157 k p) => @lem134505 m k p h1 h3) (fun h3 : term744 m p => @lem134500 m k p h2)). Qed.
Lemma lem134507 (m : nat) (k : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) (h2 : term150 m k p) : term744 m p.
Proof. exact (EQ_MP (@lem134506 m k p h1 h2) (@lem134500 m k p h2)). Qed.
Lemma lem134508 (m : nat) (k : nat) (p : nat) (h1 : term150 m k p) : (Coq.Arith.PeanoNat.Nat.Odd p) = (term744 m p).
Proof. exact (prop_ext (fun h2 : Coq.Arith.PeanoNat.Nat.Odd p => @lem134507 m k p h2 h1) (fun h2 : term744 m p => @lem134501 m k p h1)). Qed.
Lemma lem134509 (m : nat) (k : nat) (p : nat) (h1 : term150 m k p) : term744 m p.
Proof. exact (EQ_MP (@lem134508 m k p h1) (@lem134501 m k p h1)). Qed.
Lemma lem134510 (m : nat) (p : nat) (h1 : term726 m p) : term744 m p.
Proof. exact (ex_elim (@lem134422 m p h1) (fun k : nat => fun h0 : term724 m p k => @lem134509 m k p h0)). Qed.
Lemma lem134511 (m : nat) (p : nat) : term756 m p.
Proof. exact (fun h0 : term726 m p => @lem134510 m p h0). Qed.
Lemma lem134516 (m : nat) : term760 m.
Proof. exact (fun p : nat => @lem134511 m p). Qed.
Lemma lem134517 (m : nat) : term748 m.
Proof. exact (@lem134421 m (@lem134516 m)). Qed.
Lemma lem134518 (m : nat) : term711 m.
Proof. exact (EQ_MP (@lem134380 m) (@lem134517 m)). Qed.
Lemma lem134519 (m : nat) : term710 m.
Proof. exact (EQ_MP (@lem134314 m) (@lem134518 m)). Qed.
Lemma lem134520 (m : nat) : term709 m.
Proof. exact (EQ_MP (@lem134211 m) (@lem134519 m)). Qed.
Lemma lem134521 (m : nat) (h1 : term37 m) : term791 m.
Proof. exact (conj (@lem134070 m h1) (@lem134520 m)). Qed.
Lemma lem134522 (m : nat) (h1 : term37 m) : term626 m.
Proof. exact (@lem133983 m (@lem134521 m h1)). Qed.
Lemma lem134523 (m : nat) (h1 : term37 m) : term619 m.
Proof. exact (EQ_MP (@lem133227 m h1) (@lem134522 m h1)). Qed.
Lemma lem134524 (m : nat) (h1 : m = (NUMERAL 0)) : term619 m.
Proof. exact (EQ_MP (@lem133117 m h1) (@lem133980)). Qed.
Lemma lem134525 (m : nat) : term619 m.
Proof. exact (or_elim (@lem129037 m) (fun h0 : m = (NUMERAL 0) => @lem134524 m h0) (fun h0 : term37 m => @lem134523 m h0)). Qed.
Lemma lem134526 (n : nat) (m : nat) (h1 : term59 n) (h2 : n = (term569 m)) : (term571 m) = (term572 m).
Proof. exact (@lem134525 m (@lem132917 n m h1 h2)). Qed.
Lemma lem134527 (n : nat) (m : nat) (h1 : term59 n) (h2 : n = (term569 m)) : (term52 n) = (term37 n).
Proof. exact (EQ_MP (@lem132901 n m h2) (@lem134526 n m h1 h2)). Qed.
Lemma lem134528 (n : nat) (h1 : term59 n) (h2 : term39 n) : (term52 n) = (term37 n).
Proof. exact (ex_elim (@lem132887 n h2) (fun m : nat => fun h0 : term792 n m => @lem134527 n m h1 h0)). Qed.
Lemma lem134529 (n : nat) (h1 : term59 n) : term793 n.
Proof. exact (fun h0 : term39 n => @lem134528 n h1 h0). Qed.
Lemma lem134530 (n : nat) (h1 : term59 n) (h2 : Coq.Arith.PeanoNat.Nat.Even n) : (term52 n) = (term37 n).
Proof. exact (@lem134529 n h1 (@lem132886 n h2)). Qed.
Lemma lem134531 (n : nat) (h1 : term59 n) : (term52 n) = (term37 n).
Proof. exact (or_elim (@lem129055 n) (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem134530 n h1 h0) (fun h0 : Coq.Arith.PeanoNat.Nat.Odd n => @lem132883 n h1 h0)). Qed.
Lemma lem134532 (n : nat) : term63 n.
Proof. exact (fun h0 : term59 n => @lem134531 n h0). Qed.
Lemma lem134537 : term67.
Proof. exact (fun n : nat => @lem134532 n). Qed.
Lemma lem134538 : term72.
Proof. exact (@lem129097 (@lem134537)). Qed.
