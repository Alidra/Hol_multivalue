Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVMOD_EXIST_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_CLAUSES_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import LE_EXISTS_spec.
Require Import LT_ADDR_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_FORALL_THM_spec.
Require Import NOT_IMP_spec.
Require Import NOT_LE_spec.
Require Import NOT_LT_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import RIGHT_AND_EXISTS_THM_spec.
Require Import num_WOP_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10568_spec.
Require Import thm1820_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm37_spec.
Require Import thm82_spec.
Require Import thm89498_spec.
Lemma lem153862 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (term0 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem153863 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term0 m n).
Proof. exact (SYM (@lem153862 n m h1)). Qed.
Lemma lem153864 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (Peano.lt n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem153865 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (term0 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem153864 m n h1)). Qed.
Lemma lem153866 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt n m) => @lem153863 n m h1) (fun h1 : (Peano.lt n m) = (term0 m n) => @lem153865 m n h1)). Qed.
Lemma lem153867 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem153866 m n)). Qed.
Lemma lem153868 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem153869 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem153868) (@lem153867 m)). Qed.
Lemma lem153870 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem153869 m)). Qed.
Lemma lem153871 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem153872 : term7 = term8.
Proof. exact (MK_COMB (@lem153871) (@lem153870)). Qed.
Lemma lem153873 : term8.
Proof. exact (EQ_MP (@lem153872) (@lem97961)). Qed.
Lemma lem153874 (m : nat) : term9 m.
Proof. exact (@lem100773 m). Qed.
Lemma lem153875 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem153876 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem153875 m) (@lem153874 m)). Qed.
Lemma lem153877 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem153876 m n). Qed.
Lemma lem153878 (n : nat) (m : nat) : (term11 m n) = ((term12 m n) = (term13 m)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem153880 (m : nat) : term14 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem153881 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem153882 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem153881 m) (@lem153880 m)). Qed.
Lemma lem153883 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem153882 m n). Qed.
Lemma lem153884 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem153885 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem153884 m n) (@lem153883 m n)). Qed.
Lemma lem153886 (m : nat) (n : nat) (p : nat) : term18 m n p.
Proof. exact (@lem153885 m n p). Qed.
Lemma lem153887 (m : nat) (n : nat) (p : nat) : (term18 m n p) = ((term19 m n p) = (term20 m n p)).
Proof. exact (eq_refl (term18 m n p)). Qed.
Lemma lem153889 : term21.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem153890 : term22.
Proof. exact (proj2 (@lem153889)). Qed.
Lemma lem153911 : term23.
Proof. exact (proj1 (@lem153890)). Qed.
Lemma lem153912 (n : nat) : term24 n.
Proof. exact (@lem153911 n). Qed.
Lemma lem153913 (n : nat) : (term24 n) = ((term25 n) = n).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem153923 (m : nat) : term26 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem153924 (m : nat) : (term26 m) = (term27 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem153925 (m : nat) : term27 m.
Proof. exact (EQ_MP (@lem153924 m) (@lem153923 m)). Qed.
Lemma lem153926 (m : nat) (n : nat) : term28 m n.
Proof. exact (@lem153925 m n). Qed.
Lemma lem153927 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem153928 (m : nat) (n : nat) : term29 m n.
Proof. exact (EQ_MP (@lem153927 m n) (@lem153926 m n)). Qed.
Lemma lem153929 (m : nat) (n : nat) (p : nat) : term30 m n p.
Proof. exact (@lem153928 m n p). Qed.
Lemma lem153930 (m : nat) (n : nat) (p : nat) : (term30 m n p) = ((term31 m n p) = (term32 m n p)).
Proof. exact (eq_refl (term30 m n p)). Qed.
Lemma lem153932 {A : Type'} (P : Prop) : term33 A P.
Proof. exact (@lem5950 A P). Qed.
Lemma lem153933 {A : Type'} (P : Prop) : (term33 A P) = (term34 A P).
Proof. exact (eq_refl (term33 A P)). Qed.
Lemma lem153934 {A : Type'} (P : Prop) : term34 A P.
Proof. exact (EQ_MP (@lem153933 A P) (@lem153932 A P)). Qed.
Lemma lem153935 {A : Type'} (P : Prop) (Q : A -> Prop) : term35 A P Q.
Proof. exact (@lem153934 A P Q). Qed.
Lemma lem153936 {A : Type'} (P : Prop) (Q : A -> Prop) : (term35 A P Q) = ((term36 A P Q) = (term37 A P Q)).
Proof. exact (eq_refl (term35 A P Q)). Qed.
Lemma lem153938 (t1 : Prop) : term38 t1.
Proof. exact (@lem10299 t1). Qed.
Lemma lem153939 (t1 : Prop) : (term38 t1) = (term39 t1).
Proof. exact (eq_refl (term38 t1)). Qed.
Lemma lem153940 (t1 : Prop) : term39 t1.
Proof. exact (EQ_MP (@lem153939 t1) (@lem153938 t1)). Qed.
Lemma lem153941 (t1 : Prop) (t2 : Prop) : term40 t1 t2.
Proof. exact (@lem153940 t1 t2). Qed.
Lemma lem153942 (t1 : Prop) (t2 : Prop) : (term40 t1 t2) = ((term41 t1 t2) = (term42 t1 t2)).
Proof. exact (eq_refl (term40 t1 t2)). Qed.
Lemma lem153944 {A : Type'} (P : A -> Prop) : term43 A P.
Proof. exact (@lem10884 A P). Qed.
Lemma lem153945 {A : Type'} (P : A -> Prop) : (term43 A P) = ((term44 A P) = (term45 A P)).
Proof. exact (eq_refl (term43 A P)). Qed.
Lemma lem153947 (m : nat) : term46 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem153948 (m : nat) : (term46 m) = (term47 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem153949 (m : nat) : term47 m.
Proof. exact (EQ_MP (@lem153948 m) (@lem153947 m)). Qed.
Lemma lem153950 (m : nat) (n : nat) : term48 m n.
Proof. exact (@lem153949 m n). Qed.
Lemma lem153951 (n : nat) (m : nat) : (term48 m n) = ((Peano.le m n) = (term49 n m)).
Proof. exact (eq_refl (term48 m n)). Qed.
Lemma lem153973 : term50.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem153974 (n : nat) : term51 n.
Proof. exact (@lem153973 n). Qed.
Lemma lem153975 (n : nat) : (term51 n) = ((term52 n) = n).
Proof. exact (eq_refl (term51 n)). Qed.
Lemma lem154007 : term53.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem154008 (n : nat) : term54 n.
Proof. exact (@lem154007 n). Qed.
Lemma lem154009 (n : nat) : (term54 n) = ((term55 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term54 n)). Qed.
Lemma lem154011 {A : Type'} (P : A -> Prop) : term56 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem154012 {A : Type'} (P : A -> Prop) : (term56 A P) = (term57 A P).
Proof. exact (eq_refl (term56 A P)). Qed.
Lemma lem154013 {A : Type'} (P : A -> Prop) : term57 A P.
Proof. exact (EQ_MP (@lem154012 A P) (@lem154011 A P)). Qed.
Lemma lem154014 {A : Type'} (P : A -> Prop) (Q : Prop) : term58 A P Q.
Proof. exact (@lem154013 A P Q). Qed.
Lemma lem154015 {A : Type'} (P : A -> Prop) (Q : Prop) : (term58 A P Q) = ((term59 A P Q) = (term60 A P Q)).
Proof. exact (eq_refl (term58 A P Q)). Qed.
Lemma lem154017 (m : nat) (n : nat) : term61 m n.
Proof. exact (@lem116994 (term62 m n)). Qed.
Lemma lem154018 (m : nat) (n : nat) : (term61 m n) = ((term63 m n) = (term64 m n)).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem154019 (m : nat) (n : nat) : (term63 m n) = (term64 m n).
Proof. exact (EQ_MP (@lem154018 m n) (@lem154017 m n)). Qed.
Lemma lem154020 (n : nat) (h1 : term65 n) : term65 n.
Proof. exact (h1). Qed.
Lemma lem154021 (m : nat) (n : nat) (n' : nat) : (term66 m n n') = (term67 m n n').
Proof. exact (eq_refl (term66 m n n')). Qed.
Lemma lem154022 (m : nat) (n : nat) : (term68 m n) = (term62 m n).
Proof. exact (fun_ext (fun n' : nat => @lem154021 m n n')). Qed.
Lemma lem154023 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem154024 (m : nat) (n : nat) : (term63 m n) = (term69 m n).
Proof. exact (MK_COMB (@lem154023) (@lem154022 m n)). Qed.
Lemma lem154025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem154026 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem154025) (@lem154024 m n)). Qed.
Lemma lem154027 (m : nat) (n : nat) (n' : nat) : (term66 m n n') = (term67 m n n').
Proof. exact (eq_refl (term66 m n n')). Qed.
Lemma lem154028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem154029 (m : nat) (n : nat) (n' : nat) : (term72 m n n') = (term73 m n n').
Proof. exact (MK_COMB (@lem154028) (@lem154027 m n n')). Qed.
Lemma lem154030 (m : nat) (n : nat) (m' : nat) : (term66 m n m') = (term67 m n m').
Proof. exact (eq_refl (term66 m n m')). Qed.
Lemma lem154031 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem154032 (m : nat) (n : nat) (m' : nat) : (term74 m n m') = (term75 m n m').
Proof. exact (MK_COMB (@lem154031) (@lem154030 m n m')). Qed.
Lemma lem154033 (m' : nat) (n' : nat) : (term76 m' n') = (term76 m' n').
Proof. exact (eq_refl (term76 m' n')). Qed.
Lemma lem154034 (n' : nat) (m : nat) (n : nat) (m' : nat) : (term77 n' m n m') = (term78 n' m n m').
Proof. exact (MK_COMB (@lem154033 m' n') (@lem154032 m n m')). Qed.
Lemma lem154035 (n' : nat) (m : nat) (n : nat) : (term79 n' m n) = (term80 n' m n).
Proof. exact (fun_ext (fun m' : nat => @lem154034 n' m n m')). Qed.
Lemma lem154036 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem154037 (n' : nat) (m : nat) (n : nat) : (term81 n' m n) = (term82 n' m n).
Proof. exact (MK_COMB (@lem154036) (@lem154035 n' m n)). Qed.
Lemma lem154038 (n' : nat) (m : nat) (n : nat) : (term83 n' m n) = (term84 n' m n).
Proof. exact (MK_COMB (@lem154029 m n n') (@lem154037 n' m n)). Qed.
Lemma lem154039 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (fun_ext (fun n' : nat => @lem154038 n' m n)). Qed.
Lemma lem154040 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem154041 (m : nat) (n : nat) : (term64 m n) = (term87 m n).
Proof. exact (MK_COMB (@lem154040) (@lem154039 m n)). Qed.
Lemma lem154042 (m : nat) (n : nat) : ((term63 m n) = (term64 m n)) = ((term69 m n) = (term87 m n)).
Proof. exact (MK_COMB (@lem154026 m n) (@lem154041 m n)). Qed.
Lemma lem154043 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem154044 (m : nat) (n : nat) : (term88 m n) = (term89 m n).
Proof. exact (MK_COMB (@lem154043) (@lem154042 m n)). Qed.
Lemma lem154045 (m : nat) (n : nat) : (term90 m n) = (term90 m n).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem154046 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (MK_COMB (@lem154044 m n) (@lem154045 m n)). Qed.
Lemma lem154047 (m : nat) (n : nat) : (term92 m n) = (term91 m n).
Proof. exact (SYM (@lem154046 m n)). Qed.
Lemma lem154048 (m : nat) (n : nat) (h1 : (term69 m n) = (term87 m n)) : (term69 m n) = (term87 m n).
Proof. exact (h1). Qed.
Lemma lem154051 (m : nat) (n : nat) : term93 m n.
Proof. exact (@lem37 (term69 m n) (term87 m n)). Qed.
Lemma lem154052 (m : nat) (n : nat) (h1 : (term69 m n) = (term87 m n)) : term94 m n.
Proof. exact (@lem154051 m n (@lem154048 m n h1)). Qed.
Lemma lem154056 {A : Type'} (P : A -> Prop) (Q : Prop) : (term59 A P Q) = (term60 A P Q).
Proof. exact (EQ_MP (@lem154015 A P Q) (@lem154014 A P Q)). Qed.
Lemma lem154057 (P : nat -> Prop) (Q : Prop) : (term95 P Q) = (term96 P Q).
Proof. exact (@lem154056 nat P Q). Qed.
Lemma lem154058 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (@lem154057 (term62 m n) (term87 m n)). Qed.
Lemma lem154059 (m : nat) (n : nat) (n' : nat) : (term66 m n n') = (term67 m n n').
Proof. exact (eq_refl (term66 m n n')). Qed.
Lemma lem154060 (m : nat) (n : nat) : (term68 m n) = (term62 m n).
Proof. exact (fun_ext (fun n' : nat => @lem154059 m n n')). Qed.
Lemma lem154061 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem154062 (m : nat) (n : nat) : (term63 m n) = (term69 m n).
Proof. exact (MK_COMB (@lem154061) (@lem154060 m n)). Qed.
Lemma lem154063 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem154064 (m : nat) (n : nat) : (term99 m n) = (term100 m n).
Proof. exact (MK_COMB (@lem154063) (@lem154062 m n)). Qed.
Lemma lem154065 (m : nat) (n : nat) : (term87 m n) = (term87 m n).
Proof. exact (eq_refl (term87 m n)). Qed.
Lemma lem154066 (m : nat) (n : nat) : (term97 m n) = (term94 m n).
Proof. exact (MK_COMB (@lem154064 m n) (@lem154065 m n)). Qed.
Lemma lem154067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem154068 (m : nat) (n : nat) : (term101 m n) = (term102 m n).
Proof. exact (MK_COMB (@lem154067) (@lem154066 m n)). Qed.
Lemma lem154069 (m : nat) (n : nat) (n' : nat) : (term66 m n n') = (term67 m n n').
Proof. exact (eq_refl (term66 m n n')). Qed.
Lemma lem154070 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem154071 (m : nat) (n : nat) (n' : nat) : (term103 m n n') = (term104 m n n').
Proof. exact (MK_COMB (@lem154070) (@lem154069 m n n')). Qed.
Lemma lem154072 (m : nat) (n : nat) : (term87 m n) = (term87 m n).
Proof. exact (eq_refl (term87 m n)). Qed.
Lemma lem154073 (n' : nat) (m : nat) (n : nat) : (term105 n' m n) = (term106 n' m n).
Proof. exact (MK_COMB (@lem154071 m n n') (@lem154072 m n)). Qed.
Lemma lem154074 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (fun_ext (fun n' : nat => @lem154073 n' m n)). Qed.
Lemma lem154075 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem154076 (m : nat) (n : nat) : (term98 m n) = (term109 m n).
Proof. exact (MK_COMB (@lem154075) (@lem154074 m n)). Qed.
Lemma lem154077 (m : nat) (n : nat) : ((term97 m n) = (term98 m n)) = ((term94 m n) = (term109 m n)).
Proof. exact (MK_COMB (@lem154068 m n) (@lem154076 m n)). Qed.
Lemma lem154078 (m : nat) (n : nat) : (term94 m n) = (term109 m n).
Proof. exact (EQ_MP (@lem154077 m n) (@lem154058 m n)). Qed.
Lemma lem154084 {A : Type'} (P : A -> Prop) (Q : Prop) : (term59 A P Q) = (term60 A P Q).
Proof. exact (EQ_MP (@lem154015 A P Q) (@lem154014 A P Q)). Qed.
Lemma lem154085 (P : nat -> Prop) (Q : Prop) : (term95 P Q) = (term96 P Q).
Proof. exact (@lem154084 nat P Q). Qed.
Lemma lem154086 (n' : nat) (m : nat) (n : nat) : (term110 n' m n) = (term111 n' m n).
Proof. exact (@lem154085 (term112 m n n') (term87 m n)). Qed.
Lemma lem154087 (m : nat) (q : nat) (n : nat) (n' : nat) : (term113 m n n' q) = (m = (term114 q n n')).
Proof. exact (eq_refl (term113 m n n' q)). Qed.
Lemma lem154088 (m : nat) (n : nat) (n' : nat) : (term115 m n n') = (term112 m n n').
Proof. exact (fun_ext (fun q : nat => @lem154087 m q n n')). Qed.
Lemma lem154089 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem154090 (m : nat) (n : nat) (n' : nat) : (term116 m n n') = (term67 m n n').
Proof. exact (MK_COMB (@lem154089) (@lem154088 m n n')). Qed.
Lemma lem154091 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem154092 (m : nat) (n : nat) (n' : nat) : (term117 m n n') = (term104 m n n').
Proof. exact (MK_COMB (@lem154091) (@lem154090 m n n')). Qed.
Lemma lem154093 (m : nat) (n : nat) : (term87 m n) = (term87 m n).
Proof. exact (eq_refl (term87 m n)). Qed.
Lemma lem154094 (n' : nat) (m : nat) (n : nat) : (term110 n' m n) = (term106 n' m n).
Proof. exact (MK_COMB (@lem154092 m n n') (@lem154093 m n)). Qed.
Lemma lem154095 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem154096 (n' : nat) (m : nat) (n : nat) : (term118 n' m n) = (term119 n' m n).
Proof. exact (MK_COMB (@lem154095) (@lem154094 n' m n)). Qed.
Lemma lem154097 (m : nat) (q : nat) (n : nat) (n' : nat) : (term113 m n n' q) = (m = (term114 q n n')).
Proof. exact (eq_refl (term113 m n n' q)). Qed.
Lemma lem154098 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem154099 (m : nat) (q : nat) (n : nat) (n' : nat) : (term120 m n n' q) = (term121 m q n n').
Proof. exact (MK_COMB (@lem154098) (@lem154097 m q n n')). Qed.
Lemma lem154100 (m : nat) (n : nat) : (term87 m n) = (term87 m n).
Proof. exact (eq_refl (term87 m n)). Qed.
Lemma lem154101 (q : nat) (n' : nat) (m : nat) (n : nat) : (term122 n' q m n) = (term123 q n' m n).
Proof. exact (MK_COMB (@lem154099 m q n n') (@lem154100 m n)). Qed.
Lemma lem154102 (n' : nat) (m : nat) (n : nat) : (term124 n' m n) = (term125 n' m n).
Proof. exact (fun_ext (fun q : nat => @lem154101 q n' m n)). Qed.
Lemma lem154103 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem154104 (n' : nat) (m : nat) (n : nat) : (term111 n' m n) = (term126 n' m n).
Proof. exact (MK_COMB (@lem154103) (@lem154102 n' m n)). Qed.
Lemma lem154105 (n' : nat) (m : nat) (n : nat) : ((term110 n' m n) = (term111 n' m n)) = ((term106 n' m n) = (term126 n' m n)).
Proof. exact (MK_COMB (@lem154096 n' m n) (@lem154104 n' m n)). Qed.
Lemma lem154106 (n' : nat) (m : nat) (n : nat) : (term106 n' m n) = (term126 n' m n).
Proof. exact (EQ_MP (@lem154105 n' m n) (@lem154086 n' m n)). Qed.
Lemma lem154141 (m : nat) (n : nat) : (term108 m n) = (term127 m n).
Proof. exact (fun_ext (fun n' : nat => @lem154106 n' m n)). Qed.
Lemma lem154142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem154143 (m : nat) (n : nat) : (term109 m n) = (term128 m n).
Proof. exact (MK_COMB (@lem154142) (@lem154141 m n)). Qed.
Lemma lem154148 (m : nat) (n : nat) : (term94 m n) = (term128 m n).
Proof. exact (TRANS (@lem154078 m n) (@lem154143 m n)). Qed.
Lemma lem154149 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem154150 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (MK_COMB (@lem154149) (@lem154148 m n)). Qed.
Lemma lem154163 (m : nat) (n : nat) : (term90 m n) = (term90 m n).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem154164 (m : nat) (n : nat) : (term131 m n) = (term132 m n).
Proof. exact (MK_COMB (@lem154150 m n) (@lem154163 m n)). Qed.
Lemma lem154167 (m : nat) (n : nat) : (term132 m n) = (term131 m n).
Proof. exact (SYM (@lem154164 m n)). Qed.
Lemma lem154168 (m : nat) (n : nat) (h1 : term128 m n) : term128 m n.
Proof. exact (h1). Qed.
Lemma lem154169 (m : nat) (n : nat) (h1 : term128 m n) : term133 n m.
Proof. exact (@lem154168 m n h1 m). Qed.
Lemma lem154170 (m : nat) (n : nat) : (term133 n m) = (term134 m n).
Proof. exact (eq_refl (term133 n m)). Qed.
Lemma lem154171 (m : nat) (n : nat) (h1 : term128 m n) : term134 m n.
Proof. exact (EQ_MP (@lem154170 m n) (@lem154169 m n h1)). Qed.
Lemma lem154172 (m : nat) (n : nat) (h1 : term128 m n) : term135 m n.
Proof. exact (@lem154171 m n h1 (NUMERAL 0)). Qed.
Lemma lem154173 (m : nat) (n : nat) : (term135 m n) = (term136 m n).
Proof. exact (eq_refl (term135 m n)). Qed.
Lemma lem154174 (m : nat) (n : nat) (h1 : term128 m n) : term136 m n.
Proof. exact (EQ_MP (@lem154173 m n) (@lem154172 m n h1)). Qed.
Lemma lem154184 (n : nat) : (term55 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem154009 n) (@lem154008 n)). Qed.
Lemma lem154185 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem154186 (n : nat) : (term137 n) = term138.
Proof. exact (MK_COMB (@lem154185) (@lem154184 n)). Qed.
Lemma lem154187 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem154188 (n : nat) (m : nat) : (term139 n m) = (term52 m).
Proof. exact (MK_COMB (@lem154186 n) (@lem154187 m)). Qed.
Lemma lem154190 (n : nat) : (term52 n) = n.
Proof. exact (EQ_MP (@lem153975 n) (@lem153974 n)). Qed.
Lemma lem154191 (m : nat) : (term52 m) = m.
Proof. exact (@lem154190 m). Qed.
Lemma lem154192 (n : nat) (m : nat) : (term139 n m) = m.
Proof. exact (TRANS (@lem154188 n m) (@lem154191 m)). Qed.
Lemma lem154193 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem154194 (n : nat) (m : nat) : (m = (term139 n m)) = (m = m).
Proof. exact (MK_COMB (@lem154193 m) (@lem154192 n m)). Qed.
Lemma lem154196 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem154197 (x : nat) : (x = x) = True.
Proof. exact (@lem154196 nat x). Qed.
Lemma lem154198 (m : nat) : (m = m) = True.
Proof. exact (@lem154197 m). Qed.
Lemma lem154199 (n : nat) (m : nat) : (m = (term139 n m)) = True.
Proof. exact (TRANS (@lem154194 n m) (@lem154198 m)). Qed.
Lemma lem154200 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem154201 (n : nat) (m : nat) : (term140 n m) = (imp True).
Proof. exact (MK_COMB (@lem154200) (@lem154199 n m)). Qed.
Lemma lem154226 (m : nat) (n : nat) : (term87 m n) = (term87 m n).
Proof. exact (eq_refl (term87 m n)). Qed.
Lemma lem154227 (m : nat) (n : nat) : (term136 m n) = (term141 m n).
Proof. exact (MK_COMB (@lem154201 n m) (@lem154226 m n)). Qed.
Lemma lem154229 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem154230 (m : nat) (n : nat) : (term141 m n) = (term87 m n).
Proof. exact (@lem154229 (term87 m n)). Qed.
Lemma lem154255 (m : nat) (n : nat) : (term136 m n) = (term87 m n).
Proof. exact (TRANS (@lem154227 m n) (@lem154230 m n)). Qed.
Lemma lem154256 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem154257 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (MK_COMB (@lem154256) (@lem154255 m n)). Qed.
Lemma lem154270 (m : nat) (n : nat) : (term90 m n) = (term90 m n).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem154271 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (MK_COMB (@lem154257 m n) (@lem154270 m n)). Qed.
Lemma lem154274 (m : nat) (n : nat) : (term145 m n) = (term144 m n).
Proof. exact (SYM (@lem154271 m n)). Qed.
Lemma lem154275 (m : nat) (n : nat) (h1 : term87 m n) : term87 m n.
Proof. exact (h1). Qed.
Lemma lem154276 (r : nat) (m : nat) (n : nat) (h1 : term84 r m n) : term84 r m n.
Proof. exact (h1). Qed.
Lemma lem154277 (r : nat) (m : nat) (n : nat) (h1 : term84 r m n) : term84 r m n.
Proof. exact (h1). Qed.
Lemma lem154278 (r : nat) (m : nat) (n : nat) (h1 : term82 r m n) : term82 r m n.
Proof. exact (h1). Qed.
Lemma lem154279 (m : nat) (n : nat) (r : nat) (h1 : term67 m n r) : term67 m n r.
Proof. exact (h1). Qed.
Lemma lem154281 (r : nat) (m : nat) (n : nat) (h1 : term82 r m n) : term82 r m n.
Proof. exact (h1). Qed.
Lemma lem154282 (q : nat) (r : nat) (m : nat) (n : nat) : (term146 m q r n) = (term147 q r m n).
Proof. exact (@lem10568 (term148 m q r n) (term82 r m n)). Qed.
Lemma lem154283 (m : nat) (q : nat) (r : nat) (n : nat) : (term147 q r m n) = (term146 m q r n).
Proof. exact (SYM (@lem154282 q r m n)). Qed.
Lemma lem154284 (m : nat) : term149 m.
Proof. exact (@lem98377 m). Qed.
Lemma lem154285 (m : nat) : (term149 m) = (term150 m).
Proof. exact (eq_refl (term149 m)). Qed.
Lemma lem154286 (m : nat) : term150 m.
Proof. exact (EQ_MP (@lem154285 m) (@lem154284 m)). Qed.
Lemma lem154287 (m : nat) (n : nat) : term151 m n.
Proof. exact (@lem154286 m n). Qed.
Lemma lem154288 (n : nat) (m : nat) : (term151 m n) = ((term152 m n) = (Peano.le n m)).
Proof. exact (eq_refl (term151 m n)). Qed.
Lemma lem154310 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : m = (term114 q n r).
Proof. exact (h1). Qed.
Lemma lem154311 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem154312 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (@eq nat m) = (term153 q n r).
Proof. exact (MK_COMB (@lem154311) (@lem154310 m q n r h1)). Qed.
Lemma lem154313 (q : nat) (n : nat) (r : nat) : (term114 q n r) = (term114 q n r).
Proof. exact (eq_refl (term114 q n r)). Qed.
Lemma lem154314 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (m = (term114 q n r)) = ((term114 q n r) = (term114 q n r)).
Proof. exact (MK_COMB (@lem154312 m q n r h1) (@lem154313 q n r)). Qed.
Lemma lem154316 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem154317 (x : nat) : (x = x) = True.
Proof. exact (@lem154316 nat x). Qed.
Lemma lem154318 (q : nat) (n : nat) (r : nat) : ((term114 q n r) = (term114 q n r)) = True.
Proof. exact (@lem154317 (term114 q n r)). Qed.
Lemma lem154319 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (m = (term114 q n r)) = True.
Proof. exact (TRANS (@lem154314 m q n r h1) (@lem154318 q n r)). Qed.
Lemma lem154320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem154321 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (term154 m q n r) = (and True).
Proof. exact (MK_COMB (@lem154320) (@lem154319 m q n r h1)). Qed.
Lemma lem154322 (r : nat) (n : nat) : (Peano.lt r n) = (Peano.lt r n).
Proof. exact (eq_refl (Peano.lt r n)). Qed.
Lemma lem154323 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (term148 m q r n) = (term155 r n).
Proof. exact (MK_COMB (@lem154321 m q n r h1) (@lem154322 r n)). Qed.
Lemma lem154325 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem154326 (r : nat) (n : nat) : (term155 r n) = (Peano.lt r n).
Proof. exact (@lem154325 (Peano.lt r n)). Qed.
Lemma lem154327 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (term148 m q r n) = (Peano.lt r n).
Proof. exact (TRANS (@lem154323 m q n r h1) (@lem154326 r n)). Qed.
Lemma lem154328 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem154329 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (term156 m q r n) = (term152 r n).
Proof. exact (MK_COMB (@lem154328) (@lem154327 m q n r h1)). Qed.
Lemma lem154331 (n : nat) (m : nat) : (term152 m n) = (Peano.le n m).
Proof. exact (EQ_MP (@lem154288 n m) (@lem154287 m n)). Qed.
Lemma lem154332 (n : nat) (r : nat) : (term152 r n) = (Peano.le n r).
Proof. exact (@lem154331 n r). Qed.
Lemma lem154333 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (term156 m q r n) = (Peano.le n r).
Proof. exact (TRANS (@lem154329 m q n r h1) (@lem154332 n r)). Qed.
Lemma lem154334 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem154335 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (term157 m q r n) = (term158 n r).
Proof. exact (MK_COMB (@lem154334) (@lem154333 m q n r h1)). Qed.
Lemma lem154359 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : m = (term114 q n r).
Proof. exact (h1). Qed.
Lemma lem154360 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem154361 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (@eq nat m) = (term153 q n r).
Proof. exact (MK_COMB (@lem154360) (@lem154359 m q n r h1)). Qed.
Lemma lem154362 (_3079 : nat) (n : nat) (m' : nat) : (term114 _3079 n m') = (term114 _3079 n m').
Proof. exact (eq_refl (term114 _3079 n m')). Qed.
Lemma lem154363 (_3079 : nat) (m' : nat) (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (m = (term114 _3079 n m')) = ((term114 q n r) = (term114 _3079 n m')).
Proof. exact (MK_COMB (@lem154361 m q n r h1) (@lem154362 _3079 n m')). Qed.
Lemma lem154368 (m' : nat) (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (term112 m n m') = (term159 q r n m').
Proof. exact (fun_ext (fun _3079 : nat => @lem154363 _3079 m' m q n r h1)). Qed.
Lemma lem154369 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem154370 (m' : nat) (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (term67 m n m') = (term160 q r n m').
Proof. exact (MK_COMB (@lem154369) (@lem154368 m' m q n r h1)). Qed.
Lemma lem154375 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem154376 (m' : nat) (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (term75 m n m') = (term161 q r n m').
Proof. exact (MK_COMB (@lem154375) (@lem154370 m' m q n r h1)). Qed.
Lemma lem154377 (m' : nat) (r : nat) : (term76 m' r) = (term76 m' r).
Proof. exact (eq_refl (term76 m' r)). Qed.
Lemma lem154378 (m' : nat) (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (term78 r m n m') = (term162 q r n m').
Proof. exact (MK_COMB (@lem154377 m' r) (@lem154376 m' m q n r h1)). Qed.
Lemma lem154381 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (term80 r m n) = (term163 q r n).
Proof. exact (fun_ext (fun m' : nat => @lem154378 m' m q n r h1)). Qed.
Lemma lem154382 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem154383 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (term82 r m n) = (term164 q r n).
Proof. exact (MK_COMB (@lem154382) (@lem154381 m q n r h1)). Qed.
Lemma lem154388 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem154389 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (term165 r m n) = (term166 q r n).
Proof. exact (MK_COMB (@lem154388) (@lem154383 m q n r h1)). Qed.
Lemma lem154390 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (term147 q r m n) = (term167 q r n).
Proof. exact (MK_COMB (@lem154335 m q n r h1) (@lem154389 m q n r h1)). Qed.
Lemma lem154393 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term114 q n r)) : (term167 q r n) = (term147 q r m n).
Proof. exact (SYM (@lem154390 m q n r h1)). Qed.
Lemma lem154394 (n : nat) (r : nat) (h1 : Peano.le n r) : Peano.le n r.
Proof. exact (h1). Qed.
Lemma lem154396 (n : nat) (m : nat) : (Peano.le m n) = (term49 n m).
Proof. exact (EQ_MP (@lem153951 n m) (@lem153950 m n)). Qed.
Lemma lem154397 (r : nat) (n : nat) : (Peano.le n r) = (term49 r n).
Proof. exact (@lem154396 r n). Qed.
Lemma lem154404 (n : nat) (r : nat) (h1 : Peano.le n r) : term49 r n.
Proof. exact (EQ_MP (@lem154397 r n) (@lem154394 n r h1)). Qed.
Lemma lem154405 (r : nat) (n : nat) (d : nat) (h1 : r = (Nat.add n d)) : r = (Nat.add n d).
Proof. exact (h1). Qed.
Lemma lem154406 (q : nat) (n : nat) : (term168 q n) = (term168 q n).
Proof. exact (eq_refl (term168 q n)). Qed.
Lemma lem154407 (q : nat) (r : nat) (n : nat) (d : nat) (h1 : r = (Nat.add n d)) : (term169 q n r) = (term170 q n d).
Proof. exact (MK_COMB (@lem154406 q n) (@lem154405 r n d h1)). Qed.
Lemma lem154408 (q : nat) (d : nat) (n : nat) : (term170 q n d) = (term171 q d n).
Proof. exact (eq_refl (term170 q n d)). Qed.
Lemma lem154409 (q : nat) (n : nat) (r : nat) : (term172 q n r) = (term172 q n r).
Proof. exact (eq_refl (term172 q n r)). Qed.
Lemma lem154410 (r : nat) (q : nat) (d : nat) (n : nat) : ((term169 q n r) = (term170 q n d)) = ((term169 q n r) = (term171 q d n)).
Proof. exact (MK_COMB (@lem154409 q n r) (@lem154408 q d n)). Qed.
Lemma lem154411 (q : nat) (r : nat) (n : nat) : (term169 q n r) = (term166 q r n).
Proof. exact (eq_refl (term169 q n r)). Qed.
Lemma lem154412 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem154413 (q : nat) (r : nat) (n : nat) : (term172 q n r) = (term173 q r n).
Proof. exact (MK_COMB (@lem154412) (@lem154411 q r n)). Qed.
Lemma lem154414 (q : nat) (d : nat) (n : nat) : (term171 q d n) = (term171 q d n).
Proof. exact (eq_refl (term171 q d n)). Qed.
Lemma lem154415 (r : nat) (q : nat) (d : nat) (n : nat) : ((term169 q n r) = (term171 q d n)) = ((term166 q r n) = (term171 q d n)).
Proof. exact (MK_COMB (@lem154413 q r n) (@lem154414 q d n)). Qed.
Lemma lem154416 (r : nat) (q : nat) (d : nat) (n : nat) : ((term169 q n r) = (term170 q n d)) = ((term166 q r n) = (term171 q d n)).
Proof. exact (TRANS (@lem154410 r q d n) (@lem154415 r q d n)). Qed.
Lemma lem154417 (q : nat) (r : nat) (n : nat) (d : nat) (h1 : r = (Nat.add n d)) : (term166 q r n) = (term171 q d n).
Proof. exact (EQ_MP (@lem154416 r q d n) (@lem154407 q r n d h1)). Qed.
Lemma lem154418 (q : nat) (r : nat) (n : nat) (d : nat) (h1 : r = (Nat.add n d)) : (term171 q d n) = (term166 q r n).
Proof. exact (SYM (@lem154417 q r n d h1)). Qed.
Lemma lem154432 (n : nat) (h1 : term65 n) : term65 n.
Proof. exact (h1). Qed.
Lemma lem154447 {A : Type'} (P : A -> Prop) : (term44 A P) = (term45 A P).
Proof. exact (EQ_MP (@lem153945 A P) (@lem153944 A P)). Qed.
Lemma lem154448 (P : nat -> Prop) : (term174 P) = (term175 P).
Proof. exact (@lem154447 nat P). Qed.
Lemma lem154449 (q : nat) (d : nat) (n : nat) : (term176 q d n) = (term177 q d n).
Proof. exact (@lem154448 (term178 q d n)). Qed.
Lemma lem154450 (q : nat) (d : nat) (n : nat) (m' : nat) : (term179 q d n m') = (term180 q d n m').
Proof. exact (eq_refl (term179 q d n m')). Qed.
Lemma lem154451 (q : nat) (d : nat) (n : nat) : (term181 q d n) = (term178 q d n).
Proof. exact (fun_ext (fun m' : nat => @lem154450 q d n m')). Qed.
Lemma lem154452 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem154453 (q : nat) (d : nat) (n : nat) : (term182 q d n) = (term183 q d n).
Proof. exact (MK_COMB (@lem154452) (@lem154451 q d n)). Qed.
Lemma lem154454 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem154455 (q : nat) (d : nat) (n : nat) : (term176 q d n) = (term171 q d n).
Proof. exact (MK_COMB (@lem154454) (@lem154453 q d n)). Qed.
Lemma lem154456 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem154457 (q : nat) (d : nat) (n : nat) : (term184 q d n) = (term185 q d n).
Proof. exact (MK_COMB (@lem154456) (@lem154455 q d n)). Qed.
Lemma lem154458 (q : nat) (d : nat) (n : nat) (m' : nat) : (term179 q d n m') = (term180 q d n m').
Proof. exact (eq_refl (term179 q d n m')). Qed.
Lemma lem154459 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem154460 (q : nat) (d : nat) (n : nat) (m' : nat) : (term186 q d n m') = (term187 q d n m').
Proof. exact (MK_COMB (@lem154459) (@lem154458 q d n m')). Qed.
Lemma lem154461 (q : nat) (d : nat) (n : nat) : (term188 q d n) = (term189 q d n).
Proof. exact (fun_ext (fun m' : nat => @lem154460 q d n m')). Qed.
Lemma lem154462 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem154463 (q : nat) (d : nat) (n : nat) : (term177 q d n) = (term190 q d n).
Proof. exact (MK_COMB (@lem154462) (@lem154461 q d n)). Qed.
Lemma lem154464 (q : nat) (d : nat) (n : nat) : ((term176 q d n) = (term177 q d n)) = ((term171 q d n) = (term190 q d n)).
Proof. exact (MK_COMB (@lem154457 q d n) (@lem154463 q d n)). Qed.
Lemma lem154465 (q : nat) (d : nat) (n : nat) : (term171 q d n) = (term190 q d n).
Proof. exact (EQ_MP (@lem154464 q d n) (@lem154449 q d n)). Qed.
Lemma lem154478 (q : nat) (d : nat) (n : nat) : (term190 q d n) = (term171 q d n).
Proof. exact (SYM (@lem154465 q d n)). Qed.
Lemma lem154480 (t1 : Prop) (t2 : Prop) : (term41 t1 t2) = (term42 t1 t2).
Proof. exact (EQ_MP (@lem153942 t1 t2) (@lem153941 t1 t2)). Qed.
Lemma lem154481 (q : nat) (n : nat) (d : nat) : (term191 q n d) = (term192 q n d).
Proof. exact (@lem154480 (term12 n d) (term193 q n d)). Qed.
Lemma lem154485 (t : Prop) : (term194 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem154486 (q : nat) (n : nat) (d : nat) : (term195 q n d) = (term196 q n d).
Proof. exact (@lem154485 (term196 q n d)). Qed.
Lemma lem154493 (n : nat) (d : nat) : (term197 n d) = (term197 n d).
Proof. exact (eq_refl (term197 n d)). Qed.
Lemma lem154494 (q : nat) (n : nat) (d : nat) : (term192 q n d) = (term198 q n d).
Proof. exact (MK_COMB (@lem154493 n d) (@lem154486 q n d)). Qed.
Lemma lem154496 {A : Type'} (P : Prop) (Q : A -> Prop) : (term36 A P Q) = (term37 A P Q).
Proof. exact (EQ_MP (@lem153936 A P Q) (@lem153935 A P Q)). Qed.
Lemma lem154497 (P : Prop) (Q : nat -> Prop) : (term199 P Q) = (term200 P Q).
Proof. exact (@lem154496 nat P Q). Qed.
Lemma lem154498 (q : nat) (n : nat) (d : nat) : (term201 q n d) = (term202 q n d).
Proof. exact (@lem154497 (term12 n d) (term203 q n d)). Qed.
Lemma lem154499 (q : nat) (q' : nat) (n : nat) (d : nat) : (term204 q n d q') = ((term205 q n d) = (term114 q' n d)).
Proof. exact (eq_refl (term204 q n d q')). Qed.
Lemma lem154500 (q : nat) (n : nat) (d : nat) : (term206 q n d) = (term203 q n d).
Proof. exact (fun_ext (fun q' : nat => @lem154499 q q' n d)). Qed.
Lemma lem154501 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem154502 (q : nat) (n : nat) (d : nat) : (term207 q n d) = (term196 q n d).
Proof. exact (MK_COMB (@lem154501) (@lem154500 q n d)). Qed.
Lemma lem154503 (n : nat) (d : nat) : (term197 n d) = (term197 n d).
Proof. exact (eq_refl (term197 n d)). Qed.
Lemma lem154504 (q : nat) (n : nat) (d : nat) : (term201 q n d) = (term198 q n d).
Proof. exact (MK_COMB (@lem154503 n d) (@lem154502 q n d)). Qed.
Lemma lem154505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem154506 (q : nat) (n : nat) (d : nat) : (term208 q n d) = (term209 q n d).
Proof. exact (MK_COMB (@lem154505) (@lem154504 q n d)). Qed.
Lemma lem154507 (q : nat) (q' : nat) (n : nat) (d : nat) : (term204 q n d q') = ((term205 q n d) = (term114 q' n d)).
Proof. exact (eq_refl (term204 q n d q')). Qed.
Lemma lem154508 (n : nat) (d : nat) : (term197 n d) = (term197 n d).
Proof. exact (eq_refl (term197 n d)). Qed.
Lemma lem154509 (q : nat) (q' : nat) (n : nat) (d : nat) : (term210 q n d q') = (term211 q q' n d).
Proof. exact (MK_COMB (@lem154508 n d) (@lem154507 q q' n d)). Qed.
Lemma lem154510 (q : nat) (n : nat) (d : nat) : (term212 q n d) = (term213 q n d).
Proof. exact (fun_ext (fun q' : nat => @lem154509 q q' n d)). Qed.
Lemma lem154511 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem154512 (q : nat) (n : nat) (d : nat) : (term202 q n d) = (term214 q n d).
Proof. exact (MK_COMB (@lem154511) (@lem154510 q n d)). Qed.
Lemma lem154513 (q : nat) (n : nat) (d : nat) : ((term201 q n d) = (term202 q n d)) = ((term198 q n d) = (term214 q n d)).
Proof. exact (MK_COMB (@lem154506 q n d) (@lem154512 q n d)). Qed.
Lemma lem154514 (q : nat) (n : nat) (d : nat) : (term198 q n d) = (term214 q n d).
Proof. exact (EQ_MP (@lem154513 q n d) (@lem154498 q n d)). Qed.
Lemma lem154523 (q : nat) (n : nat) (d : nat) : (term192 q n d) = (term214 q n d).
Proof. exact (TRANS (@lem154494 q n d) (@lem154514 q n d)). Qed.
Lemma lem154524 (q : nat) (n : nat) (d : nat) : (term191 q n d) = (term214 q n d).
Proof. exact (TRANS (@lem154481 q n d) (@lem154523 q n d)). Qed.
Lemma lem154525 (q : nat) (n : nat) (d : nat) : (term214 q n d) = (term191 q n d).
Proof. exact (SYM (@lem154524 q n d)). Qed.
Lemma lem154531 (m : nat) (n : nat) (p : nat) : (term31 m n p) = (term32 m n p).
Proof. exact (EQ_MP (@lem153930 m n p) (@lem153929 m n p)). Qed.
Lemma lem154532 (q : nat) (n : nat) : (term215 q n) = (term216 q n).
Proof. exact (@lem154531 q term217 n). Qed.
Lemma lem154533 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem154534 (q : nat) (n : nat) : (term218 q n) = (term219 q n).
Proof. exact (MK_COMB (@lem154533) (@lem154532 q n)). Qed.
Lemma lem154535 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem154536 (q : nat) (n : nat) (d : nat) : (term220 q n d) = (term221 q n d).
Proof. exact (MK_COMB (@lem154534 q n) (@lem154535 d)). Qed.
Lemma lem154537 (q : nat) (n : nat) (d : nat) : (term222 q n d) = (term222 q n d).
Proof. exact (eq_refl (term222 q n d)). Qed.
Lemma lem154538 (q : nat) (n : nat) (d : nat) : ((term205 q n d) = (term220 q n d)) = ((term205 q n d) = (term221 q n d)).
Proof. exact (MK_COMB (@lem154537 q n d) (@lem154536 q n d)). Qed.
Lemma lem154541 (n : nat) (d : nat) : (term197 n d) = (term197 n d).
Proof. exact (eq_refl (term197 n d)). Qed.
Lemma lem154542 (q : nat) (n : nat) (d : nat) : (term223 q n d) = (term224 q n d).
Proof. exact (MK_COMB (@lem154541 n d) (@lem154538 q n d)). Qed.
Lemma lem154545 (q : nat) (n : nat) (d : nat) : (term224 q n d) = (term223 q n d).
Proof. exact (SYM (@lem154542 q n d)). Qed.
Lemma lem154549 (n : nat) (m : nat) : (term12 m n) = (term13 m).
Proof. exact (EQ_MP (@lem153878 n m) (@lem153877 m n)). Qed.
Lemma lem154550 (d : nat) (n : nat) : (term12 n d) = (term13 n).
Proof. exact (@lem154549 d n). Qed.
Lemma lem154551 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem154552 (d : nat) (n : nat) : (term197 n d) = (term225 n).
Proof. exact (MK_COMB (@lem154551) (@lem154550 d n)). Qed.
Lemma lem154556 (m : nat) (n : nat) (p : nat) : (term19 m n p) = (term20 m n p).
Proof. exact (EQ_MP (@lem153887 m n p) (@lem153886 m n p)). Qed.
Lemma lem154557 (q : nat) (n : nat) (d : nat) : (term205 q n d) = (term226 q n d).
Proof. exact (@lem154556 (Nat.mul q n) n d). Qed.
Lemma lem154558 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem154559 (q : nat) (n : nat) (d : nat) : (term222 q n d) = (term227 q n d).
Proof. exact (MK_COMB (@lem154558) (@lem154557 q n d)). Qed.
Lemma lem154561 (n : nat) : (term25 n) = n.
Proof. exact (EQ_MP (@lem153913 n) (@lem153912 n)). Qed.
Lemma lem154562 (q : nat) (n : nat) : (term228 q n) = (term228 q n).
Proof. exact (eq_refl (term228 q n)). Qed.
Lemma lem154563 (q : nat) (n : nat) : (term216 q n) = (term229 q n).
Proof. exact (MK_COMB (@lem154562 q n) (@lem154561 n)). Qed.
Lemma lem154564 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem154565 (q : nat) (n : nat) : (term219 q n) = (term230 q n).
Proof. exact (MK_COMB (@lem154564) (@lem154563 q n)). Qed.
Lemma lem154566 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem154567 (q : nat) (n : nat) (d : nat) : (term221 q n d) = (term226 q n d).
Proof. exact (MK_COMB (@lem154565 q n) (@lem154566 d)). Qed.
Lemma lem154568 (q : nat) (n : nat) (d : nat) : ((term205 q n d) = (term221 q n d)) = ((term226 q n d) = (term226 q n d)).
Proof. exact (MK_COMB (@lem154559 q n d) (@lem154567 q n d)). Qed.
Lemma lem154570 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem154571 (x : nat) : (x = x) = True.
Proof. exact (@lem154570 nat x). Qed.
Lemma lem154572 (q : nat) (n : nat) (d : nat) : ((term226 q n d) = (term226 q n d)) = True.
Proof. exact (@lem154571 (term226 q n d)). Qed.
Lemma lem154573 (q : nat) (n : nat) (d : nat) : ((term205 q n d) = (term221 q n d)) = True.
Proof. exact (TRANS (@lem154568 q n d) (@lem154572 q n d)). Qed.
Lemma lem154574 (q : nat) (d : nat) (n : nat) : (term224 q n d) = (term231 n).
Proof. exact (MK_COMB (@lem154552 d n) (@lem154573 q n d)). Qed.
Lemma lem154576 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem154577 (n : nat) : (term231 n) = (term13 n).
Proof. exact (@lem154576 (term13 n)). Qed.
Lemma lem154578 (q : nat) (d : nat) (n : nat) : (term224 q n d) = (term13 n).
Proof. exact (TRANS (@lem154574 q d n) (@lem154577 n)). Qed.
Lemma lem154579 (q : nat) (n : nat) (d : nat) : (term13 n) = (term224 q n d).
Proof. exact (SYM (@lem154578 q d n)). Qed.
Lemma lem154587 : term232.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem154588 (m : nat) : term233 m.
Proof. exact (@lem154587 m). Qed.
Lemma lem154589 (m : nat) : (term233 m) = ((term234 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term233 m)). Qed.
Lemma lem154591 (m : nat) : term235 m.
Proof. exact (@lem153873 m). Qed.
Lemma lem154592 (m : nat) : (term235 m) = (term4 m).
Proof. exact (eq_refl (term235 m)). Qed.
Lemma lem154593 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem154592 m) (@lem154591 m)). Qed.
Lemma lem154594 (m : nat) (n : nat) : term236 m n.
Proof. exact (@lem154593 m n). Qed.
Lemma lem154595 (m : nat) (n : nat) : (term236 m n) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (eq_refl (term236 m n)). Qed.
Lemma lem154597 (n : nat) : term237 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem154611 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem154595 m n) (@lem154594 m n)). Qed.
Lemma lem154612 (n : nat) : (term13 n) = (term238 n).
Proof. exact (@lem154611 n (NUMERAL 0)). Qed.
Lemma lem154614 (m : nat) : (term234 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem154589 m) (@lem154588 m)). Qed.
Lemma lem154615 (n : nat) : (term234 n) = (n = (NUMERAL 0)).
Proof. exact (@lem154614 n). Qed.
Lemma lem154617 (n : nat) (h1 : term65 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem154597 n (@lem154432 n h1)). Qed.
Lemma lem154618 (n : nat) (h1 : term65 n) : (term234 n) = False.
Proof. exact (TRANS (@lem154615 n) (@lem154617 n h1)). Qed.
Lemma lem154619 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem154620 (n : nat) (h1 : term65 n) : (term238 n) = (~ False).
Proof. exact (MK_COMB (@lem154619) (@lem154618 n h1)). Qed.
Lemma lem154622 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem154623 (n : nat) (h1 : term65 n) : (term238 n) = True.
Proof. exact (TRANS (@lem154620 n h1) (@lem154622)). Qed.
Lemma lem154624 (n : nat) (h1 : term65 n) : (term13 n) = True.
Proof. exact (TRANS (@lem154612 n) (@lem154623 n h1)). Qed.
Lemma lem154625 (n : nat) (h1 : term65 n) : True = (term13 n).
Proof. exact (SYM (@lem154624 n h1)). Qed.
Lemma lem154626 (n : nat) (h1 : term65 n) : term13 n.
Proof. exact (EQ_MP (@lem154625 n h1) (@lem0)). Qed.
Lemma lem154627 (q : nat) (d : nat) (n : nat) (h1 : term65 n) : term224 q n d.
Proof. exact (EQ_MP (@lem154579 q n d) (@lem154626 n h1)). Qed.
Lemma lem154628 (q : nat) (d : nat) (n : nat) (h1 : term65 n) : term223 q n d.
Proof. exact (EQ_MP (@lem154545 q n d) (@lem154627 q d n h1)). Qed.
Lemma lem154629 (q : nat) (d : nat) (n : nat) (h1 : term65 n) : term214 q n d.
Proof. exact (ex_intro (term213 q n d) (term239 q) (@lem154628 q d n h1)). Qed.
Lemma lem154630 (q : nat) (d : nat) (n : nat) (h1 : term65 n) : term191 q n d.
Proof. exact (EQ_MP (@lem154525 q n d) (@lem154629 q d n h1)). Qed.
Lemma lem154631 (q : nat) (d : nat) (n : nat) (h1 : term65 n) : term190 q d n.
Proof. exact (ex_intro (term189 q d n) d (@lem154630 q d n h1)). Qed.
Lemma lem154632 (q : nat) (d : nat) (n : nat) (h1 : term65 n) : term171 q d n.
Proof. exact (EQ_MP (@lem154478 q d n) (@lem154631 q d n h1)). Qed.
Lemma lem154633 (q : nat) (d : nat) (n : nat) (h1 : term65 n) : (term65 n) = (term171 q d n).
Proof. exact (prop_ext (fun h2 : term65 n => @lem154632 q d n h1) (fun h2 : term171 q d n => @lem154432 n h1)). Qed.
Lemma lem154634 (q : nat) (d : nat) (n : nat) (h1 : term65 n) : term171 q d n.
Proof. exact (EQ_MP (@lem154633 q d n h1) (@lem154432 n h1)). Qed.
Lemma lem154635 (q : nat) (r : nat) (n : nat) (d : nat) (h1 : term65 n) (h2 : r = (Nat.add n d)) : term166 q r n.
Proof. exact (EQ_MP (@lem154418 q r n d h2) (@lem154634 q d n h1)). Qed.
Lemma lem154636 (q : nat) (n : nat) (r : nat) (h1 : term65 n) (h2 : Peano.le n r) : term166 q r n.
Proof. exact (ex_elim (@lem154404 n r h2) (fun d : nat => fun h0 : term240 r n d => @lem154635 q r n d h1 h0)). Qed.
Lemma lem154637 (q : nat) (r : nat) (n : nat) (h1 : term65 n) : term167 q r n.
Proof. exact (fun h0 : Peano.le n r => @lem154636 q n r h1 h0). Qed.
Lemma lem154638 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : term65 n) (h2 : m = (term114 q n r)) : term147 q r m n.
Proof. exact (EQ_MP (@lem154393 m q n r h2) (@lem154637 q r n h1)). Qed.
Lemma lem154639 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : term65 n) (h2 : m = (term114 q n r)) : term146 m q r n.
Proof. exact (EQ_MP (@lem154283 m q r n) (@lem154638 m q n r h1 h2)). Qed.
Lemma lem154640 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : term82 r m n) (h2 : term65 n) (h3 : m = (term114 q n r)) : term148 m q r n.
Proof. exact (@lem154639 m q n r h2 h3 (@lem154281 r m n h1)). Qed.
Lemma lem154641 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : term82 r m n) (h2 : term65 n) (h3 : m = (term114 q n r)) : term241 m q n.
Proof. exact (ex_intro (term242 m q n) r (@lem154640 m q n r h1 h2 h3)). Qed.
Lemma lem154642 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : term82 r m n) (h2 : term65 n) (h3 : m = (term114 q n r)) : term90 m n.
Proof. exact (ex_intro (term243 m n) q (@lem154641 m q n r h1 h2 h3)). Qed.
Lemma lem154643 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : term65 n) (h2 : m = (term114 q n r)) : term244 r m n.
Proof. exact (fun h0 : term82 r m n => @lem154642 m q n r h0 h1 h2). Qed.
Lemma lem154644 (r : nat) (m : nat) (n : nat) (h1 : term84 r m n) : term82 r m n.
Proof. exact (proj2 (@lem154277 r m n h1)). Qed.
Lemma lem154645 (r : nat) (m : nat) (n : nat) (h1 : term84 r m n) : term67 m n r.
Proof. exact (proj1 (@lem154277 r m n h1)). Qed.
Lemma lem154646 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : term82 r m n) (h2 : term65 n) (h3 : m = (term114 q n r)) : term90 m n.
Proof. exact (@lem154643 m q n r h2 h3 (@lem154278 r m n h1)). Qed.
Lemma lem154647 (m : nat) (r : nat) (n : nat) (h1 : term82 r m n) (h2 : term67 m n r) (h3 : term65 n) : term90 m n.
Proof. exact (ex_elim (@lem154279 m n r h2) (fun q : nat => fun h0 : term112 m n r q => @lem154646 m q n r h1 h3 h0)). Qed.
Lemma lem154648 (r : nat) (m : nat) (n : nat) (h1 : term67 m n r) (h2 : term65 n) (h3 : term84 r m n) : (term82 r m n) = (term90 m n).
Proof. exact (prop_ext (fun h4 : term82 r m n => @lem154647 m r n h4 h1 h2) (fun h4 : term90 m n => @lem154644 r m n h3)). Qed.
Lemma lem154649 (r : nat) (m : nat) (n : nat) (h1 : term67 m n r) (h2 : term65 n) (h3 : term84 r m n) : term90 m n.
Proof. exact (EQ_MP (@lem154648 r m n h1 h2 h3) (@lem154644 r m n h3)). Qed.
Lemma lem154650 (r : nat) (m : nat) (n : nat) (h1 : term65 n) (h2 : term84 r m n) : (term67 m n r) = (term90 m n).
Proof. exact (prop_ext (fun h3 : term67 m n r => @lem154649 r m n h3 h1 h2) (fun h3 : term90 m n => @lem154645 r m n h2)). Qed.
Lemma lem154651 (r : nat) (m : nat) (n : nat) (h1 : term65 n) (h2 : term84 r m n) : term90 m n.
Proof. exact (EQ_MP (@lem154650 r m n h1 h2) (@lem154645 r m n h2)). Qed.
Lemma lem154652 (r : nat) (m : nat) (n : nat) (h1 : term65 n) : term245 r m n.
Proof. exact (fun h0 : term84 r m n => @lem154651 r m n h1 h0). Qed.
Lemma lem154653 (r : nat) (m : nat) (n : nat) (h1 : term65 n) (h2 : term84 r m n) : term90 m n.
Proof. exact (@lem154652 r m n h1 (@lem154276 r m n h2)). Qed.
Lemma lem154654 (m : nat) (n : nat) (h1 : term87 m n) (h2 : term65 n) : term90 m n.
Proof. exact (ex_elim (@lem154275 m n h1) (fun r : nat => fun h0 : term86 m n r => @lem154653 r m n h2 h0)). Qed.
Lemma lem154655 (m : nat) (n : nat) (h1 : term65 n) : term145 m n.
Proof. exact (fun h0 : term87 m n => @lem154654 m n h0 h1). Qed.
Lemma lem154656 (m : nat) (n : nat) (h1 : term65 n) : term144 m n.
Proof. exact (EQ_MP (@lem154274 m n) (@lem154655 m n h1)). Qed.
Lemma lem154657 (m : nat) (n : nat) (h1 : term128 m n) (h2 : term65 n) : term90 m n.
Proof. exact (@lem154656 m n h2 (@lem154174 m n h1)). Qed.
Lemma lem154658 (m : nat) (n : nat) (h1 : term65 n) : term132 m n.
Proof. exact (fun h0 : term128 m n => @lem154657 m n h0 h1). Qed.
Lemma lem154659 (m : nat) (n : nat) (h1 : term65 n) : term131 m n.
Proof. exact (EQ_MP (@lem154167 m n) (@lem154658 m n h1)). Qed.
Lemma lem154660 (m : nat) (n : nat) (h1 : term65 n) (h2 : (term69 m n) = (term87 m n)) : term90 m n.
Proof. exact (@lem154659 m n h1 (@lem154052 m n h2)). Qed.
Lemma lem154661 (m : nat) (n : nat) (h1 : term65 n) : term92 m n.
Proof. exact (fun h0 : (term69 m n) = (term87 m n) => @lem154660 m n h1 h0). Qed.
Lemma lem154662 (m : nat) (n : nat) (h1 : term65 n) : term91 m n.
Proof. exact (EQ_MP (@lem154047 m n) (@lem154661 m n h1)). Qed.
Lemma lem154663 (m : nat) (n : nat) (h1 : term65 n) : term90 m n.
Proof. exact (@lem154662 m n h1 (@lem154019 m n)). Qed.
Lemma lem154664 (m : nat) (n : nat) (h1 : term65 n) : (term65 n) = (term90 m n).
Proof. exact (prop_ext (fun h2 : term65 n => @lem154663 m n h1) (fun h2 : term90 m n => @lem154020 n h1)). Qed.
Lemma lem154665 (m : nat) (n : nat) (h1 : term65 n) : term90 m n.
Proof. exact (EQ_MP (@lem154664 m n h1) (@lem154020 n h1)). Qed.
Lemma lem154666 (m : nat) (n : nat) : term246 m n.
Proof. exact (fun h0 : term65 n => @lem154665 m n h0). Qed.
Lemma lem154671 (m : nat) : term247 m.
Proof. exact (fun n : nat => @lem154666 m n). Qed.
Lemma lem154676 : term248.
Proof. exact (fun m : nat => @lem154671 m). Qed.
