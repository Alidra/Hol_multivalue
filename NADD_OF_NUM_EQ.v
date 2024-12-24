Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_OF_NUM_EQ_term_abbrevs.
Require Import BOUNDS_LINEAR_0_spec.
Require Import DIST_EQ_0_spec.
Require Import DIST_RMUL_spec.
Require Import NADD_OF_NUM_spec.
Require Import NADD_OF_NUM_WELLDEF_spec.
Require Import nadd_eq_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1823_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Lemma lem1269008 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem1269009 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem1269008 m n p h1)). Qed.
Lemma lem1269010 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem1269011 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem1269010 m n p h1)). Qed.
Lemma lem1269012 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem1269009 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem1269011 m n p h1)). Qed.
Lemma lem1269013 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem1269012 m n p)). Qed.
Lemma lem1269014 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1269015 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem1269014) (@lem1269013 m n)). Qed.
Lemma lem1269016 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem1269015 m n)). Qed.
Lemma lem1269017 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1269018 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem1269017) (@lem1269016 m)). Qed.
Lemma lem1269019 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem1269018 m)). Qed.
Lemma lem1269020 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1269021 : term12 = term13.
Proof. exact (MK_COMB (@lem1269020) (@lem1269019)). Qed.
Lemma lem1269022 : term13.
Proof. exact (EQ_MP (@lem1269021) (@lem1245482)). Qed.
Lemma lem1269023 (m : nat) : term14 m.
Proof. exact (@lem1245573 m). Qed.
Lemma lem1269024 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1269025 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem1269024 m) (@lem1269023 m)). Qed.
Lemma lem1269026 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem1269025 m n). Qed.
Lemma lem1269027 (m : nat) (n : nat) : (term16 m n) = (((term17 m n) = (NUMERAL 0)) = (m = n)).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1269029 (A : nat) : term18 A.
Proof. exact (@lem1260600 A). Qed.
Lemma lem1269030 (A : nat) : (term18 A) = (term19 A).
Proof. exact (eq_refl (term18 A)). Qed.
Lemma lem1269031 (A : nat) : term19 A.
Proof. exact (EQ_MP (@lem1269030 A) (@lem1269029 A)). Qed.
Lemma lem1269032 (A : nat) (B : nat) : term20 A B.
Proof. exact (@lem1269031 A B). Qed.
Lemma lem1269033 (B : nat) (A : nat) : (term20 A B) = ((term21 A B) = (A = (NUMERAL 0))).
Proof. exact (eq_refl (term20 A B)). Qed.
Lemma lem1269035 (m : nat) : term22 m.
Proof. exact (@lem1269022 m). Qed.
Lemma lem1269036 (m : nat) : (term22 m) = (term9 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem1269037 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1269036 m) (@lem1269035 m)). Qed.
Lemma lem1269038 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1269037 m n). Qed.
Lemma lem1269039 (m : nat) (n : nat) : (term23 m n) = (term5 m n).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1269040 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem1269039 m n) (@lem1269038 m n)). Qed.
Lemma lem1269041 (m : nat) (n : nat) (p : nat) : term24 m n p.
Proof. exact (@lem1269040 m n p). Qed.
Lemma lem1269042 (m : nat) (n : nat) (p : nat) : (term24 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term24 m n p)). Qed.
Lemma lem1269044 (k : nat) : term25 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1269045 (k : nat) : (term25 k) = ((term26 k) = (term27 k)).
Proof. exact (eq_refl (term25 k)). Qed.
Lemma lem1269047 (x : nadd) : term28 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1269048 (x : nadd) : (term28 x) = (term29 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1269049 (x : nadd) : term29 x.
Proof. exact (EQ_MP (@lem1269048 x) (@lem1269047 x)). Qed.
Lemma lem1269050 (x : nadd) (y : nadd) : term30 x y.
Proof. exact (@lem1269049 x y). Qed.
Lemma lem1269051 (x : nadd) (y : nadd) : (term30 x y) = ((nadd_eq x y) = (term31 x y)).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem1269053 (m : nat) : term32 m.
Proof. exact (@lem1269004 m). Qed.
Lemma lem1269054 (m : nat) : (term32 m) = (term33 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem1269055 (m : nat) : term33 m.
Proof. exact (EQ_MP (@lem1269054 m) (@lem1269053 m)). Qed.
Lemma lem1269056 (m : nat) (n : nat) : term34 m n.
Proof. exact (@lem1269055 m n). Qed.
Lemma lem1269057 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem1269058 (m : nat) (n : nat) : term35 m n.
Proof. exact (EQ_MP (@lem1269057 m n) (@lem1269056 m n)). Qed.
Lemma lem1269059 (m : nat) (n : nat) : (term35 m n) = ((term35 m n) = True).
Proof. exact (@lem7 (term35 m n)). Qed.
Lemma lem1269068 (m : nat) (n : nat) : (term35 m n) = True.
Proof. exact (EQ_MP (@lem1269059 m n) (@lem1269058 m n)). Qed.
Lemma lem1269069 (m : nat) (n : nat) : True = (term35 m n).
Proof. exact (SYM (@lem1269068 m n)). Qed.
Lemma lem1269070 (m : nat) (n : nat) : term35 m n.
Proof. exact (EQ_MP (@lem1269069 m n) (@lem0)). Qed.
Lemma lem1269074 (x : nadd) (y : nadd) : (nadd_eq x y) = (term31 x y).
Proof. exact (EQ_MP (@lem1269051 x y) (@lem1269050 x y)). Qed.
Lemma lem1269075 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (@lem1269074 (nadd_of_num m) (nadd_of_num n)). Qed.
Lemma lem1269085 (k : nat) : (term26 k) = (term27 k).
Proof. exact (EQ_MP (@lem1269045 k) (@lem1269044 k)). Qed.
Lemma lem1269086 (m : nat) : (term26 m) = (term27 m).
Proof. exact (@lem1269085 m). Qed.
Lemma lem1269087 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1269088 (m : nat) (n' : nat) : (term38 m n') = (term39 m n').
Proof. exact (MK_COMB (@lem1269086 m) (@lem1269087 n')). Qed.
Lemma lem1269090 {A B : Type'} (f : A -> B) (y : A) : (term40 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1269091 (f : nat -> nat) (y : nat) : (term41 f y) = (f y).
Proof. exact (@lem1269090 nat nat f y). Qed.
Lemma lem1269092 (m : nat) (n' : nat) : (term42 m n') = (term39 m n').
Proof. exact (@lem1269091 (term27 m) n'). Qed.
Lemma lem1269093 (m : nat) (n : nat) : (term39 m n) = (Nat.mul m n).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem1269094 (m : nat) : (term43 m) = (term27 m).
Proof. exact (fun_ext (fun n : nat => @lem1269093 m n)). Qed.
Lemma lem1269095 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1269096 (m : nat) (n' : nat) : (term42 m n') = (term39 m n').
Proof. exact (MK_COMB (@lem1269094 m) (@lem1269095 n')). Qed.
Lemma lem1269097 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1269098 (m : nat) (n' : nat) : (term44 m n') = (term45 m n').
Proof. exact (MK_COMB (@lem1269097) (@lem1269096 m n')). Qed.
Lemma lem1269099 (m : nat) (n' : nat) : (term39 m n') = (Nat.mul m n').
Proof. exact (eq_refl (term39 m n')). Qed.
Lemma lem1269100 (m : nat) (n' : nat) : ((term42 m n') = (term39 m n')) = ((term39 m n') = (Nat.mul m n')).
Proof. exact (MK_COMB (@lem1269098 m n') (@lem1269099 m n')). Qed.
Lemma lem1269101 (m : nat) (n' : nat) : (term39 m n') = (Nat.mul m n').
Proof. exact (EQ_MP (@lem1269100 m n') (@lem1269092 m n')). Qed.
Lemma lem1269102 (m : nat) (n' : nat) : (term38 m n') = (Nat.mul m n').
Proof. exact (TRANS (@lem1269088 m n') (@lem1269101 m n')). Qed.
Lemma lem1269103 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1269104 (m : nat) (n' : nat) : (term46 m n') = (term47 m n').
Proof. exact (MK_COMB (@lem1269103) (@lem1269102 m n')). Qed.
Lemma lem1269106 (k : nat) : (term26 k) = (term27 k).
Proof. exact (EQ_MP (@lem1269045 k) (@lem1269044 k)). Qed.
Lemma lem1269107 (n : nat) : (term26 n) = (term27 n).
Proof. exact (@lem1269106 n). Qed.
Lemma lem1269108 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1269109 (n : nat) (n' : nat) : (term38 n n') = (term39 n n').
Proof. exact (MK_COMB (@lem1269107 n) (@lem1269108 n')). Qed.
Lemma lem1269111 {A B : Type'} (f : A -> B) (y : A) : (term40 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1269112 (f : nat -> nat) (y : nat) : (term41 f y) = (f y).
Proof. exact (@lem1269111 nat nat f y). Qed.
Lemma lem1269113 (n : nat) (n' : nat) : (term42 n n') = (term39 n n').
Proof. exact (@lem1269112 (term27 n) n'). Qed.
Lemma lem1269114 (n : nat) (n' : nat) : (term39 n n') = (Nat.mul n n').
Proof. exact (eq_refl (term39 n n')). Qed.
Lemma lem1269115 (n : nat) : (term43 n) = (term27 n).
Proof. exact (fun_ext (fun n' : nat => @lem1269114 n n')). Qed.
Lemma lem1269116 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1269117 (n : nat) (n' : nat) : (term42 n n') = (term39 n n').
Proof. exact (MK_COMB (@lem1269115 n) (@lem1269116 n')). Qed.
Lemma lem1269118 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1269119 (n : nat) (n' : nat) : (term44 n n') = (term45 n n').
Proof. exact (MK_COMB (@lem1269118) (@lem1269117 n n')). Qed.
Lemma lem1269120 (n : nat) (n' : nat) : (term39 n n') = (Nat.mul n n').
Proof. exact (eq_refl (term39 n n')). Qed.
Lemma lem1269121 (n : nat) (n' : nat) : ((term42 n n') = (term39 n n')) = ((term39 n n') = (Nat.mul n n')).
Proof. exact (MK_COMB (@lem1269119 n n') (@lem1269120 n n')). Qed.
Lemma lem1269122 (n : nat) (n' : nat) : (term39 n n') = (Nat.mul n n').
Proof. exact (EQ_MP (@lem1269121 n n') (@lem1269113 n n')). Qed.
Lemma lem1269123 (n : nat) (n' : nat) : (term38 n n') = (Nat.mul n n').
Proof. exact (TRANS (@lem1269109 n n') (@lem1269122 n n')). Qed.
Lemma lem1269124 (m : nat) (n : nat) (n' : nat) : (term48 m n n') = (term49 m n n').
Proof. exact (MK_COMB (@lem1269104 m n') (@lem1269123 n n')). Qed.
Lemma lem1269125 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1269126 (m : nat) (n : nat) (n' : nat) : (term50 m n n') = (term1 m n n').
Proof. exact (MK_COMB (@lem1269125) (@lem1269124 m n n')). Qed.
Lemma lem1269127 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1269128 (m : nat) (n : nat) (n' : nat) : (term51 m n n') = (term52 m n n').
Proof. exact (MK_COMB (@lem1269127) (@lem1269126 m n n')). Qed.
Lemma lem1269129 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1269130 (m : nat) (n : nat) (n' : nat) (B : nat) : (term53 m n n' B) = (term54 m n n' B).
Proof. exact (MK_COMB (@lem1269128 m n n') (@lem1269129 B)). Qed.
Lemma lem1269131 (m : nat) (n : nat) (B : nat) : (term55 m n B) = (term56 m n B).
Proof. exact (fun_ext (fun n' : nat => @lem1269130 m n n' B)). Qed.
Lemma lem1269132 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1269133 (m : nat) (n : nat) (B : nat) : (term57 m n B) = (term58 m n B).
Proof. exact (MK_COMB (@lem1269132) (@lem1269131 m n B)). Qed.
Lemma lem1269138 (m : nat) (n : nat) : (term59 m n) = (term60 m n).
Proof. exact (fun_ext (fun B : nat => @lem1269133 m n B)). Qed.
Lemma lem1269139 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1269140 (m : nat) (n : nat) : (term37 m n) = (term61 m n).
Proof. exact (MK_COMB (@lem1269139) (@lem1269138 m n)). Qed.
Lemma lem1269145 (m : nat) (n : nat) : (term36 m n) = (term61 m n).
Proof. exact (TRANS (@lem1269075 m n) (@lem1269140 m n)). Qed.
Lemma lem1269146 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1269147 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (MK_COMB (@lem1269146) (@lem1269145 m n)). Qed.
Lemma lem1269150 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem1269151 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (MK_COMB (@lem1269147 m n) (@lem1269150 m n)). Qed.
Lemma lem1269154 (m : nat) (n : nat) : (term65 m n) = (term64 m n).
Proof. exact (SYM (@lem1269151 m n)). Qed.
Lemma lem1269166 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem1269042 m n p) (@lem1269041 m n p)). Qed.
Lemma lem1269167 (m : nat) (n : nat) (n' : nat) : (term1 m n n') = (term0 m n n').
Proof. exact (@lem1269166 m n n'). Qed.
Lemma lem1269168 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1269169 (m : nat) (n : nat) (n' : nat) : (term52 m n n') = (term66 m n n').
Proof. exact (MK_COMB (@lem1269168) (@lem1269167 m n n')). Qed.
Lemma lem1269170 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1269171 (m : nat) (n : nat) (n' : nat) (B : nat) : (term54 m n n' B) = (term67 m n n' B).
Proof. exact (MK_COMB (@lem1269169 m n n') (@lem1269170 B)). Qed.
Lemma lem1269172 (m : nat) (n : nat) (B : nat) : (term56 m n B) = (term68 m n B).
Proof. exact (fun_ext (fun n' : nat => @lem1269171 m n n' B)). Qed.
Lemma lem1269173 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1269174 (m : nat) (n : nat) (B : nat) : (term58 m n B) = (term69 m n B).
Proof. exact (MK_COMB (@lem1269173) (@lem1269172 m n B)). Qed.
Lemma lem1269176 (B : nat) (A : nat) : (term21 A B) = (A = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1269033 B A) (@lem1269032 A B)). Qed.
Lemma lem1269177 (B : nat) (m : nat) (n : nat) : (term69 m n B) = ((term17 m n) = (NUMERAL 0)).
Proof. exact (@lem1269176 B (term17 m n)). Qed.
Lemma lem1269179 (m : nat) (n : nat) : ((term17 m n) = (NUMERAL 0)) = (m = n).
Proof. exact (EQ_MP (@lem1269027 m n) (@lem1269026 m n)). Qed.
Lemma lem1269182 (B : nat) (m : nat) (n : nat) : (term69 m n B) = (m = n).
Proof. exact (TRANS (@lem1269177 B m n) (@lem1269179 m n)). Qed.
Lemma lem1269183 (B : nat) (m : nat) (n : nat) : (term58 m n B) = (m = n).
Proof. exact (TRANS (@lem1269174 m n B) (@lem1269182 B m n)). Qed.
Lemma lem1269184 (m : nat) (n : nat) : (term60 m n) = (term70 m n).
Proof. exact (fun_ext (fun B : nat => @lem1269183 B m n)). Qed.
Lemma lem1269185 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1269186 (m : nat) (n : nat) : (term61 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem1269185) (@lem1269184 m n)). Qed.
Lemma lem1269188 {A : Type'} (t : Prop) : (term72 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1269189 (t : Prop) : (term73 t) = t.
Proof. exact (@lem1269188 nat t). Qed.
Lemma lem1269190 (m : nat) (n : nat) : (term71 m n) = (m = n).
Proof. exact (@lem1269189 (m = n)). Qed.
Lemma lem1269193 (m : nat) (n : nat) : (term61 m n) = (m = n).
Proof. exact (TRANS (@lem1269186 m n) (@lem1269190 m n)). Qed.
Lemma lem1269194 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1269195 (m : nat) (n : nat) : (term63 m n) = (term74 m n).
Proof. exact (MK_COMB (@lem1269194) (@lem1269193 m n)). Qed.
Lemma lem1269198 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem1269199 (m : nat) (n : nat) : (term65 m n) = (term75 m n).
Proof. exact (MK_COMB (@lem1269195 m n) (@lem1269198 m n)). Qed.
Lemma lem1269203 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1269204 (m : nat) (n : nat) : (term75 m n) = True.
Proof. exact (@lem1269203 (m = n)). Qed.
Lemma lem1269205 (m : nat) (n : nat) : (term65 m n) = True.
Proof. exact (TRANS (@lem1269199 m n) (@lem1269204 m n)). Qed.
Lemma lem1269206 (m : nat) (n : nat) : True = (term65 m n).
Proof. exact (SYM (@lem1269205 m n)). Qed.
Lemma lem1269207 (m : nat) (n : nat) : term65 m n.
Proof. exact (EQ_MP (@lem1269206 m n) (@lem0)). Qed.
Lemma lem1269209 (m : nat) (n : nat) : term64 m n.
Proof. exact (EQ_MP (@lem1269154 m n) (@lem1269207 m n)). Qed.
Lemma lem1269210 (m : nat) (n : nat) : term76 m n.
Proof. exact (conj (@lem1269209 m n) (@lem1269070 m n)). Qed.
Lemma lem1269211 (m : nat) (n : nat) : (term76 m n) = ((term36 m n) = (m = n)).
Proof. exact (@lem32 (term36 m n) (m = n)). Qed.
Lemma lem1269212 (m : nat) (n : nat) : (term36 m n) = (m = n).
Proof. exact (EQ_MP (@lem1269211 m n) (@lem1269210 m n)). Qed.
Lemma lem1269217 (m : nat) : term77 m.
Proof. exact (fun n : nat => @lem1269212 m n). Qed.
Lemma lem1269222 : term78.
Proof. exact (fun m : nat => @lem1269217 m). Qed.
