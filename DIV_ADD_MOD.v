Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_ADD_MOD_term_abbrevs.
Require Import ADD_AC_spec.
Require Import DIVISION_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EQ_ADD_RCANCEL_spec.
Require Import EQ_MULT_RCANCEL_spec.
Require Import EQ_SYM_EQ_spec.
Require Import REFL_CLAUSE_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm1834_spec.
Require Import thm32_spec.
Require Import thm82_spec.
Lemma lem209996 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem362 A x). Qed.
Lemma lem209997 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem209998 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem209997 A x) (@lem209996 A x)). Qed.
Lemma lem209999 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem209998 A x y). Qed.
Lemma lem210000 {A : Type'} (y : A) (x : A) : (term2 A x y) = ((x = y) = (y = x)).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem210005 (m : nat) (n : nat) (p : nat) (h1 : (term3 m n p) = (term4 m n p)) : (term3 m n p) = (term4 m n p).
Proof. exact (h1). Qed.
Lemma lem210006 (m : nat) (n : nat) (p : nat) (h1 : (term3 m n p) = (term4 m n p)) : (term4 m n p) = (term3 m n p).
Proof. exact (SYM (@lem210005 m n p h1)). Qed.
Lemma lem210007 (m : nat) (n : nat) (p : nat) (h1 : (term4 m n p) = (term3 m n p)) : (term4 m n p) = (term3 m n p).
Proof. exact (h1). Qed.
Lemma lem210008 (m : nat) (n : nat) (p : nat) (h1 : (term4 m n p) = (term3 m n p)) : (term3 m n p) = (term4 m n p).
Proof. exact (SYM (@lem210007 m n p h1)). Qed.
Lemma lem210009 (m : nat) (n : nat) (p : nat) : ((term3 m n p) = (term4 m n p)) = ((term4 m n p) = (term3 m n p)).
Proof. exact (prop_ext (fun h1 : (term3 m n p) = (term4 m n p) => @lem210006 m n p h1) (fun h1 : (term4 m n p) = (term3 m n p) => @lem210008 m n p h1)). Qed.
Lemma lem210010 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (fun_ext (fun p : nat => @lem210009 m n p)). Qed.
Lemma lem210011 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem210012 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem210011) (@lem210010 m n)). Qed.
Lemma lem210013 (m : nat) : (term9 m) = (term10 m).
Proof. exact (fun_ext (fun n : nat => @lem210012 m n)). Qed.
Lemma lem210014 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem210015 (m : nat) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem210014) (@lem210013 m)). Qed.
Lemma lem210016 : term13 = term14.
Proof. exact (fun_ext (fun m : nat => @lem210015 m)). Qed.
Lemma lem210017 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem210018 : term15 = term16.
Proof. exact (MK_COMB (@lem210017) (@lem210016)). Qed.
Lemma lem210019 : term16.
Proof. exact (EQ_MP (@lem210018) (@lem82128)). Qed.
Lemma lem210020 (m : nat) : term17 m.
Proof. exact (@lem210019 m). Qed.
Lemma lem210021 (m : nat) : (term17 m) = (term12 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem210022 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem210021 m) (@lem210020 m)). Qed.
Lemma lem210023 (m : nat) (n : nat) : term18 m n.
Proof. exact (@lem210022 m n). Qed.
Lemma lem210024 (m : nat) (n : nat) : (term18 m n) = (term8 m n).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem210025 (m : nat) (n : nat) : term8 m n.
Proof. exact (EQ_MP (@lem210024 m n) (@lem210023 m n)). Qed.
Lemma lem210026 (m : nat) (n : nat) (p : nat) : term19 m n p.
Proof. exact (@lem210025 m n p). Qed.
Lemma lem210027 (m : nat) (n : nat) (p : nat) : (term19 m n p) = ((term4 m n p) = (term3 m n p)).
Proof. exact (eq_refl (term19 m n p)). Qed.
Lemma lem210029 {A : Type'} (x : A) : term20 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem210030 {A : Type'} (x : A) : (term20 A x) = ((x = x) = True).
Proof. exact (eq_refl (term20 A x)). Qed.
Lemma lem210032 (n : nat) (m : nat) (p : nat) : term21 n m p.
Proof. exact (proj2 (@lem79120 n m p)). Qed.
Lemma lem210039 (m : nat) (n : nat) (p : nat) : (term22 m n p) = (term23 m n p).
Proof. exact (proj1 (@lem210032 n m p)). Qed.
Lemma lem210040 (a : nat) (b : nat) (c : nat) (d : nat) : (term24 a b c d) = (term25 a b c d).
Proof. exact (@lem210039 a b (Nat.add c d)). Qed.
Lemma lem210056 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem210057 (a : nat) (b : nat) (c : nat) (d : nat) : (term26 a b c d) = (term27 a b c d).
Proof. exact (MK_COMB (@lem210056) (@lem210040 a b c d)). Qed.
Lemma lem210059 (m : nat) (n : nat) (p : nat) : (term22 m n p) = (term23 m n p).
Proof. exact (proj1 (@lem210032 n m p)). Qed.
Lemma lem210060 (a : nat) (c : nat) (b : nat) (d : nat) : (term24 a c b d) = (term25 a c b d).
Proof. exact (@lem210059 a c (Nat.add b d)). Qed.
Lemma lem210068 (n : nat) (m : nat) (p : nat) : (term23 m n p) = (term23 n m p).
Proof. exact (proj2 (@lem210032 n m p)). Qed.
Lemma lem210069 (b : nat) (c : nat) (d : nat) : (term23 c b d) = (term23 b c d).
Proof. exact (@lem210068 b c d). Qed.
Lemma lem210079 (a : nat) : (Nat.add a) = (Nat.add a).
Proof. exact (eq_refl (Nat.add a)). Qed.
Lemma lem210080 (a : nat) (b : nat) (c : nat) (d : nat) : (term25 a c b d) = (term25 a b c d).
Proof. exact (MK_COMB (@lem210079 a) (@lem210069 b c d)). Qed.
Lemma lem210087 (a : nat) (b : nat) (c : nat) (d : nat) : (term24 a c b d) = (term25 a b c d).
Proof. exact (TRANS (@lem210060 a c b d) (@lem210080 a b c d)). Qed.
Lemma lem210088 (a : nat) (b : nat) (c : nat) (d : nat) : ((term24 a b c d) = (term24 a c b d)) = ((term25 a b c d) = (term25 a b c d)).
Proof. exact (MK_COMB (@lem210057 a b c d) (@lem210087 a b c d)). Qed.
Lemma lem210090 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem210030 A x) (@lem210029 A x)). Qed.
Lemma lem210091 (x : nat) : (x = x) = True.
Proof. exact (@lem210090 nat x). Qed.
Lemma lem210092 (a : nat) (b : nat) (c : nat) (d : nat) : ((term25 a b c d) = (term25 a b c d)) = True.
Proof. exact (@lem210091 (term25 a b c d)). Qed.
Lemma lem210093 (a : nat) (c : nat) (b : nat) (d : nat) : ((term24 a b c d) = (term24 a c b d)) = True.
Proof. exact (TRANS (@lem210088 a b c d) (@lem210092 a b c d)). Qed.
Lemma lem210094 (a : nat) (c : nat) (b : nat) (d : nat) : True = ((term24 a b c d) = (term24 a c b d)).
Proof. exact (SYM (@lem210093 a c b d)). Qed.
Lemma lem210096 (h1 : term28) : term28.
Proof. exact (h1). Qed.
Lemma lem210097 (m : nat) (h1 : term28) : term29 m.
Proof. exact (@lem210096 h1 m). Qed.
Lemma lem210098 (m : nat) : (term29 m) = (term30 m).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem210099 (m : nat) (h1 : term28) : term30 m.
Proof. exact (EQ_MP (@lem210098 m) (@lem210097 m h1)). Qed.
Lemma lem210100 (m : nat) (n : nat) (h1 : term28) : term31 m n.
Proof. exact (@lem210099 m h1 n). Qed.
Lemma lem210101 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem210102 (m : nat) (n : nat) (h1 : term28) : term32 m n.
Proof. exact (EQ_MP (@lem210101 m n) (@lem210100 m n h1)). Qed.
Lemma lem210103 (n : nat) (h1 : term33 n) : term33 n.
Proof. exact (h1). Qed.
Lemma lem210104 (m : nat) (n : nat) (h1 : term28) (h2 : term33 n) : term34 m n.
Proof. exact (@lem210102 m n h1 (@lem210103 n h2)). Qed.
Lemma lem210105 (n : nat) (h1 : term28) (h2 : term33 n) : term35 n.
Proof. exact (fun m : nat => @lem210104 m n h1 h2). Qed.
Lemma lem210106 (n : nat) (h1 : term28) : term36 n.
Proof. exact (fun h0 : term33 n => @lem210105 n h1 h0). Qed.
Lemma lem210107 (h1 : term28) : term37.
Proof. exact (fun n : nat => @lem210106 n h1). Qed.
Lemma lem210108 : term38.
Proof. exact (fun h0 : term28 => @lem210107 h0). Qed.
Lemma lem210109 : term37.
Proof. exact (@lem210108 (@lem157261)). Qed.
Lemma lem210110 (n : nat) : term39 n.
Proof. exact (@lem210109 n). Qed.
Lemma lem210111 (n : nat) : (term39 n) = (term36 n).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem210113 (n : nat) (h1 : term33 n) : term33 n.
Proof. exact (h1). Qed.
Lemma lem210115 (n : nat) : term36 n.
Proof. exact (EQ_MP (@lem210111 n) (@lem210110 n)). Qed.
Lemma lem210116 (n : nat) (h1 : term33 n) : term35 n.
Proof. exact (@lem210115 n (@lem210113 n h1)). Qed.
Lemma lem210117 (n : nat) (h1 : term35 n) : term35 n.
Proof. exact (h1). Qed.
Lemma lem210118 (a : nat) (b : nat) (n : nat) (h1 : term35 n) : term40 n a b.
Proof. exact (@lem210117 n h1 (Nat.add a b)). Qed.
Lemma lem210119 (a : nat) (b : nat) (n : nat) : (term40 n a b) = (term41 a b n).
Proof. exact (eq_refl (term40 n a b)). Qed.
Lemma lem210120 (a : nat) (b : nat) (n : nat) (h1 : term35 n) : term41 a b n.
Proof. exact (EQ_MP (@lem210119 a b n) (@lem210118 a b n h1)). Qed.
Lemma lem210121 (a : nat) (b : nat) (n : nat) (h1 : term35 n) : (Nat.add a b) = (term42 a b n).
Proof. exact (proj1 (@lem210120 a b n h1)). Qed.
Lemma lem210122 (a : nat) (n : nat) (h1 : term35 n) : term43 n a.
Proof. exact (@lem210117 n h1 a). Qed.
Lemma lem210123 (a : nat) (n : nat) : (term43 n a) = (term34 a n).
Proof. exact (eq_refl (term43 n a)). Qed.
Lemma lem210124 (a : nat) (n : nat) (h1 : term35 n) : term34 a n.
Proof. exact (EQ_MP (@lem210123 a n) (@lem210122 a n h1)). Qed.
Lemma lem210125 (a : nat) (n : nat) (h1 : term35 n) : a = (term44 a n).
Proof. exact (proj1 (@lem210124 a n h1)). Qed.
Lemma lem210126 (b : nat) (n : nat) (h1 : term35 n) : term43 n b.
Proof. exact (@lem210117 n h1 b). Qed.
Lemma lem210127 (b : nat) (n : nat) : (term43 n b) = (term34 b n).
Proof. exact (eq_refl (term43 n b)). Qed.
Lemma lem210128 (b : nat) (n : nat) (h1 : term35 n) : term34 b n.
Proof. exact (EQ_MP (@lem210127 b n) (@lem210126 b n h1)). Qed.
Lemma lem210129 (b : nat) (n : nat) (h1 : term35 n) : b = (term44 b n).
Proof. exact (proj1 (@lem210128 b n h1)). Qed.
Lemma lem210130 (b : nat) (n : nat) (h1 : b = (term44 b n)) : b = (term44 b n).
Proof. exact (h1). Qed.
Lemma lem210131 (a : nat) (n : nat) (h1 : a = (term44 a n)) : a = (term44 a n).
Proof. exact (h1). Qed.
Lemma lem210132 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem210133 (a : nat) (n : nat) (h1 : a = (term44 a n)) : (Nat.add a) = (term45 a n).
Proof. exact (MK_COMB (@lem210132) (@lem210131 a n h1)). Qed.
Lemma lem210134 (a : nat) (b : nat) (n : nat) (h1 : a = (term44 a n)) (h2 : b = (term44 b n)) : (Nat.add a b) = (term46 a b n).
Proof. exact (MK_COMB (@lem210133 a n h1) (@lem210130 b n h2)). Qed.
Lemma lem210137 (a : nat) (b : nat) (n : nat) (h1 : (Nat.add a b) = (term46 a b n)) : (Nat.add a b) = (term46 a b n).
Proof. exact (h1). Qed.
Lemma lem210138 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem210139 (a : nat) (b : nat) (n : nat) (h1 : (Nat.add a b) = (term46 a b n)) : (term47 a b) = (term48 a b n).
Proof. exact (MK_COMB (@lem210138) (@lem210137 a b n h1)). Qed.
Lemma lem210140 (a : nat) (b : nat) (n : nat) : (term42 a b n) = (term42 a b n).
Proof. exact (eq_refl (term42 a b n)). Qed.
Lemma lem210141 (a : nat) (b : nat) (n : nat) (h1 : (Nat.add a b) = (term46 a b n)) : ((Nat.add a b) = (term42 a b n)) = ((term46 a b n) = (term42 a b n)).
Proof. exact (MK_COMB (@lem210139 a b n h1) (@lem210140 a b n)). Qed.
Lemma lem210142 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem210143 (a : nat) (b : nat) (n : nat) (h1 : (Nat.add a b) = (term46 a b n)) : (term49 a b n) = (term50 a b n).
Proof. exact (MK_COMB (@lem210142) (@lem210141 a b n h1)). Qed.
Lemma lem210144 (a : nat) (b : nat) (n : nat) : (((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n))) = (((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n))).
Proof. exact (eq_refl (((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n)))). Qed.
Lemma lem210145 (a : nat) (b : nat) (n : nat) (h1 : (Nat.add a b) = (term46 a b n)) : (term55 a b n) = (term56 a b n).
Proof. exact (MK_COMB (@lem210143 a b n h1) (@lem210144 a b n)). Qed.
Lemma lem210146 (a : nat) (b : nat) (n : nat) (h1 : (Nat.add a b) = (term46 a b n)) : (term56 a b n) = (term55 a b n).
Proof. exact (SYM (@lem210145 a b n h1)). Qed.
Lemma lem210154 (a : nat) (c : nat) (b : nat) (d : nat) : (term24 a b c d) = (term24 a c b d).
Proof. exact (EQ_MP (@lem210094 a c b d) (@lem0)). Qed.
Lemma lem210155 (a : nat) (b : nat) (n : nat) : (term46 a b n) = (term57 a b n).
Proof. exact (@lem210154 (term58 a n) (term58 b n) (Nat.modulo a n) (Nat.modulo b n)). Qed.
Lemma lem210156 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem210157 (a : nat) (b : nat) (n : nat) : (term48 a b n) = (term59 a b n).
Proof. exact (MK_COMB (@lem210156) (@lem210155 a b n)). Qed.
Lemma lem210158 (a : nat) (b : nat) (n : nat) : (term42 a b n) = (term42 a b n).
Proof. exact (eq_refl (term42 a b n)). Qed.
Lemma lem210159 (a : nat) (b : nat) (n : nat) : ((term46 a b n) = (term42 a b n)) = ((term57 a b n) = (term42 a b n)).
Proof. exact (MK_COMB (@lem210157 a b n) (@lem210158 a b n)). Qed.
Lemma lem210160 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem210161 (a : nat) (b : nat) (n : nat) : (term50 a b n) = (term60 a b n).
Proof. exact (MK_COMB (@lem210160) (@lem210159 a b n)). Qed.
Lemma lem210168 (a : nat) (b : nat) (n : nat) : (((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n))) = (((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n))).
Proof. exact (eq_refl (((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n)))). Qed.
Lemma lem210169 (a : nat) (b : nat) (n : nat) : (term56 a b n) = (term61 a b n).
Proof. exact (MK_COMB (@lem210161 a b n) (@lem210168 a b n)). Qed.
Lemma lem210170 (a : nat) (b : nat) (n : nat) : (term61 a b n) = (term56 a b n).
Proof. exact (SYM (@lem210169 a b n)). Qed.
Lemma lem210178 (m : nat) (n : nat) (p : nat) : (term4 m n p) = (term3 m n p).
Proof. exact (EQ_MP (@lem210027 m n p) (@lem210026 m n p)). Qed.
Lemma lem210179 (a : nat) (b : nat) (n : nat) : (term62 a b n) = (term63 a b n).
Proof. exact (@lem210178 (Nat.div a n) (Nat.div b n) n). Qed.
Lemma lem210180 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem210181 (a : nat) (b : nat) (n : nat) : (term64 a b n) = (term65 a b n).
Proof. exact (MK_COMB (@lem210180) (@lem210179 a b n)). Qed.
Lemma lem210182 (a : nat) (b : nat) (n : nat) : (term52 a b n) = (term52 a b n).
Proof. exact (eq_refl (term52 a b n)). Qed.
Lemma lem210183 (a : nat) (b : nat) (n : nat) : (term57 a b n) = (term66 a b n).
Proof. exact (MK_COMB (@lem210181 a b n) (@lem210182 a b n)). Qed.
Lemma lem210184 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem210185 (a : nat) (b : nat) (n : nat) : (term59 a b n) = (term67 a b n).
Proof. exact (MK_COMB (@lem210184) (@lem210183 a b n)). Qed.
Lemma lem210186 (a : nat) (b : nat) (n : nat) : (term42 a b n) = (term42 a b n).
Proof. exact (eq_refl (term42 a b n)). Qed.
Lemma lem210187 (a : nat) (b : nat) (n : nat) : ((term57 a b n) = (term42 a b n)) = ((term66 a b n) = (term42 a b n)).
Proof. exact (MK_COMB (@lem210185 a b n) (@lem210186 a b n)). Qed.
Lemma lem210190 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem210191 (a : nat) (b : nat) (n : nat) : (term60 a b n) = (term68 a b n).
Proof. exact (MK_COMB (@lem210190) (@lem210187 a b n)). Qed.
Lemma lem210198 (a : nat) (b : nat) (n : nat) : (((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n))) = (((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n))).
Proof. exact (eq_refl (((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n)))). Qed.
Lemma lem210199 (a : nat) (b : nat) (n : nat) : (term61 a b n) = (term69 a b n).
Proof. exact (MK_COMB (@lem210191 a b n) (@lem210198 a b n)). Qed.
Lemma lem210204 (a : nat) (b : nat) (n : nat) : (term69 a b n) = (term61 a b n).
Proof. exact (SYM (@lem210199 a b n)). Qed.
Lemma lem210205 (a : nat) (b : nat) (n : nat) (h1 : (term66 a b n) = (term42 a b n)) : (term66 a b n) = (term42 a b n).
Proof. exact (h1). Qed.
Lemma lem210208 (m : nat) : term70 m.
Proof. exact (@lem84913 m). Qed.
Lemma lem210209 (m : nat) : (term70 m) = (term71 m).
Proof. exact (eq_refl (term70 m)). Qed.
Lemma lem210210 (m : nat) : term71 m.
Proof. exact (EQ_MP (@lem210209 m) (@lem210208 m)). Qed.
Lemma lem210211 (m : nat) (n : nat) : term72 m n.
Proof. exact (@lem210210 m n). Qed.
Lemma lem210212 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (eq_refl (term72 m n)). Qed.
Lemma lem210213 (m : nat) (n : nat) : term73 m n.
Proof. exact (EQ_MP (@lem210212 m n) (@lem210211 m n)). Qed.
Lemma lem210214 (m : nat) (n : nat) (p : nat) : term74 m n p.
Proof. exact (@lem210213 m n p). Qed.
Lemma lem210215 (m : nat) (n : nat) (p : nat) : (term74 m n p) = (((Nat.mul m p) = (Nat.mul n p)) = (term75 m n p)).
Proof. exact (eq_refl (term74 m n p)). Qed.
Lemma lem210226 (m : nat) : term76 m.
Proof. exact (@lem79714 m). Qed.
Lemma lem210227 (m : nat) : (term76 m) = (term77 m).
Proof. exact (eq_refl (term76 m)). Qed.
Lemma lem210228 (m : nat) : term77 m.
Proof. exact (EQ_MP (@lem210227 m) (@lem210226 m)). Qed.
Lemma lem210229 (m : nat) (n : nat) : term78 m n.
Proof. exact (@lem210228 m n). Qed.
Lemma lem210230 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (eq_refl (term78 m n)). Qed.
Lemma lem210231 (m : nat) (n : nat) : term79 m n.
Proof. exact (EQ_MP (@lem210230 m n) (@lem210229 m n)). Qed.
Lemma lem210232 (m : nat) (n : nat) (p : nat) : term80 m n p.
Proof. exact (@lem210231 m n p). Qed.
Lemma lem210233 (p : nat) (m : nat) (n : nat) : (term80 m n p) = (((Nat.add m p) = (Nat.add n p)) = (m = n)).
Proof. exact (eq_refl (term80 m n p)). Qed.
Lemma lem210235 (n : nat) : term81 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem210259 (a : nat) (b : nat) (n : nat) (h1 : (term51 a b n) = (term52 a b n)) : (term51 a b n) = (term52 a b n).
Proof. exact (h1). Qed.
Lemma lem210260 (a : nat) (b : nat) (n : nat) : (term82 a b n) = (term82 a b n).
Proof. exact (eq_refl (term82 a b n)). Qed.
Lemma lem210261 (a : nat) (b : nat) (n : nat) (h1 : (term51 a b n) = (term52 a b n)) : (term42 a b n) = (term83 a b n).
Proof. exact (MK_COMB (@lem210260 a b n) (@lem210259 a b n h1)). Qed.
Lemma lem210262 (a : nat) (b : nat) (n : nat) : (term67 a b n) = (term67 a b n).
Proof. exact (eq_refl (term67 a b n)). Qed.
Lemma lem210263 (a : nat) (b : nat) (n : nat) (h1 : (term51 a b n) = (term52 a b n)) : ((term66 a b n) = (term42 a b n)) = ((term66 a b n) = (term83 a b n)).
Proof. exact (MK_COMB (@lem210262 a b n) (@lem210261 a b n h1)). Qed.
Lemma lem210267 (p : nat) (m : nat) (n : nat) : ((Nat.add m p) = (Nat.add n p)) = (m = n).
Proof. exact (EQ_MP (@lem210233 p m n) (@lem210232 m n p)). Qed.
Lemma lem210268 (a : nat) (b : nat) (n : nat) : ((term66 a b n) = (term83 a b n)) = ((term63 a b n) = (term84 a b n)).
Proof. exact (@lem210267 (term52 a b n) (term63 a b n) (term84 a b n)). Qed.
Lemma lem210270 (m : nat) (n : nat) (p : nat) : ((Nat.mul m p) = (Nat.mul n p)) = (term75 m n p).
Proof. exact (EQ_MP (@lem210215 m n p) (@lem210214 m n p)). Qed.
Lemma lem210271 (a : nat) (b : nat) (n : nat) : ((term63 a b n) = (term84 a b n)) = (term85 a b n).
Proof. exact (@lem210270 (term54 a b n) (term53 a b n) n). Qed.
Lemma lem210277 (n : nat) (h1 : term33 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem210235 n (@lem210113 n h1)). Qed.
Lemma lem210278 (a : nat) (b : nat) (n : nat) : (term86 a b n) = (term86 a b n).
Proof. exact (eq_refl (term86 a b n)). Qed.
Lemma lem210279 (a : nat) (b : nat) (n : nat) (h1 : term33 n) : (term85 a b n) = (term87 a b n).
Proof. exact (MK_COMB (@lem210278 a b n) (@lem210277 n h1)). Qed.
Lemma lem210281 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem210282 (a : nat) (b : nat) (n : nat) : (term87 a b n) = ((term54 a b n) = (term53 a b n)).
Proof. exact (@lem210281 ((term54 a b n) = (term53 a b n))). Qed.
Lemma lem210285 (a : nat) (b : nat) (n : nat) (h1 : term33 n) : (term85 a b n) = ((term54 a b n) = (term53 a b n)).
Proof. exact (TRANS (@lem210279 a b n h1) (@lem210282 a b n)). Qed.
Lemma lem210286 (a : nat) (b : nat) (n : nat) (h1 : term33 n) : ((term63 a b n) = (term84 a b n)) = ((term54 a b n) = (term53 a b n)).
Proof. exact (TRANS (@lem210271 a b n) (@lem210285 a b n h1)). Qed.
Lemma lem210287 (a : nat) (b : nat) (n : nat) (h1 : term33 n) : ((term66 a b n) = (term83 a b n)) = ((term54 a b n) = (term53 a b n)).
Proof. exact (TRANS (@lem210268 a b n) (@lem210286 a b n h1)). Qed.
Lemma lem210288 (a : nat) (b : nat) (n : nat) (h1 : term33 n) (h2 : (term51 a b n) = (term52 a b n)) : ((term66 a b n) = (term42 a b n)) = ((term54 a b n) = (term53 a b n)).
Proof. exact (TRANS (@lem210263 a b n h2) (@lem210287 a b n h1)). Qed.
Lemma lem210289 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem210290 (a : nat) (b : nat) (n : nat) (h1 : term33 n) (h2 : (term51 a b n) = (term52 a b n)) : (term68 a b n) = (term88 a b n).
Proof. exact (MK_COMB (@lem210289) (@lem210288 a b n h1 h2)). Qed.
Lemma lem210293 (a : nat) (b : nat) (n : nat) : ((term53 a b n) = (term54 a b n)) = ((term53 a b n) = (term54 a b n)).
Proof. exact (eq_refl ((term53 a b n) = (term54 a b n))). Qed.
Lemma lem210294 (a : nat) (b : nat) (n : nat) (h1 : term33 n) (h2 : (term51 a b n) = (term52 a b n)) : (term89 a b n) = (term90 a b n).
Proof. exact (MK_COMB (@lem210290 a b n h1 h2) (@lem210293 a b n)). Qed.
Lemma lem210299 (a : nat) (b : nat) (n : nat) (h1 : term33 n) (h2 : (term51 a b n) = (term52 a b n)) : (term90 a b n) = (term89 a b n).
Proof. exact (SYM (@lem210294 a b n h1 h2)). Qed.
Lemma lem210309 (m : nat) : term91 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem210310 (m : nat) : (term91 m) = (term92 m).
Proof. exact (eq_refl (term91 m)). Qed.
Lemma lem210311 (m : nat) : term92 m.
Proof. exact (EQ_MP (@lem210310 m) (@lem210309 m)). Qed.
Lemma lem210312 (m : nat) (n : nat) : term93 m n.
Proof. exact (@lem210311 m n). Qed.
Lemma lem210313 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (eq_refl (term93 m n)). Qed.
Lemma lem210314 (m : nat) (n : nat) : term94 m n.
Proof. exact (EQ_MP (@lem210313 m n) (@lem210312 m n)). Qed.
Lemma lem210315 (m : nat) (n : nat) (p : nat) : term95 m n p.
Proof. exact (@lem210314 m n p). Qed.
Lemma lem210316 (m : nat) (n : nat) (p : nat) : (term95 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term95 m n p)). Qed.
Lemma lem210351 (a : nat) (b : nat) (n : nat) (h1 : (term53 a b n) = (term54 a b n)) : (term53 a b n) = (term54 a b n).
Proof. exact (h1). Qed.
Lemma lem210352 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem210353 (a : nat) (b : nat) (n : nat) (h1 : (term53 a b n) = (term54 a b n)) : (term96 a b n) = (term97 a b n).
Proof. exact (MK_COMB (@lem210352) (@lem210351 a b n h1)). Qed.
Lemma lem210354 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem210355 (a : nat) (b : nat) (n : nat) (h1 : (term53 a b n) = (term54 a b n)) : (term84 a b n) = (term63 a b n).
Proof. exact (MK_COMB (@lem210353 a b n h1) (@lem210354 n)). Qed.
Lemma lem210356 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem210357 (a : nat) (b : nat) (n : nat) (h1 : (term53 a b n) = (term54 a b n)) : (term82 a b n) = (term65 a b n).
Proof. exact (MK_COMB (@lem210356) (@lem210355 a b n h1)). Qed.
Lemma lem210358 (a : nat) (b : nat) (n : nat) : (term51 a b n) = (term51 a b n).
Proof. exact (eq_refl (term51 a b n)). Qed.
Lemma lem210359 (a : nat) (b : nat) (n : nat) (h1 : (term53 a b n) = (term54 a b n)) : (term42 a b n) = (term98 a b n).
Proof. exact (MK_COMB (@lem210357 a b n h1) (@lem210358 a b n)). Qed.
Lemma lem210360 (a : nat) (b : nat) (n : nat) : (term67 a b n) = (term67 a b n).
Proof. exact (eq_refl (term67 a b n)). Qed.
Lemma lem210361 (a : nat) (b : nat) (n : nat) (h1 : (term53 a b n) = (term54 a b n)) : ((term66 a b n) = (term42 a b n)) = ((term66 a b n) = (term98 a b n)).
Proof. exact (MK_COMB (@lem210360 a b n) (@lem210359 a b n h1)). Qed.
Lemma lem210363 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem210316 m n p) (@lem210315 m n p)). Qed.
Lemma lem210364 (a : nat) (b : nat) (n : nat) : ((term66 a b n) = (term98 a b n)) = ((term52 a b n) = (term51 a b n)).
Proof. exact (@lem210363 (term63 a b n) (term52 a b n) (term51 a b n)). Qed.
Lemma lem210367 (a : nat) (b : nat) (n : nat) (h1 : (term53 a b n) = (term54 a b n)) : ((term66 a b n) = (term42 a b n)) = ((term52 a b n) = (term51 a b n)).
Proof. exact (TRANS (@lem210361 a b n h1) (@lem210364 a b n)). Qed.
Lemma lem210368 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem210369 (a : nat) (b : nat) (n : nat) (h1 : (term53 a b n) = (term54 a b n)) : (term68 a b n) = (term99 a b n).
Proof. exact (MK_COMB (@lem210368) (@lem210367 a b n h1)). Qed.
Lemma lem210372 (a : nat) (b : nat) (n : nat) : ((term51 a b n) = (term52 a b n)) = ((term51 a b n) = (term52 a b n)).
Proof. exact (eq_refl ((term51 a b n) = (term52 a b n))). Qed.
Lemma lem210373 (a : nat) (b : nat) (n : nat) (h1 : (term53 a b n) = (term54 a b n)) : (term100 a b n) = (term101 a b n).
Proof. exact (MK_COMB (@lem210369 a b n h1) (@lem210372 a b n)). Qed.
Lemma lem210378 (a : nat) (b : nat) (n : nat) (h1 : (term53 a b n) = (term54 a b n)) : (term101 a b n) = (term100 a b n).
Proof. exact (SYM (@lem210373 a b n h1)). Qed.
Lemma lem210392 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem210000 A y x) (@lem209999 A x y)). Qed.
Lemma lem210393 (y : nat) (x : nat) : (x = y) = (y = x).
Proof. exact (@lem210392 nat y x). Qed.
Lemma lem210394 (a : nat) (b : nat) (n : nat) : ((term53 a b n) = (term54 a b n)) = ((term54 a b n) = (term53 a b n)).
Proof. exact (@lem210393 (term54 a b n) (term53 a b n)). Qed.
Lemma lem210401 (a : nat) (b : nat) (n : nat) : (term88 a b n) = (term88 a b n).
Proof. exact (eq_refl (term88 a b n)). Qed.
Lemma lem210402 (a : nat) (b : nat) (n : nat) : (term90 a b n) = (term102 a b n).
Proof. exact (MK_COMB (@lem210401 a b n) (@lem210394 a b n)). Qed.
Lemma lem210406 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem210407 (a : nat) (b : nat) (n : nat) : (term102 a b n) = True.
Proof. exact (@lem210406 ((term54 a b n) = (term53 a b n))). Qed.
Lemma lem210408 (a : nat) (b : nat) (n : nat) : (term90 a b n) = True.
Proof. exact (TRANS (@lem210402 a b n) (@lem210407 a b n)). Qed.
Lemma lem210409 (a : nat) (b : nat) (n : nat) : True = (term90 a b n).
Proof. exact (SYM (@lem210408 a b n)). Qed.
Lemma lem210410 (a : nat) (b : nat) (n : nat) : term90 a b n.
Proof. exact (EQ_MP (@lem210409 a b n) (@lem0)). Qed.
Lemma lem210424 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem210000 A y x) (@lem209999 A x y)). Qed.
Lemma lem210425 (y : nat) (x : nat) : (x = y) = (y = x).
Proof. exact (@lem210424 nat y x). Qed.
Lemma lem210426 (a : nat) (b : nat) (n : nat) : ((term51 a b n) = (term52 a b n)) = ((term52 a b n) = (term51 a b n)).
Proof. exact (@lem210425 (term52 a b n) (term51 a b n)). Qed.
Lemma lem210433 (a : nat) (b : nat) (n : nat) : (term99 a b n) = (term99 a b n).
Proof. exact (eq_refl (term99 a b n)). Qed.
Lemma lem210434 (a : nat) (b : nat) (n : nat) : (term101 a b n) = (term103 a b n).
Proof. exact (MK_COMB (@lem210433 a b n) (@lem210426 a b n)). Qed.
Lemma lem210438 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem210439 (a : nat) (b : nat) (n : nat) : (term103 a b n) = True.
Proof. exact (@lem210438 ((term52 a b n) = (term51 a b n))). Qed.
Lemma lem210440 (a : nat) (b : nat) (n : nat) : (term101 a b n) = True.
Proof. exact (TRANS (@lem210434 a b n) (@lem210439 a b n)). Qed.
Lemma lem210441 (a : nat) (b : nat) (n : nat) : True = (term101 a b n).
Proof. exact (SYM (@lem210440 a b n)). Qed.
Lemma lem210442 (a : nat) (b : nat) (n : nat) : term101 a b n.
Proof. exact (EQ_MP (@lem210441 a b n) (@lem0)). Qed.
Lemma lem210443 (a : nat) (b : nat) (n : nat) (h1 : (term53 a b n) = (term54 a b n)) : term100 a b n.
Proof. exact (EQ_MP (@lem210378 a b n h1) (@lem210442 a b n)). Qed.
Lemma lem210444 (a : nat) (b : nat) (n : nat) (h1 : term33 n) (h2 : (term51 a b n) = (term52 a b n)) : term89 a b n.
Proof. exact (EQ_MP (@lem210299 a b n h1 h2) (@lem210410 a b n)). Qed.
Lemma lem210445 (a : nat) (b : nat) (n : nat) (h1 : (term66 a b n) = (term42 a b n)) (h2 : (term53 a b n) = (term54 a b n)) : (term51 a b n) = (term52 a b n).
Proof. exact (@lem210443 a b n h2 (@lem210205 a b n h1)). Qed.
Lemma lem210446 (a : nat) (b : nat) (n : nat) (h1 : term33 n) (h2 : (term66 a b n) = (term42 a b n)) (h3 : (term51 a b n) = (term52 a b n)) : (term53 a b n) = (term54 a b n).
Proof. exact (@lem210444 a b n h1 h3 (@lem210205 a b n h2)). Qed.
Lemma lem210447 (a : nat) (b : nat) (n : nat) (h1 : (term66 a b n) = (term42 a b n)) : term104 a b n.
Proof. exact (fun h0 : (term53 a b n) = (term54 a b n) => @lem210445 a b n h1 h0). Qed.
Lemma lem210448 (a : nat) (b : nat) (n : nat) (h1 : term33 n) (h2 : (term66 a b n) = (term42 a b n)) : term105 a b n.
Proof. exact (fun h0 : (term51 a b n) = (term52 a b n) => @lem210446 a b n h1 h2 h0). Qed.
Lemma lem210449 (a : nat) (b : nat) (n : nat) (h1 : term33 n) (h2 : (term66 a b n) = (term42 a b n)) : term106 a b n.
Proof. exact (conj (@lem210448 a b n h1 h2) (@lem210447 a b n h2)). Qed.
Lemma lem210450 (a : nat) (b : nat) (n : nat) : (term106 a b n) = (((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n))).
Proof. exact (@lem32 ((term51 a b n) = (term52 a b n)) ((term53 a b n) = (term54 a b n))). Qed.
Lemma lem210451 (a : nat) (b : nat) (n : nat) (h1 : term33 n) (h2 : (term66 a b n) = (term42 a b n)) : ((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n)).
Proof. exact (EQ_MP (@lem210450 a b n) (@lem210449 a b n h1 h2)). Qed.
Lemma lem210452 (a : nat) (b : nat) (n : nat) (h1 : term33 n) : term69 a b n.
Proof. exact (fun h0 : (term66 a b n) = (term42 a b n) => @lem210451 a b n h1 h0). Qed.
Lemma lem210453 (a : nat) (b : nat) (n : nat) (h1 : term33 n) : term61 a b n.
Proof. exact (EQ_MP (@lem210204 a b n) (@lem210452 a b n h1)). Qed.
Lemma lem210454 (a : nat) (b : nat) (n : nat) (h1 : term33 n) : term56 a b n.
Proof. exact (EQ_MP (@lem210170 a b n) (@lem210453 a b n h1)). Qed.
Lemma lem210455 (a : nat) (b : nat) (n : nat) (h1 : term33 n) (h2 : (Nat.add a b) = (term46 a b n)) : term55 a b n.
Proof. exact (EQ_MP (@lem210146 a b n h2) (@lem210454 a b n h1)). Qed.
Lemma lem210456 (a : nat) (b : nat) (n : nat) (h1 : term33 n) : term107 a b n.
Proof. exact (fun h0 : (Nat.add a b) = (term46 a b n) => @lem210455 a b n h1 h0). Qed.
Lemma lem210457 (a : nat) (b : nat) (n : nat) (h1 : term33 n) (h2 : a = (term44 a n)) (h3 : b = (term44 b n)) : term55 a b n.
Proof. exact (@lem210456 a b n h1 (@lem210134 a b n h2 h3)). Qed.
Lemma lem210458 (a : nat) (b : nat) (n : nat) (h1 : term33 n) (h2 : b = (term44 b n)) : term108 a b n.
Proof. exact (fun h0 : a = (term44 a n) => @lem210457 a b n h1 h0 h2). Qed.
Lemma lem210459 (a : nat) (b : nat) (n : nat) (h1 : term33 n) : term109 a b n.
Proof. exact (fun h0 : b = (term44 b n) => @lem210458 a b n h1 h0). Qed.
Lemma lem210460 (a : nat) (b : nat) (n : nat) (h1 : term35 n) (h2 : term33 n) : term108 a b n.
Proof. exact (@lem210459 a b n h2 (@lem210129 b n h1)). Qed.
Lemma lem210461 (a : nat) (b : nat) (n : nat) (h1 : term35 n) (h2 : term33 n) : term55 a b n.
Proof. exact (@lem210460 a b n h1 h2 (@lem210125 a n h1)). Qed.
Lemma lem210462 (a : nat) (b : nat) (n : nat) (h1 : term35 n) (h2 : term33 n) : ((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n)).
Proof. exact (@lem210461 a b n h1 h2 (@lem210121 a b n h1)). Qed.
Lemma lem210463 (a : nat) (b : nat) (n : nat) (h1 : term33 n) : term110 a b n.
Proof. exact (fun h0 : term35 n => @lem210462 a b n h0 h1). Qed.
Lemma lem210464 (a : nat) (b : nat) (n : nat) (h1 : term33 n) : ((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n)).
Proof. exact (@lem210463 a b n h1 (@lem210116 n h1)). Qed.
Lemma lem210465 (a : nat) (b : nat) (n : nat) (h1 : term33 n) : (term33 n) = (((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n))).
Proof. exact (prop_ext (fun h2 : term33 n => @lem210464 a b n h1) (fun h2 : ((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n)) => @lem210113 n h1)). Qed.
Lemma lem210466 (a : nat) (b : nat) (n : nat) (h1 : term33 n) : ((term51 a b n) = (term52 a b n)) = ((term53 a b n) = (term54 a b n)).
Proof. exact (EQ_MP (@lem210465 a b n h1) (@lem210113 n h1)). Qed.
Lemma lem210467 (a : nat) (b : nat) (n : nat) : term111 a b n.
Proof. exact (fun h0 : term33 n => @lem210466 a b n h0). Qed.
Lemma lem210472 (a : nat) (b : nat) : term112 a b.
Proof. exact (fun n : nat => @lem210467 a b n). Qed.
Lemma lem210477 (a : nat) : term113 a.
Proof. exact (fun b : nat => @lem210472 a b). Qed.
Lemma lem210482 : term114.
Proof. exact (fun a : nat => @lem210477 a). Qed.
