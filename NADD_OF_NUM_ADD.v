Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_OF_NUM_ADD_term_abbrevs.
Require Import DIST_REFL_spec.
Require Import LE_0_spec.
Require Import NADD_ADD_spec.
Require Import NADD_OF_NUM_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import nadd_eq_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1276038 (n : nat) : term0 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1276039 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1276040 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1276039 n) (@lem1276038 n)). Qed.
Lemma lem1276041 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem1276043 (n : nat) : term2 n.
Proof. exact (@lem1244783 n). Qed.
Lemma lem1276044 (n : nat) : (term2 n) = ((term3 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem1276046 (m : nat) : term4 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1276047 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1276048 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1276047 m) (@lem1276046 m)). Qed.
Lemma lem1276049 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1276048 m n). Qed.
Lemma lem1276050 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1276051 (m : nat) (n : nat) : term7 m n.
Proof. exact (EQ_MP (@lem1276050 m n) (@lem1276049 m n)). Qed.
Lemma lem1276052 (m : nat) (n : nat) (p : nat) : term8 m n p.
Proof. exact (@lem1276051 m n p). Qed.
Lemma lem1276053 (m : nat) (n : nat) (p : nat) : (term8 m n p) = ((term9 m n p) = (term10 m n p)).
Proof. exact (eq_refl (term8 m n p)). Qed.
Lemma lem1276055 (x : nadd) : term11 x.
Proof. exact (@lem1274104 x). Qed.
Lemma lem1276056 (x : nadd) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1276057 (x : nadd) : term12 x.
Proof. exact (EQ_MP (@lem1276056 x) (@lem1276055 x)). Qed.
Lemma lem1276058 (x : nadd) (y : nadd) : term13 x y.
Proof. exact (@lem1276057 x y). Qed.
Lemma lem1276059 (x : nadd) (y : nadd) : (term13 x y) = ((term14 x y) = (term15 x y)).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1276061 (k : nat) : term16 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1276062 (k : nat) : (term16 k) = ((term17 k) = (term18 k)).
Proof. exact (eq_refl (term16 k)). Qed.
Lemma lem1276064 (x : nadd) : term19 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1276065 (x : nadd) : (term19 x) = (term20 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1276066 (x : nadd) : term20 x.
Proof. exact (EQ_MP (@lem1276065 x) (@lem1276064 x)). Qed.
Lemma lem1276067 (x : nadd) (y : nadd) : term21 x y.
Proof. exact (@lem1276066 x y). Qed.
Lemma lem1276068 (x : nadd) (y : nadd) : (term21 x y) = ((nadd_eq x y) = (term22 x y)).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1276079 (x : nadd) (y : nadd) : (nadd_eq x y) = (term22 x y).
Proof. exact (EQ_MP (@lem1276068 x y) (@lem1276067 x y)). Qed.
Lemma lem1276080 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (@lem1276079 (term25 m n) (term26 m n)). Qed.
Lemma lem1276090 (x : nadd) (y : nadd) : (term14 x y) = (term15 x y).
Proof. exact (EQ_MP (@lem1276059 x y) (@lem1276058 x y)). Qed.
Lemma lem1276091 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (@lem1276090 (nadd_of_num m) (nadd_of_num n)). Qed.
Lemma lem1276093 (k : nat) : (term17 k) = (term18 k).
Proof. exact (EQ_MP (@lem1276062 k) (@lem1276061 k)). Qed.
Lemma lem1276094 (m : nat) : (term17 m) = (term18 m).
Proof. exact (@lem1276093 m). Qed.
Lemma lem1276095 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1276096 (m : nat) (n' : nat) : (term29 m n') = (term30 m n').
Proof. exact (MK_COMB (@lem1276094 m) (@lem1276095 n')). Qed.
Lemma lem1276098 {A B : Type'} (f : A -> B) (y : A) : (term31 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1276099 (f : nat -> nat) (y : nat) : (term32 f y) = (f y).
Proof. exact (@lem1276098 nat nat f y). Qed.
Lemma lem1276100 (m : nat) (n' : nat) : (term33 m n') = (term30 m n').
Proof. exact (@lem1276099 (term18 m) n'). Qed.
Lemma lem1276101 (m : nat) (n : nat) : (term30 m n) = (Nat.mul m n).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem1276102 (m : nat) : (term34 m) = (term18 m).
Proof. exact (fun_ext (fun n : nat => @lem1276101 m n)). Qed.
Lemma lem1276103 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1276104 (m : nat) (n' : nat) : (term33 m n') = (term30 m n').
Proof. exact (MK_COMB (@lem1276102 m) (@lem1276103 n')). Qed.
Lemma lem1276105 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1276106 (m : nat) (n' : nat) : (term35 m n') = (term36 m n').
Proof. exact (MK_COMB (@lem1276105) (@lem1276104 m n')). Qed.
Lemma lem1276107 (m : nat) (n' : nat) : (term30 m n') = (Nat.mul m n').
Proof. exact (eq_refl (term30 m n')). Qed.
Lemma lem1276108 (m : nat) (n' : nat) : ((term33 m n') = (term30 m n')) = ((term30 m n') = (Nat.mul m n')).
Proof. exact (MK_COMB (@lem1276106 m n') (@lem1276107 m n')). Qed.
Lemma lem1276109 (m : nat) (n' : nat) : (term30 m n') = (Nat.mul m n').
Proof. exact (EQ_MP (@lem1276108 m n') (@lem1276100 m n')). Qed.
Lemma lem1276110 (m : nat) (n' : nat) : (term29 m n') = (Nat.mul m n').
Proof. exact (TRANS (@lem1276096 m n') (@lem1276109 m n')). Qed.
Lemma lem1276111 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1276112 (m : nat) (n' : nat) : (term37 m n') = (term38 m n').
Proof. exact (MK_COMB (@lem1276111) (@lem1276110 m n')). Qed.
Lemma lem1276114 (k : nat) : (term17 k) = (term18 k).
Proof. exact (EQ_MP (@lem1276062 k) (@lem1276061 k)). Qed.
Lemma lem1276115 (n : nat) : (term17 n) = (term18 n).
Proof. exact (@lem1276114 n). Qed.
Lemma lem1276116 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1276117 (n : nat) (n' : nat) : (term29 n n') = (term30 n n').
Proof. exact (MK_COMB (@lem1276115 n) (@lem1276116 n')). Qed.
Lemma lem1276119 {A B : Type'} (f : A -> B) (y : A) : (term31 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1276120 (f : nat -> nat) (y : nat) : (term32 f y) = (f y).
Proof. exact (@lem1276119 nat nat f y). Qed.
Lemma lem1276121 (n : nat) (n' : nat) : (term33 n n') = (term30 n n').
Proof. exact (@lem1276120 (term18 n) n'). Qed.
Lemma lem1276122 (n : nat) (n' : nat) : (term30 n n') = (Nat.mul n n').
Proof. exact (eq_refl (term30 n n')). Qed.
Lemma lem1276123 (n : nat) : (term34 n) = (term18 n).
Proof. exact (fun_ext (fun n' : nat => @lem1276122 n n')). Qed.
Lemma lem1276124 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1276125 (n : nat) (n' : nat) : (term33 n n') = (term30 n n').
Proof. exact (MK_COMB (@lem1276123 n) (@lem1276124 n')). Qed.
Lemma lem1276126 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1276127 (n : nat) (n' : nat) : (term35 n n') = (term36 n n').
Proof. exact (MK_COMB (@lem1276126) (@lem1276125 n n')). Qed.
Lemma lem1276128 (n : nat) (n' : nat) : (term30 n n') = (Nat.mul n n').
Proof. exact (eq_refl (term30 n n')). Qed.
Lemma lem1276129 (n : nat) (n' : nat) : ((term33 n n') = (term30 n n')) = ((term30 n n') = (Nat.mul n n')).
Proof. exact (MK_COMB (@lem1276127 n n') (@lem1276128 n n')). Qed.
Lemma lem1276130 (n : nat) (n' : nat) : (term30 n n') = (Nat.mul n n').
Proof. exact (EQ_MP (@lem1276129 n n') (@lem1276121 n n')). Qed.
Lemma lem1276131 (n : nat) (n' : nat) : (term29 n n') = (Nat.mul n n').
Proof. exact (TRANS (@lem1276117 n n') (@lem1276130 n n')). Qed.
Lemma lem1276132 (m : nat) (n : nat) (n' : nat) : (term39 m n n') = (term10 m n n').
Proof. exact (MK_COMB (@lem1276112 m n') (@lem1276131 n n')). Qed.
Lemma lem1276133 (m : nat) (n : nat) : (term28 m n) = (term40 m n).
Proof. exact (fun_ext (fun n' : nat => @lem1276132 m n n')). Qed.
Lemma lem1276134 (m : nat) (n : nat) : (term27 m n) = (term40 m n).
Proof. exact (TRANS (@lem1276091 m n) (@lem1276133 m n)). Qed.
Lemma lem1276135 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1276136 (m : nat) (n : nat) (n' : nat) : (term41 m n n') = (term42 m n n').
Proof. exact (MK_COMB (@lem1276134 m n) (@lem1276135 n')). Qed.
Lemma lem1276138 {A B : Type'} (f : A -> B) (y : A) : (term31 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1276139 (f : nat -> nat) (y : nat) : (term32 f y) = (f y).
Proof. exact (@lem1276138 nat nat f y). Qed.
Lemma lem1276140 (m : nat) (n : nat) (n' : nat) : (term43 m n n') = (term42 m n n').
Proof. exact (@lem1276139 (term40 m n) n'). Qed.
Lemma lem1276141 (m : nat) (n : nat) (n' : nat) : (term42 m n n') = (term10 m n n').
Proof. exact (eq_refl (term42 m n n')). Qed.
Lemma lem1276142 (m : nat) (n : nat) : (term44 m n) = (term40 m n).
Proof. exact (fun_ext (fun n' : nat => @lem1276141 m n n')). Qed.
Lemma lem1276143 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1276144 (m : nat) (n : nat) (n' : nat) : (term43 m n n') = (term42 m n n').
Proof. exact (MK_COMB (@lem1276142 m n) (@lem1276143 n')). Qed.
Lemma lem1276145 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1276146 (m : nat) (n : nat) (n' : nat) : (term45 m n n') = (term46 m n n').
Proof. exact (MK_COMB (@lem1276145) (@lem1276144 m n n')). Qed.
Lemma lem1276147 (m : nat) (n : nat) (n' : nat) : (term42 m n n') = (term10 m n n').
Proof. exact (eq_refl (term42 m n n')). Qed.
Lemma lem1276148 (m : nat) (n : nat) (n' : nat) : ((term43 m n n') = (term42 m n n')) = ((term42 m n n') = (term10 m n n')).
Proof. exact (MK_COMB (@lem1276146 m n n') (@lem1276147 m n n')). Qed.
Lemma lem1276149 (m : nat) (n : nat) (n' : nat) : (term42 m n n') = (term10 m n n').
Proof. exact (EQ_MP (@lem1276148 m n n') (@lem1276140 m n n')). Qed.
Lemma lem1276150 (m : nat) (n : nat) (n' : nat) : (term41 m n n') = (term10 m n n').
Proof. exact (TRANS (@lem1276136 m n n') (@lem1276149 m n n')). Qed.
Lemma lem1276151 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1276152 (m : nat) (n : nat) (n' : nat) : (term47 m n n') = (term48 m n n').
Proof. exact (MK_COMB (@lem1276151) (@lem1276150 m n n')). Qed.
Lemma lem1276154 (k : nat) : (term17 k) = (term18 k).
Proof. exact (EQ_MP (@lem1276062 k) (@lem1276061 k)). Qed.
Lemma lem1276155 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (@lem1276154 (Nat.add m n)). Qed.
Lemma lem1276156 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1276157 (m : nat) (n : nat) (n' : nat) : (term51 m n n') = (term52 m n n').
Proof. exact (MK_COMB (@lem1276155 m n) (@lem1276156 n')). Qed.
Lemma lem1276159 {A B : Type'} (f : A -> B) (y : A) : (term31 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1276160 (f : nat -> nat) (y : nat) : (term32 f y) = (f y).
Proof. exact (@lem1276159 nat nat f y). Qed.
Lemma lem1276161 (m : nat) (n : nat) (n' : nat) : (term53 m n n') = (term52 m n n').
Proof. exact (@lem1276160 (term50 m n) n'). Qed.
Lemma lem1276162 (m : nat) (n : nat) (n' : nat) : (term52 m n n') = (term9 m n n').
Proof. exact (eq_refl (term52 m n n')). Qed.
Lemma lem1276163 (m : nat) (n : nat) : (term54 m n) = (term50 m n).
Proof. exact (fun_ext (fun n' : nat => @lem1276162 m n n')). Qed.
Lemma lem1276164 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1276165 (m : nat) (n : nat) (n' : nat) : (term53 m n n') = (term52 m n n').
Proof. exact (MK_COMB (@lem1276163 m n) (@lem1276164 n')). Qed.
Lemma lem1276166 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1276167 (m : nat) (n : nat) (n' : nat) : (term55 m n n') = (term56 m n n').
Proof. exact (MK_COMB (@lem1276166) (@lem1276165 m n n')). Qed.
Lemma lem1276168 (m : nat) (n : nat) (n' : nat) : (term52 m n n') = (term9 m n n').
Proof. exact (eq_refl (term52 m n n')). Qed.
Lemma lem1276169 (m : nat) (n : nat) (n' : nat) : ((term53 m n n') = (term52 m n n')) = ((term52 m n n') = (term9 m n n')).
Proof. exact (MK_COMB (@lem1276167 m n n') (@lem1276168 m n n')). Qed.
Lemma lem1276170 (m : nat) (n : nat) (n' : nat) : (term52 m n n') = (term9 m n n').
Proof. exact (EQ_MP (@lem1276169 m n n') (@lem1276161 m n n')). Qed.
Lemma lem1276171 (m : nat) (n : nat) (n' : nat) : (term51 m n n') = (term9 m n n').
Proof. exact (TRANS (@lem1276157 m n n') (@lem1276170 m n n')). Qed.
Lemma lem1276172 (m : nat) (n : nat) (n' : nat) : (term57 m n n') = (term58 m n n').
Proof. exact (MK_COMB (@lem1276152 m n n') (@lem1276171 m n n')). Qed.
Lemma lem1276173 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1276174 (m : nat) (n : nat) (n' : nat) : (term59 m n n') = (term60 m n n').
Proof. exact (MK_COMB (@lem1276173) (@lem1276172 m n n')). Qed.
Lemma lem1276175 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1276176 (m : nat) (n : nat) (n' : nat) : (term61 m n n') = (term62 m n n').
Proof. exact (MK_COMB (@lem1276175) (@lem1276174 m n n')). Qed.
Lemma lem1276177 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1276178 (m : nat) (n : nat) (n' : nat) (B : nat) : (term63 m n n' B) = (term64 m n n' B).
Proof. exact (MK_COMB (@lem1276176 m n n') (@lem1276177 B)). Qed.
Lemma lem1276179 (m : nat) (n : nat) (B : nat) : (term65 m n B) = (term66 m n B).
Proof. exact (fun_ext (fun n' : nat => @lem1276178 m n n' B)). Qed.
Lemma lem1276180 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1276181 (m : nat) (n : nat) (B : nat) : (term67 m n B) = (term68 m n B).
Proof. exact (MK_COMB (@lem1276180) (@lem1276179 m n B)). Qed.
Lemma lem1276186 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (fun_ext (fun B : nat => @lem1276181 m n B)). Qed.
Lemma lem1276187 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1276188 (m : nat) (n : nat) : (term24 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem1276187) (@lem1276186 m n)). Qed.
Lemma lem1276193 (m : nat) (n : nat) : (term23 m n) = (term71 m n).
Proof. exact (TRANS (@lem1276080 m n) (@lem1276188 m n)). Qed.
Lemma lem1276194 (m : nat) : (term72 m) = (term73 m).
Proof. exact (fun_ext (fun n : nat => @lem1276193 m n)). Qed.
Lemma lem1276195 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1276196 (m : nat) : (term74 m) = (term75 m).
Proof. exact (MK_COMB (@lem1276195) (@lem1276194 m)). Qed.
Lemma lem1276201 : term76 = term77.
Proof. exact (fun_ext (fun m : nat => @lem1276196 m)). Qed.
Lemma lem1276202 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1276203 : term78 = term79.
Proof. exact (MK_COMB (@lem1276202) (@lem1276201)). Qed.
Lemma lem1276208 : term79 = term78.
Proof. exact (SYM (@lem1276203)). Qed.
Lemma lem1276228 (m : nat) (n : nat) (p : nat) : (term9 m n p) = (term10 m n p).
Proof. exact (EQ_MP (@lem1276053 m n p) (@lem1276052 m n p)). Qed.
Lemma lem1276229 (m : nat) (n : nat) (n' : nat) : (term9 m n n') = (term10 m n n').
Proof. exact (@lem1276228 m n n'). Qed.
Lemma lem1276230 (m : nat) (n : nat) (n' : nat) : (term48 m n n') = (term48 m n n').
Proof. exact (eq_refl (term48 m n n')). Qed.
Lemma lem1276231 (m : nat) (n : nat) (n' : nat) : (term58 m n n') = (term80 m n n').
Proof. exact (MK_COMB (@lem1276230 m n n') (@lem1276229 m n n')). Qed.
Lemma lem1276232 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1276233 (m : nat) (n : nat) (n' : nat) : (term60 m n n') = (term81 m n n').
Proof. exact (MK_COMB (@lem1276232) (@lem1276231 m n n')). Qed.
Lemma lem1276235 (n : nat) : (term3 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1276044 n) (@lem1276043 n)). Qed.
Lemma lem1276236 (m : nat) (n : nat) (n' : nat) : (term81 m n n') = (NUMERAL 0).
Proof. exact (@lem1276235 (term10 m n n')). Qed.
Lemma lem1276237 (m : nat) (n : nat) (n' : nat) : (term60 m n n') = (NUMERAL 0).
Proof. exact (TRANS (@lem1276233 m n n') (@lem1276236 m n n')). Qed.
Lemma lem1276238 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1276239 (m : nat) (n : nat) (n' : nat) : (term62 m n n') = term82.
Proof. exact (MK_COMB (@lem1276238) (@lem1276237 m n n')). Qed.
Lemma lem1276240 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1276241 (m : nat) (n : nat) (n' : nat) (B : nat) : (term64 m n n' B) = (term1 B).
Proof. exact (MK_COMB (@lem1276239 m n n') (@lem1276240 B)). Qed.
Lemma lem1276243 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem1276041 n) (@lem1276040 n)). Qed.
Lemma lem1276244 (B : nat) : (term1 B) = True.
Proof. exact (@lem1276243 B). Qed.
Lemma lem1276245 (m : nat) (n : nat) (n' : nat) (B : nat) : (term64 m n n' B) = True.
Proof. exact (TRANS (@lem1276241 m n n' B) (@lem1276244 B)). Qed.
Lemma lem1276246 (m : nat) (n : nat) (B : nat) : (term66 m n B) = term83.
Proof. exact (fun_ext (fun n' : nat => @lem1276245 m n n' B)). Qed.
Lemma lem1276247 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1276248 (m : nat) (n : nat) (B : nat) : (term68 m n B) = term84.
Proof. exact (MK_COMB (@lem1276247) (@lem1276246 m n B)). Qed.
Lemma lem1276250 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1276251 (t : Prop) : (term86 t) = t.
Proof. exact (@lem1276250 nat t). Qed.
Lemma lem1276252 : term84 = True.
Proof. exact (@lem1276251 True). Qed.
Lemma lem1276253 (m : nat) (n : nat) (B : nat) : (term68 m n B) = True.
Proof. exact (TRANS (@lem1276248 m n B) (@lem1276252)). Qed.
Lemma lem1276254 (m : nat) (n : nat) : (term70 m n) = term83.
Proof. exact (fun_ext (fun B : nat => @lem1276253 m n B)). Qed.
Lemma lem1276255 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1276256 (m : nat) (n : nat) : (term71 m n) = term87.
Proof. exact (MK_COMB (@lem1276255) (@lem1276254 m n)). Qed.
Lemma lem1276258 {A : Type'} (t : Prop) : (term88 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1276259 (t : Prop) : (term89 t) = t.
Proof. exact (@lem1276258 nat t). Qed.
Lemma lem1276260 : term87 = True.
Proof. exact (@lem1276259 True). Qed.
Lemma lem1276261 (m : nat) (n : nat) : (term71 m n) = True.
Proof. exact (TRANS (@lem1276256 m n) (@lem1276260)). Qed.
Lemma lem1276262 (m : nat) : (term73 m) = term83.
Proof. exact (fun_ext (fun n : nat => @lem1276261 m n)). Qed.
Lemma lem1276263 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1276264 (m : nat) : (term75 m) = term84.
Proof. exact (MK_COMB (@lem1276263) (@lem1276262 m)). Qed.
Lemma lem1276266 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1276267 (t : Prop) : (term86 t) = t.
Proof. exact (@lem1276266 nat t). Qed.
Lemma lem1276268 : term84 = True.
Proof. exact (@lem1276267 True). Qed.
Lemma lem1276269 (m : nat) : (term75 m) = True.
Proof. exact (TRANS (@lem1276264 m) (@lem1276268)). Qed.
Lemma lem1276270 : term77 = term83.
Proof. exact (fun_ext (fun m : nat => @lem1276269 m)). Qed.
Lemma lem1276271 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1276272 : term79 = term84.
Proof. exact (MK_COMB (@lem1276271) (@lem1276270)). Qed.
Lemma lem1276274 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1276275 (t : Prop) : (term86 t) = t.
Proof. exact (@lem1276274 nat t). Qed.
Lemma lem1276276 : term84 = True.
Proof. exact (@lem1276275 True). Qed.
Lemma lem1276277 : term79 = True.
Proof. exact (TRANS (@lem1276272) (@lem1276276)). Qed.
Lemma lem1276278 : True = term79.
Proof. exact (SYM (@lem1276277)). Qed.
Lemma lem1276279 : term79.
Proof. exact (EQ_MP (@lem1276278) (@lem0)). Qed.
Lemma lem1276280 : term78.
Proof. exact (EQ_MP (@lem1276208) (@lem1276279)). Qed.
