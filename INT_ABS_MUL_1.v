Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_MUL_1_term_abbrevs.
Require Import INT_ABS_MUL_spec.
Require Import INT_ABS_POS_spec.
Require Import INT_FORALL_POS_spec.
Require Import INT_OF_NUM_EQ_spec.
Require Import INT_OF_NUM_MUL_spec.
Require Import MULT_EQ_1_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2338028 (P : int -> Prop) (h1 : (term0 P) = (term1 P)) : (term0 P) = (term1 P).
Proof. exact (h1). Qed.
Lemma lem2338029 (P : int -> Prop) (h1 : (term0 P) = (term1 P)) : (term1 P) = (term0 P).
Proof. exact (SYM (@lem2338028 P h1)). Qed.
Lemma lem2338030 (P : int -> Prop) (h1 : (term1 P) = (term0 P)) : (term1 P) = (term0 P).
Proof. exact (h1). Qed.
Lemma lem2338031 (P : int -> Prop) (h1 : (term1 P) = (term0 P)) : (term0 P) = (term1 P).
Proof. exact (SYM (@lem2338030 P h1)). Qed.
Lemma lem2338032 (P : int -> Prop) : ((term0 P) = (term1 P)) = ((term1 P) = (term0 P)).
Proof. exact (prop_ext (fun h1 : (term0 P) = (term1 P) => @lem2338029 P h1) (fun h1 : (term1 P) = (term0 P) => @lem2338031 P h1)). Qed.
Lemma lem2338033 : term2 = term3.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2338032 P)). Qed.
Lemma lem2338034 : (@all (int -> Prop)) = (@all (int -> Prop)).
Proof. exact (eq_refl (@all (int -> Prop))). Qed.
Lemma lem2338035 : term4 = term5.
Proof. exact (MK_COMB (@lem2338034) (@lem2338033)). Qed.
Lemma lem2338036 : term5.
Proof. exact (EQ_MP (@lem2338035) (@lem2315380)). Qed.
Lemma lem2338037 (m : nat) : term6 m.
Proof. exact (@lem85714 m). Qed.
Lemma lem2338038 (m : nat) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem2338039 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem2338038 m) (@lem2338037 m)). Qed.
Lemma lem2338040 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem2338039 m n). Qed.
Lemma lem2338041 (m : nat) (n : nat) : (term8 m n) = (((Nat.mul m n) = term9) = (term10 m n)).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem2338043 (m : nat) : term11 m.
Proof. exact (@lem2307147 m). Qed.
Lemma lem2338044 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem2338045 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem2338044 m) (@lem2338043 m)). Qed.
Lemma lem2338046 (m : nat) (n : nat) : term13 m n.
Proof. exact (@lem2338045 m n). Qed.
Lemma lem2338047 (m : nat) (n : nat) : (term13 m n) = (((int_of_num m) = (int_of_num n)) = (m = n)).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem2338049 (m : nat) : term14 m.
Proof. exact (@lem2307381 m). Qed.
Lemma lem2338050 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem2338051 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem2338050 m) (@lem2338049 m)). Qed.
Lemma lem2338052 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem2338051 m n). Qed.
Lemma lem2338053 (m : nat) (n : nat) : (term16 m n) = ((term17 m n) = (term18 m n)).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem2338055 (P : int -> Prop) : term19 P.
Proof. exact (@lem2338036 P). Qed.
Lemma lem2338056 (P : int -> Prop) : (term19 P) = ((term1 P) = (term0 P)).
Proof. exact (eq_refl (term19 P)). Qed.
Lemma lem2338058 (x : int) : term20 x.
Proof. exact (@lem2300522 x). Qed.
Lemma lem2338059 (x : int) : (term20 x) = (term21 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem2338060 (x : int) : term21 x.
Proof. exact (EQ_MP (@lem2338059 x) (@lem2338058 x)). Qed.
Lemma lem2338061 (y : int) : term20 y.
Proof. exact (@lem2300522 y). Qed.
Lemma lem2338062 (y : int) : (term20 y) = (term21 y).
Proof. exact (eq_refl (term20 y)). Qed.
Lemma lem2338063 (y : int) : term21 y.
Proof. exact (EQ_MP (@lem2338062 y) (@lem2338061 y)). Qed.
Lemma lem2338064 (x : int) : term22 x.
Proof. exact (@lem2300430 x). Qed.
Lemma lem2338065 (x : int) : (term22 x) = (term23 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem2338066 (x : int) : term23 x.
Proof. exact (EQ_MP (@lem2338065 x) (@lem2338064 x)). Qed.
Lemma lem2338067 (x : int) (y : int) : term24 x y.
Proof. exact (@lem2338066 x y). Qed.
Lemma lem2338068 (x : int) (y : int) : (term24 x y) = ((term25 x y) = (term26 x y)).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem2338075 (x : int) (y : int) : (term25 x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2338068 x y) (@lem2338067 x y)). Qed.
Lemma lem2338076 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2338077 (x : int) (y : int) : (term27 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem2338076) (@lem2338075 x y)). Qed.
Lemma lem2338078 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem2338079 (x : int) (y : int) : ((term25 x y) = term29) = ((term26 x y) = term29).
Proof. exact (MK_COMB (@lem2338077 x y) (@lem2338078)). Qed.
Lemma lem2338082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2338083 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem2338082) (@lem2338079 x y)). Qed.
Lemma lem2338090 (x : int) (y : int) : (term32 x y) = (term32 x y).
Proof. exact (eq_refl (term32 x y)). Qed.
Lemma lem2338091 (x : int) (y : int) : (((term25 x y) = term29) = (term32 x y)) = (((term26 x y) = term29) = (term32 x y)).
Proof. exact (MK_COMB (@lem2338083 x y) (@lem2338090 x y)). Qed.
Lemma lem2338094 (x : int) (y : int) : (((term26 x y) = term29) = (term32 x y)) = (((term25 x y) = term29) = (term32 x y)).
Proof. exact (SYM (@lem2338091 x y)). Qed.
Lemma lem2338096 (P : int -> Prop) : (term1 P) = (term0 P).
Proof. exact (EQ_MP (@lem2338056 P) (@lem2338055 P)). Qed.
Lemma lem2338097 : term33 = term34.
Proof. exact (@lem2338096 term35). Qed.
Lemma lem2338098 (a : int) : (term36 a) = (term37 a).
Proof. exact (eq_refl (term36 a)). Qed.
Lemma lem2338099 (a : int) : (term38 a) = (term38 a).
Proof. exact (eq_refl (term38 a)). Qed.
Lemma lem2338100 (a : int) : (term39 a) = (term40 a).
Proof. exact (MK_COMB (@lem2338099 a) (@lem2338098 a)). Qed.
Lemma lem2338101 : term41 = term42.
Proof. exact (fun_ext (fun a : int => @lem2338100 a)). Qed.
Lemma lem2338102 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2338103 : term33 = term43.
Proof. exact (MK_COMB (@lem2338102) (@lem2338101)). Qed.
Lemma lem2338104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2338105 : term44 = term45.
Proof. exact (MK_COMB (@lem2338104) (@lem2338103)). Qed.
Lemma lem2338106 (n : nat) : (term46 n) = (term47 n).
Proof. exact (eq_refl (term46 n)). Qed.
Lemma lem2338107 : term48 = term49.
Proof. exact (fun_ext (fun n : nat => @lem2338106 n)). Qed.
Lemma lem2338108 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2338109 : term34 = term50.
Proof. exact (MK_COMB (@lem2338108) (@lem2338107)). Qed.
Lemma lem2338110 : (term33 = term34) = (term43 = term50).
Proof. exact (MK_COMB (@lem2338105) (@lem2338109)). Qed.
Lemma lem2338111 : term43 = term50.
Proof. exact (EQ_MP (@lem2338110) (@lem2338097)). Qed.
Lemma lem2338117 (P : int -> Prop) : (term1 P) = (term0 P).
Proof. exact (EQ_MP (@lem2338056 P) (@lem2338055 P)). Qed.
Lemma lem2338118 (n : nat) : (term51 n) = (term52 n).
Proof. exact (@lem2338117 (term53 n)). Qed.
Lemma lem2338119 (n : nat) (b : int) : (term54 n b) = (((term55 n b) = term29) = (term56 n b)).
Proof. exact (eq_refl (term54 n b)). Qed.
Lemma lem2338120 (b : int) : (term38 b) = (term38 b).
Proof. exact (eq_refl (term38 b)). Qed.
Lemma lem2338121 (n : nat) (b : int) : (term57 n b) = (term58 n b).
Proof. exact (MK_COMB (@lem2338120 b) (@lem2338119 n b)). Qed.
Lemma lem2338122 (n : nat) : (term59 n) = (term60 n).
Proof. exact (fun_ext (fun b : int => @lem2338121 n b)). Qed.
Lemma lem2338123 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2338124 (n : nat) : (term51 n) = (term47 n).
Proof. exact (MK_COMB (@lem2338123) (@lem2338122 n)). Qed.
Lemma lem2338125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2338126 (n : nat) : (term61 n) = (term62 n).
Proof. exact (MK_COMB (@lem2338125) (@lem2338124 n)). Qed.
Lemma lem2338127 (n : nat) (n' : nat) : (term63 n n') = (((term17 n n') = term29) = (term64 n n')).
Proof. exact (eq_refl (term63 n n')). Qed.
Lemma lem2338128 (n : nat) : (term65 n) = (term66 n).
Proof. exact (fun_ext (fun n' : nat => @lem2338127 n n')). Qed.
Lemma lem2338129 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2338130 (n : nat) : (term52 n) = (term67 n).
Proof. exact (MK_COMB (@lem2338129) (@lem2338128 n)). Qed.
Lemma lem2338131 (n : nat) : ((term51 n) = (term52 n)) = ((term47 n) = (term67 n)).
Proof. exact (MK_COMB (@lem2338126 n) (@lem2338130 n)). Qed.
Lemma lem2338132 (n : nat) : (term47 n) = (term67 n).
Proof. exact (EQ_MP (@lem2338131 n) (@lem2338118 n)). Qed.
Lemma lem2338142 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (EQ_MP (@lem2338053 m n) (@lem2338052 m n)). Qed.
Lemma lem2338143 (n : nat) (n' : nat) : (term17 n n') = (term18 n n').
Proof. exact (@lem2338142 n n'). Qed.
Lemma lem2338144 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2338145 (n : nat) (n' : nat) : (term68 n n') = (term69 n n').
Proof. exact (MK_COMB (@lem2338144) (@lem2338143 n n')). Qed.
Lemma lem2338146 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem2338147 (n : nat) (n' : nat) : ((term17 n n') = term29) = ((term18 n n') = term29).
Proof. exact (MK_COMB (@lem2338145 n n') (@lem2338146)). Qed.
Lemma lem2338149 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2338047 m n) (@lem2338046 m n)). Qed.
Lemma lem2338150 (n : nat) (n' : nat) : ((term18 n n') = term29) = ((Nat.mul n n') = term9).
Proof. exact (@lem2338149 (Nat.mul n n') term9). Qed.
Lemma lem2338152 (m : nat) (n : nat) : ((Nat.mul m n) = term9) = (term10 m n).
Proof. exact (EQ_MP (@lem2338041 m n) (@lem2338040 m n)). Qed.
Lemma lem2338153 (n : nat) (n' : nat) : ((Nat.mul n n') = term9) = (term10 n n').
Proof. exact (@lem2338152 n n'). Qed.
Lemma lem2338160 (n : nat) (n' : nat) : ((term18 n n') = term29) = (term10 n n').
Proof. exact (TRANS (@lem2338150 n n') (@lem2338153 n n')). Qed.
Lemma lem2338161 (n : nat) (n' : nat) : ((term17 n n') = term29) = (term10 n n').
Proof. exact (TRANS (@lem2338147 n n') (@lem2338160 n n')). Qed.
Lemma lem2338162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2338163 (n : nat) (n' : nat) : (term70 n n') = (term71 n n').
Proof. exact (MK_COMB (@lem2338162) (@lem2338161 n n')). Qed.
Lemma lem2338167 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2338047 m n) (@lem2338046 m n)). Qed.
Lemma lem2338168 (n : nat) : ((int_of_num n) = term29) = (n = term9).
Proof. exact (@lem2338167 n term9). Qed.
Lemma lem2338171 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2338172 (n : nat) : (term72 n) = (term73 n).
Proof. exact (MK_COMB (@lem2338171) (@lem2338168 n)). Qed.
Lemma lem2338174 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2338047 m n) (@lem2338046 m n)). Qed.
Lemma lem2338175 (n' : nat) : ((int_of_num n') = term29) = (n' = term9).
Proof. exact (@lem2338174 n' term9). Qed.
Lemma lem2338178 (n : nat) (n' : nat) : (term64 n n') = (term10 n n').
Proof. exact (MK_COMB (@lem2338172 n) (@lem2338175 n')). Qed.
Lemma lem2338181 (n : nat) (n' : nat) : (((term17 n n') = term29) = (term64 n n')) = ((term10 n n') = (term10 n n')).
Proof. exact (MK_COMB (@lem2338163 n n') (@lem2338178 n n')). Qed.
Lemma lem2338183 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2338184 (x : Prop) : (x = x) = True.
Proof. exact (@lem2338183 Prop x). Qed.
Lemma lem2338185 (n : nat) (n' : nat) : ((term10 n n') = (term10 n n')) = True.
Proof. exact (@lem2338184 (term10 n n')). Qed.
Lemma lem2338186 (n : nat) (n' : nat) : (((term17 n n') = term29) = (term64 n n')) = True.
Proof. exact (TRANS (@lem2338181 n n') (@lem2338185 n n')). Qed.
Lemma lem2338187 (n : nat) : (term66 n) = term74.
Proof. exact (fun_ext (fun n' : nat => @lem2338186 n n')). Qed.
Lemma lem2338188 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2338189 (n : nat) : (term67 n) = term75.
Proof. exact (MK_COMB (@lem2338188) (@lem2338187 n)). Qed.
Lemma lem2338191 {A : Type'} (t : Prop) : (term76 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2338192 (t : Prop) : (term77 t) = t.
Proof. exact (@lem2338191 nat t). Qed.
Lemma lem2338193 : term75 = True.
Proof. exact (@lem2338192 True). Qed.
Lemma lem2338194 (n : nat) : (term67 n) = True.
Proof. exact (TRANS (@lem2338189 n) (@lem2338193)). Qed.
Lemma lem2338195 (n : nat) : (term47 n) = True.
Proof. exact (TRANS (@lem2338132 n) (@lem2338194 n)). Qed.
Lemma lem2338196 : term49 = term74.
Proof. exact (fun_ext (fun n : nat => @lem2338195 n)). Qed.
Lemma lem2338197 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2338198 : term50 = term75.
Proof. exact (MK_COMB (@lem2338197) (@lem2338196)). Qed.
Lemma lem2338200 {A : Type'} (t : Prop) : (term76 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2338201 (t : Prop) : (term77 t) = t.
Proof. exact (@lem2338200 nat t). Qed.
Lemma lem2338202 : term75 = True.
Proof. exact (@lem2338201 True). Qed.
Lemma lem2338203 : term50 = True.
Proof. exact (TRANS (@lem2338198) (@lem2338202)). Qed.
Lemma lem2338204 : term43 = True.
Proof. exact (TRANS (@lem2338111) (@lem2338203)). Qed.
Lemma lem2338205 : True = term43.
Proof. exact (SYM (@lem2338204)). Qed.
Lemma lem2338206 : term43.
Proof. exact (EQ_MP (@lem2338205) (@lem0)). Qed.
Lemma lem2338207 (x : int) : term78 x.
Proof. exact (@lem2338206 (int_abs x)). Qed.
Lemma lem2338208 (x : int) : (term78 x) = (term79 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem2338209 (x : int) : term79 x.
Proof. exact (EQ_MP (@lem2338208 x) (@lem2338207 x)). Qed.
Lemma lem2338210 (x : int) : term80 x.
Proof. exact (@lem2338209 x (@lem2338060 x)). Qed.
Lemma lem2338211 (x : int) (y : int) : term81 x y.
Proof. exact (@lem2338210 x (int_abs y)). Qed.
Lemma lem2338212 (x : int) (y : int) : (term81 x y) = (term82 x y).
Proof. exact (eq_refl (term81 x y)). Qed.
Lemma lem2338213 (x : int) (y : int) : term82 x y.
Proof. exact (EQ_MP (@lem2338212 x y) (@lem2338211 x y)). Qed.
Lemma lem2338214 (x : int) (y : int) : ((term26 x y) = term29) = (term32 x y).
Proof. exact (@lem2338213 x y (@lem2338063 y)). Qed.
Lemma lem2338215 (x : int) (y : int) : ((term25 x y) = term29) = (term32 x y).
Proof. exact (EQ_MP (@lem2338094 x y) (@lem2338214 x y)). Qed.
Lemma lem2338220 (x : int) : term83 x.
Proof. exact (fun y : int => @lem2338215 x y). Qed.
Lemma lem2338225 : term84.
Proof. exact (fun x : int => @lem2338220 x). Qed.
