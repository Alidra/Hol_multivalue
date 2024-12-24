Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVIDES_DIVIDES_DIV_EQ_term_abbrevs.
Require Import INT_DIVIDES_DIVIDES_DIV_EQ_spec.
Require Import INT_OF_NUM_DIV_spec.
Require Import INT_OF_NUM_MUL_spec.
Require Import num_divides_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3113122 (n : int) : term0 n.
Proof. exact (@lem2741943 n). Qed.
Lemma lem3113123 (n : int) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem3113124 (n : int) : term1 n.
Proof. exact (EQ_MP (@lem3113123 n) (@lem3113122 n)). Qed.
Lemma lem3113125 (n : int) (d : int) : term2 n d.
Proof. exact (@lem3113124 n d). Qed.
Lemma lem3113126 (d : int) (n : int) : (term2 n d) = (term3 d n).
Proof. exact (eq_refl (term2 n d)). Qed.
Lemma lem3113127 (d : int) (n : int) : term3 d n.
Proof. exact (EQ_MP (@lem3113126 d n) (@lem3113125 n d)). Qed.
Lemma lem3113128 (d : int) (n : int) (e : int) : term4 d n e.
Proof. exact (@lem3113127 d n e). Qed.
Lemma lem3113129 (d : int) (e : int) (n : int) : (term4 d n e) = ((term5 e n d) = (term6 d e n)).
Proof. exact (eq_refl (term4 d n e)). Qed.
Lemma lem3113133 (m : nat) (n : nat) (h1 : (term7 m n) = (term8 m n)) : (term7 m n) = (term8 m n).
Proof. exact (h1). Qed.
Lemma lem3113134 (m : nat) (n : nat) (h1 : (term7 m n) = (term8 m n)) : (term8 m n) = (term7 m n).
Proof. exact (SYM (@lem3113133 m n h1)). Qed.
Lemma lem3113135 (m : nat) (n : nat) (h1 : (term8 m n) = (term7 m n)) : (term8 m n) = (term7 m n).
Proof. exact (h1). Qed.
Lemma lem3113136 (m : nat) (n : nat) (h1 : (term8 m n) = (term7 m n)) : (term7 m n) = (term8 m n).
Proof. exact (SYM (@lem3113135 m n h1)). Qed.
Lemma lem3113137 (m : nat) (n : nat) : ((term7 m n) = (term8 m n)) = ((term8 m n) = (term7 m n)).
Proof. exact (prop_ext (fun h1 : (term7 m n) = (term8 m n) => @lem3113134 m n h1) (fun h1 : (term8 m n) = (term7 m n) => @lem3113136 m n h1)). Qed.
Lemma lem3113138 (m : nat) : (term9 m) = (term10 m).
Proof. exact (fun_ext (fun n : nat => @lem3113137 m n)). Qed.
Lemma lem3113139 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3113140 (m : nat) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem3113139) (@lem3113138 m)). Qed.
Lemma lem3113141 : term13 = term14.
Proof. exact (fun_ext (fun m : nat => @lem3113140 m)). Qed.
Lemma lem3113142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3113143 : term15 = term16.
Proof. exact (MK_COMB (@lem3113142) (@lem3113141)). Qed.
Lemma lem3113144 : term16.
Proof. exact (EQ_MP (@lem3113143) (@lem2307381)). Qed.
Lemma lem3113147 (m : nat) (n : nat) (h1 : (term17 m n) = (term18 m n)) : (term17 m n) = (term18 m n).
Proof. exact (h1). Qed.
Lemma lem3113148 (m : nat) (n : nat) (h1 : (term17 m n) = (term18 m n)) : (term18 m n) = (term17 m n).
Proof. exact (SYM (@lem3113147 m n h1)). Qed.
Lemma lem3113149 (m : nat) (n : nat) (h1 : (term18 m n) = (term17 m n)) : (term18 m n) = (term17 m n).
Proof. exact (h1). Qed.
Lemma lem3113150 (m : nat) (n : nat) (h1 : (term18 m n) = (term17 m n)) : (term17 m n) = (term18 m n).
Proof. exact (SYM (@lem3113149 m n h1)). Qed.
Lemma lem3113151 (m : nat) (n : nat) : ((term17 m n) = (term18 m n)) = ((term18 m n) = (term17 m n)).
Proof. exact (prop_ext (fun h1 : (term17 m n) = (term18 m n) => @lem3113148 m n h1) (fun h1 : (term18 m n) = (term17 m n) => @lem3113150 m n h1)). Qed.
Lemma lem3113152 (m : nat) : (term19 m) = (term20 m).
Proof. exact (fun_ext (fun n : nat => @lem3113151 m n)). Qed.
Lemma lem3113153 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3113154 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem3113153) (@lem3113152 m)). Qed.
Lemma lem3113155 : term23 = term24.
Proof. exact (fun_ext (fun m : nat => @lem3113154 m)). Qed.
Lemma lem3113156 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3113157 : term25 = term26.
Proof. exact (MK_COMB (@lem3113156) (@lem3113155)). Qed.
Lemma lem3113158 : term26.
Proof. exact (EQ_MP (@lem3113157) (@lem2538105)). Qed.
Lemma lem3113159 (m : nat) : term27 m.
Proof. exact (@lem3113144 m). Qed.
Lemma lem3113160 (m : nat) : (term27 m) = (term12 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem3113161 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem3113160 m) (@lem3113159 m)). Qed.
Lemma lem3113162 (m : nat) (n : nat) : term28 m n.
Proof. exact (@lem3113161 m n). Qed.
Lemma lem3113163 (m : nat) (n : nat) : (term28 m n) = ((term8 m n) = (term7 m n)).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem3113165 (m : nat) : term29 m.
Proof. exact (@lem3113158 m). Qed.
Lemma lem3113166 (m : nat) : (term29 m) = (term22 m).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem3113167 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem3113166 m) (@lem3113165 m)). Qed.
Lemma lem3113168 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem3113167 m n). Qed.
Lemma lem3113169 (m : nat) (n : nat) : (term30 m n) = ((term18 m n) = (term17 m n)).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem3113171 (a : nat) : term31 a.
Proof. exact (@lem2836659 a). Qed.
Lemma lem3113172 (a : nat) : (term31 a) = (term32 a).
Proof. exact (eq_refl (term31 a)). Qed.
Lemma lem3113173 (a : nat) : term32 a.
Proof. exact (EQ_MP (@lem3113172 a) (@lem3113171 a)). Qed.
Lemma lem3113174 (a : nat) (b : nat) : term33 a b.
Proof. exact (@lem3113173 a b). Qed.
Lemma lem3113175 (a : nat) (b : nat) : (term33 a b) = ((num_divides a b) = (term34 a b)).
Proof. exact (eq_refl (term33 a b)). Qed.
Lemma lem3113194 (a : nat) (b : nat) : (num_divides a b) = (term34 a b).
Proof. exact (EQ_MP (@lem3113175 a b) (@lem3113174 a b)). Qed.
Lemma lem3113195 (d : nat) (n : nat) : (num_divides d n) = (term34 d n).
Proof. exact (@lem3113194 d n). Qed.
Lemma lem3113196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3113197 (d : nat) (n : nat) : (term35 d n) = (term36 d n).
Proof. exact (MK_COMB (@lem3113196) (@lem3113195 d n)). Qed.
Lemma lem3113199 (a : nat) (b : nat) : (num_divides a b) = (term34 a b).
Proof. exact (EQ_MP (@lem3113175 a b) (@lem3113174 a b)). Qed.
Lemma lem3113200 (e : nat) (n : nat) (d : nat) : (term37 e n d) = (term38 e n d).
Proof. exact (@lem3113199 e (Nat.div n d)). Qed.
Lemma lem3113202 (m : nat) (n : nat) : (term18 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem3113169 m n) (@lem3113168 m n)). Qed.
Lemma lem3113203 (n : nat) (d : nat) : (term18 n d) = (term17 n d).
Proof. exact (@lem3113202 n d). Qed.
Lemma lem3113204 (e : nat) : (term39 e) = (term39 e).
Proof. exact (eq_refl (term39 e)). Qed.
Lemma lem3113205 (e : nat) (n : nat) (d : nat) : (term38 e n d) = (term40 e n d).
Proof. exact (MK_COMB (@lem3113204 e) (@lem3113203 n d)). Qed.
Lemma lem3113206 (e : nat) (n : nat) (d : nat) : (term37 e n d) = (term40 e n d).
Proof. exact (TRANS (@lem3113200 e n d) (@lem3113205 e n d)). Qed.
Lemma lem3113207 (e : nat) (n : nat) (d : nat) : (term41 e n d) = (term42 e n d).
Proof. exact (MK_COMB (@lem3113197 d n) (@lem3113206 e n d)). Qed.
Lemma lem3113210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3113211 (e : nat) (n : nat) (d : nat) : (term43 e n d) = (term44 e n d).
Proof. exact (MK_COMB (@lem3113210) (@lem3113207 e n d)). Qed.
Lemma lem3113213 (a : nat) (b : nat) : (num_divides a b) = (term34 a b).
Proof. exact (EQ_MP (@lem3113175 a b) (@lem3113174 a b)). Qed.
Lemma lem3113214 (d : nat) (e : nat) (n : nat) : (term45 d e n) = (term46 d e n).
Proof. exact (@lem3113213 (Nat.mul d e) n). Qed.
Lemma lem3113216 (m : nat) (n : nat) : (term8 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem3113163 m n) (@lem3113162 m n)). Qed.
Lemma lem3113217 (d : nat) (e : nat) : (term8 d e) = (term7 d e).
Proof. exact (@lem3113216 d e). Qed.
Lemma lem3113218 : int_divides = int_divides.
Proof. exact (eq_refl int_divides). Qed.
Lemma lem3113219 (d : nat) (e : nat) : (term47 d e) = (term48 d e).
Proof. exact (MK_COMB (@lem3113218) (@lem3113217 d e)). Qed.
Lemma lem3113220 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem3113221 (d : nat) (e : nat) (n : nat) : (term46 d e n) = (term49 d e n).
Proof. exact (MK_COMB (@lem3113219 d e) (@lem3113220 n)). Qed.
Lemma lem3113222 (d : nat) (e : nat) (n : nat) : (term45 d e n) = (term49 d e n).
Proof. exact (TRANS (@lem3113214 d e n) (@lem3113221 d e n)). Qed.
Lemma lem3113223 (d : nat) (e : nat) (n : nat) : ((term41 e n d) = (term45 d e n)) = ((term42 e n d) = (term49 d e n)).
Proof. exact (MK_COMB (@lem3113211 e n d) (@lem3113222 d e n)). Qed.
Lemma lem3113226 (d : nat) (n : nat) : (term50 d n) = (term51 d n).
Proof. exact (fun_ext (fun e : nat => @lem3113223 d e n)). Qed.
Lemma lem3113227 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3113228 (d : nat) (n : nat) : (term52 d n) = (term53 d n).
Proof. exact (MK_COMB (@lem3113227) (@lem3113226 d n)). Qed.
Lemma lem3113233 (n : nat) : (term54 n) = (term55 n).
Proof. exact (fun_ext (fun d : nat => @lem3113228 d n)). Qed.
Lemma lem3113234 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3113235 (n : nat) : (term56 n) = (term57 n).
Proof. exact (MK_COMB (@lem3113234) (@lem3113233 n)). Qed.
Lemma lem3113240 : term58 = term59.
Proof. exact (fun_ext (fun n : nat => @lem3113235 n)). Qed.
Lemma lem3113241 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3113242 : term60 = term61.
Proof. exact (MK_COMB (@lem3113241) (@lem3113240)). Qed.
Lemma lem3113247 : term61 = term60.
Proof. exact (SYM (@lem3113242)). Qed.
Lemma lem3113263 (d : int) (e : int) (n : int) : (term5 e n d) = (term6 d e n).
Proof. exact (EQ_MP (@lem3113129 d e n) (@lem3113128 d n e)). Qed.
Lemma lem3113264 (d : nat) (e : nat) (n : nat) : (term42 e n d) = (term49 d e n).
Proof. exact (@lem3113263 (int_of_num d) (int_of_num e) (int_of_num n)). Qed.
Lemma lem3113265 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3113266 (d : nat) (e : nat) (n : nat) : (term44 e n d) = (term62 d e n).
Proof. exact (MK_COMB (@lem3113265) (@lem3113264 d e n)). Qed.
Lemma lem3113267 (d : nat) (e : nat) (n : nat) : (term49 d e n) = (term49 d e n).
Proof. exact (eq_refl (term49 d e n)). Qed.
Lemma lem3113268 (d : nat) (e : nat) (n : nat) : ((term42 e n d) = (term49 d e n)) = ((term49 d e n) = (term49 d e n)).
Proof. exact (MK_COMB (@lem3113266 d e n) (@lem3113267 d e n)). Qed.
Lemma lem3113270 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3113271 (x : Prop) : (x = x) = True.
Proof. exact (@lem3113270 Prop x). Qed.
Lemma lem3113272 (d : nat) (e : nat) (n : nat) : ((term49 d e n) = (term49 d e n)) = True.
Proof. exact (@lem3113271 (term49 d e n)). Qed.
Lemma lem3113273 (d : nat) (e : nat) (n : nat) : ((term42 e n d) = (term49 d e n)) = True.
Proof. exact (TRANS (@lem3113268 d e n) (@lem3113272 d e n)). Qed.
Lemma lem3113274 (d : nat) (n : nat) : (term51 d n) = term63.
Proof. exact (fun_ext (fun e : nat => @lem3113273 d e n)). Qed.
Lemma lem3113275 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3113276 (d : nat) (n : nat) : (term53 d n) = term64.
Proof. exact (MK_COMB (@lem3113275) (@lem3113274 d n)). Qed.
Lemma lem3113278 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3113279 (t : Prop) : (term66 t) = t.
Proof. exact (@lem3113278 nat t). Qed.
Lemma lem3113280 : term64 = True.
Proof. exact (@lem3113279 True). Qed.
Lemma lem3113281 (d : nat) (n : nat) : (term53 d n) = True.
Proof. exact (TRANS (@lem3113276 d n) (@lem3113280)). Qed.
Lemma lem3113282 (n : nat) : (term55 n) = term63.
Proof. exact (fun_ext (fun d : nat => @lem3113281 d n)). Qed.
Lemma lem3113283 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3113284 (n : nat) : (term57 n) = term64.
Proof. exact (MK_COMB (@lem3113283) (@lem3113282 n)). Qed.
Lemma lem3113286 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3113287 (t : Prop) : (term66 t) = t.
Proof. exact (@lem3113286 nat t). Qed.
Lemma lem3113288 : term64 = True.
Proof. exact (@lem3113287 True). Qed.
Lemma lem3113289 (n : nat) : (term57 n) = True.
Proof. exact (TRANS (@lem3113284 n) (@lem3113288)). Qed.
Lemma lem3113290 : term59 = term63.
Proof. exact (fun_ext (fun n : nat => @lem3113289 n)). Qed.
Lemma lem3113291 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3113292 : term61 = term64.
Proof. exact (MK_COMB (@lem3113291) (@lem3113290)). Qed.
Lemma lem3113294 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3113295 (t : Prop) : (term66 t) = t.
Proof. exact (@lem3113294 nat t). Qed.
Lemma lem3113296 : term64 = True.
Proof. exact (@lem3113295 True). Qed.
Lemma lem3113297 : term61 = True.
Proof. exact (TRANS (@lem3113292) (@lem3113296)). Qed.
Lemma lem3113298 : True = term61.
Proof. exact (SYM (@lem3113297)). Qed.
Lemma lem3113299 : term61.
Proof. exact (EQ_MP (@lem3113298) (@lem0)). Qed.
Lemma lem3113300 : term60.
Proof. exact (EQ_MP (@lem3113247) (@lem3113299)). Qed.
