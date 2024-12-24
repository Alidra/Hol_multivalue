Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_EVEN_2_term_abbrevs.
Require Import EVEN_EXISTS_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import MOD_MOD_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Lemma lem184095 (m : nat) : term0 m.
Proof. exact (@lem182819 m). Qed.
Lemma lem184096 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem184097 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem184096 m) (@lem184095 m)). Qed.
Lemma lem184098 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem184097 m n). Qed.
Lemma lem184099 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem184100 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem184099 m n) (@lem184098 m n)). Qed.
Lemma lem184101 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem184100 m n p). Qed.
Lemma lem184102 (p : nat) (m : nat) (n : nat) : (term4 m n p) = ((term5 m p n) = (Nat.modulo m n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem184104 {A : Type'} (P : A -> Prop) : term6 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem184105 {A : Type'} (P : A -> Prop) : (term6 A P) = (term7 A P).
Proof. exact (eq_refl (term6 A P)). Qed.
Lemma lem184106 {A : Type'} (P : A -> Prop) : term7 A P.
Proof. exact (EQ_MP (@lem184105 A P) (@lem184104 A P)). Qed.
Lemma lem184107 {A : Type'} (P : A -> Prop) (Q : Prop) : term8 A P Q.
Proof. exact (@lem184106 A P Q). Qed.
Lemma lem184108 {A : Type'} (P : A -> Prop) (Q : Prop) : (term8 A P Q) = ((term9 A P Q) = (term10 A P Q)).
Proof. exact (eq_refl (term8 A P Q)). Qed.
Lemma lem184110 (n : nat) : term11 n.
Proof. exact (@lem128828 n). Qed.
Lemma lem184111 (n : nat) : (term11 n) = ((Coq.Arith.PeanoNat.Nat.Even n) = (term12 n)).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem184124 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term13 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem184125 (p : Prop) (q : Prop) (p' : Prop) : term14 p q p'.
Proof. exact (fun q' : Prop => @lem184124 p q p' q'). Qed.
Lemma lem184126 (p : Prop) (q : Prop) : term15 p q.
Proof. exact (fun p' : Prop => @lem184125 p q p'). Qed.
Lemma lem184127 (n : nat) (m : nat) : term16 n m.
Proof. exact (@lem184126 (Coq.Arith.PeanoNat.Nat.Even n) ((term17 m n) = (term18 m))). Qed.
Lemma lem184128 (n : nat) (m : nat) (p' : Prop) : term19 n m p'.
Proof. exact (@lem184127 n m p'). Qed.
Lemma lem184129 (n : nat) (m : nat) (p' : Prop) : (term19 n m p') = (term20 n m p').
Proof. exact (eq_refl (term19 n m p')). Qed.
Lemma lem184130 (n : nat) (m : nat) (p' : Prop) : term20 n m p'.
Proof. exact (EQ_MP (@lem184129 n m p') (@lem184128 n m p')). Qed.
Lemma lem184131 (n : nat) (m : nat) (p' : Prop) (q' : Prop) : term21 n m p' q'.
Proof. exact (@lem184130 n m p' q'). Qed.
Lemma lem184132 (n : nat) (m : nat) (p' : Prop) (q' : Prop) : (term21 n m p' q') = (term22 n m p' q').
Proof. exact (eq_refl (term21 n m p' q')). Qed.
Lemma lem184133 (n : nat) (m : nat) (p' : Prop) (q' : Prop) : term22 n m p' q'.
Proof. exact (EQ_MP (@lem184132 n m p' q') (@lem184131 n m p' q')). Qed.
Lemma lem184135 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (term12 n).
Proof. exact (EQ_MP (@lem184111 n) (@lem184110 n)). Qed.
Lemma lem184142 (m : nat) (n : nat) (q' : Prop) : term23 m n q'.
Proof. exact (@lem184133 n m (term12 n) q'). Qed.
Lemma lem184143 (m : nat) (n : nat) (q' : Prop) : term24 m n q'.
Proof. exact (@lem184142 m n q' (@lem184135 n)). Qed.
Lemma lem184149 (n : nat) (m : nat) : ((term17 m n) = (term18 m)) = ((term17 m n) = (term18 m)).
Proof. exact (eq_refl ((term17 m n) = (term18 m))). Qed.
Lemma lem184150 (n : nat) (m : nat) : term25 n m.
Proof. exact (fun h0 : term12 n => @lem184149 n m). Qed.
Lemma lem184151 (n : nat) (m : nat) : term26 n m.
Proof. exact (@lem184143 m n ((term17 m n) = (term18 m))). Qed.
Lemma lem184152 (n : nat) (m : nat) : (term27 n m) = (term28 n m).
Proof. exact (@lem184151 n m (@lem184150 n m)). Qed.
Lemma lem184154 {A : Type'} (P : A -> Prop) (Q : Prop) : (term9 A P Q) = (term10 A P Q).
Proof. exact (EQ_MP (@lem184108 A P Q) (@lem184107 A P Q)). Qed.
Lemma lem184155 (P : nat -> Prop) (Q : Prop) : (term29 P Q) = (term30 P Q).
Proof. exact (@lem184154 nat P Q). Qed.
Lemma lem184156 (n : nat) (m : nat) : (term31 n m) = (term32 n m).
Proof. exact (@lem184155 (term33 n) ((term17 m n) = (term18 m))). Qed.
Lemma lem184157 (n : nat) (m : nat) : (term34 n m) = (n = (term35 m)).
Proof. exact (eq_refl (term34 n m)). Qed.
Lemma lem184158 (n : nat) : (term36 n) = (term33 n).
Proof. exact (fun_ext (fun m : nat => @lem184157 n m)). Qed.
Lemma lem184159 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem184160 (n : nat) : (term37 n) = (term12 n).
Proof. exact (MK_COMB (@lem184159) (@lem184158 n)). Qed.
Lemma lem184161 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem184162 (n : nat) : (term38 n) = (term39 n).
Proof. exact (MK_COMB (@lem184161) (@lem184160 n)). Qed.
Lemma lem184163 (n : nat) (m : nat) : ((term17 m n) = (term18 m)) = ((term17 m n) = (term18 m)).
Proof. exact (eq_refl ((term17 m n) = (term18 m))). Qed.
Lemma lem184164 (n : nat) (m : nat) : (term31 n m) = (term28 n m).
Proof. exact (MK_COMB (@lem184162 n) (@lem184163 n m)). Qed.
Lemma lem184165 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem184166 (n : nat) (m : nat) : (term40 n m) = (term41 n m).
Proof. exact (MK_COMB (@lem184165) (@lem184164 n m)). Qed.
Lemma lem184167 (n : nat) (m' : nat) : (term34 n m') = (n = (term35 m')).
Proof. exact (eq_refl (term34 n m')). Qed.
Lemma lem184168 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem184169 (n : nat) (m' : nat) : (term42 n m') = (term43 n m').
Proof. exact (MK_COMB (@lem184168) (@lem184167 n m')). Qed.
Lemma lem184170 (n : nat) (m : nat) : ((term17 m n) = (term18 m)) = ((term17 m n) = (term18 m)).
Proof. exact (eq_refl ((term17 m n) = (term18 m))). Qed.
Lemma lem184171 (m' : nat) (n : nat) (m : nat) : (term44 m' n m) = (term45 m' n m).
Proof. exact (MK_COMB (@lem184169 n m') (@lem184170 n m)). Qed.
Lemma lem184172 (n : nat) (m : nat) : (term46 n m) = (term47 n m).
Proof. exact (fun_ext (fun m' : nat => @lem184171 m' n m)). Qed.
Lemma lem184173 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem184174 (n : nat) (m : nat) : (term32 n m) = (term48 n m).
Proof. exact (MK_COMB (@lem184173) (@lem184172 n m)). Qed.
Lemma lem184175 (n : nat) (m : nat) : ((term31 n m) = (term32 n m)) = ((term28 n m) = (term48 n m)).
Proof. exact (MK_COMB (@lem184166 n m) (@lem184174 n m)). Qed.
Lemma lem184176 (n : nat) (m : nat) : (term28 n m) = (term48 n m).
Proof. exact (EQ_MP (@lem184175 n m) (@lem184156 n m)). Qed.
Lemma lem184186 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term13 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem184187 (p : Prop) (q : Prop) (p' : Prop) : term14 p q p'.
Proof. exact (fun q' : Prop => @lem184186 p q p' q'). Qed.
Lemma lem184188 (p : Prop) (q : Prop) : term15 p q.
Proof. exact (fun p' : Prop => @lem184187 p q p'). Qed.
Lemma lem184189 (m' : nat) (n : nat) (m : nat) : term49 m' n m.
Proof. exact (@lem184188 (n = (term35 m')) ((term17 m n) = (term18 m))). Qed.
Lemma lem184190 (m' : nat) (n : nat) (m : nat) (p' : Prop) : term50 m' n m p'.
Proof. exact (@lem184189 m' n m p'). Qed.
Lemma lem184191 (m' : nat) (n : nat) (m : nat) (p' : Prop) : (term50 m' n m p') = (term51 m' n m p').
Proof. exact (eq_refl (term50 m' n m p')). Qed.
Lemma lem184192 (m' : nat) (n : nat) (m : nat) (p' : Prop) : term51 m' n m p'.
Proof. exact (EQ_MP (@lem184191 m' n m p') (@lem184190 m' n m p')). Qed.
Lemma lem184193 (m' : nat) (n : nat) (m : nat) (p' : Prop) (q' : Prop) : term52 m' n m p' q'.
Proof. exact (@lem184192 m' n m p' q'). Qed.
Lemma lem184194 (m' : nat) (n : nat) (m : nat) (p' : Prop) (q' : Prop) : (term52 m' n m p' q') = (term53 m' n m p' q').
Proof. exact (eq_refl (term52 m' n m p' q')). Qed.
Lemma lem184195 (m' : nat) (n : nat) (m : nat) (p' : Prop) (q' : Prop) : term53 m' n m p' q'.
Proof. exact (EQ_MP (@lem184194 m' n m p' q') (@lem184193 m' n m p' q')). Qed.
Lemma lem184198 (n : nat) (m' : nat) : (n = (term35 m')) = (n = (term35 m')).
Proof. exact (eq_refl (n = (term35 m'))). Qed.
Lemma lem184199 (m : nat) (n : nat) (m' : nat) (q' : Prop) : term54 m n m' q'.
Proof. exact (@lem184195 m' n m (n = (term35 m')) q'). Qed.
Lemma lem184200 (m : nat) (n : nat) (m' : nat) (q' : Prop) : term55 m n m' q'.
Proof. exact (@lem184199 m n m' q' (@lem184198 n m')). Qed.
Lemma lem184205 (n : nat) (m' : nat) (h1 : n = (term35 m')) : n = (term35 m').
Proof. exact (h1). Qed.
Lemma lem184206 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem184207 (m : nat) (n : nat) (m' : nat) (h1 : n = (term35 m')) : (Nat.modulo m n) = (term56 m m').
Proof. exact (MK_COMB (@lem184206 m) (@lem184205 n m' h1)). Qed.
Lemma lem184208 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem184209 (m : nat) (n : nat) (m' : nat) (h1 : n = (term35 m')) : (term57 m n) = (term58 m m').
Proof. exact (MK_COMB (@lem184208) (@lem184207 m n m' h1)). Qed.
Lemma lem184210 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem184211 (m : nat) (n : nat) (m' : nat) (h1 : n = (term35 m')) : (term17 m n) = (term60 m m').
Proof. exact (MK_COMB (@lem184209 m n m' h1) (@lem184210)). Qed.
Lemma lem184213 (p : nat) (m : nat) (n : nat) : (term5 m p n) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem184102 p m n) (@lem184101 m n p)). Qed.
Lemma lem184214 (m' : nat) (m : nat) : (term60 m m') = (term18 m).
Proof. exact (@lem184213 m' m term59). Qed.
Lemma lem184215 (m : nat) (n : nat) (m' : nat) (h1 : n = (term35 m')) : (term17 m n) = (term18 m).
Proof. exact (TRANS (@lem184211 m n m' h1) (@lem184214 m' m)). Qed.
Lemma lem184216 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem184217 (m : nat) (n : nat) (m' : nat) (h1 : n = (term35 m')) : (term61 m n) = (term62 m).
Proof. exact (MK_COMB (@lem184216) (@lem184215 m n m' h1)). Qed.
Lemma lem184218 (m : nat) : (term18 m) = (term18 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem184219 (m : nat) (n : nat) (m' : nat) (h1 : n = (term35 m')) : ((term17 m n) = (term18 m)) = ((term18 m) = (term18 m)).
Proof. exact (MK_COMB (@lem184217 m n m' h1) (@lem184218 m)). Qed.
Lemma lem184221 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem184222 (x : nat) : (x = x) = True.
Proof. exact (@lem184221 nat x). Qed.
Lemma lem184223 (m : nat) : ((term18 m) = (term18 m)) = True.
Proof. exact (@lem184222 (term18 m)). Qed.
Lemma lem184224 (m : nat) (n : nat) (m' : nat) (h1 : n = (term35 m')) : ((term17 m n) = (term18 m)) = True.
Proof. exact (TRANS (@lem184219 m n m' h1) (@lem184223 m)). Qed.
Lemma lem184225 (m' : nat) (n : nat) (m : nat) : term63 m' n m.
Proof. exact (fun h0 : n = (term35 m') => @lem184224 m n m' h0). Qed.
Lemma lem184226 (m : nat) (n : nat) (m' : nat) : term64 m n m'.
Proof. exact (@lem184200 m n m' True). Qed.
Lemma lem184227 (m : nat) (n : nat) (m' : nat) : (term45 m' n m) = (term65 n m').
Proof. exact (@lem184226 m n m' (@lem184225 m' n m)). Qed.
Lemma lem184231 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem184232 (n : nat) (m' : nat) : (term65 n m') = True.
Proof. exact (@lem184231 (n = (term35 m'))). Qed.
Lemma lem184233 (m' : nat) (n : nat) (m : nat) : (term45 m' n m) = True.
Proof. exact (TRANS (@lem184227 m n m') (@lem184232 n m')). Qed.
Lemma lem184234 (n : nat) (m : nat) : (term47 n m) = term66.
Proof. exact (fun_ext (fun m' : nat => @lem184233 m' n m)). Qed.
Lemma lem184235 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem184236 (n : nat) (m : nat) : (term48 n m) = term67.
Proof. exact (MK_COMB (@lem184235) (@lem184234 n m)). Qed.
Lemma lem184238 {A : Type'} (t : Prop) : (term68 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem184239 (t : Prop) : (term69 t) = t.
Proof. exact (@lem184238 nat t). Qed.
Lemma lem184240 : term67 = True.
Proof. exact (@lem184239 True). Qed.
Lemma lem184241 (n : nat) (m : nat) : (term48 n m) = True.
Proof. exact (TRANS (@lem184236 n m) (@lem184240)). Qed.
Lemma lem184242 (n : nat) (m : nat) : (term28 n m) = True.
Proof. exact (TRANS (@lem184176 n m) (@lem184241 n m)). Qed.
Lemma lem184243 (n : nat) (m : nat) : (term27 n m) = True.
Proof. exact (TRANS (@lem184152 n m) (@lem184242 n m)). Qed.
Lemma lem184244 (m : nat) : (term70 m) = term66.
Proof. exact (fun_ext (fun n : nat => @lem184243 n m)). Qed.
Lemma lem184245 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem184246 (m : nat) : (term71 m) = term67.
Proof. exact (MK_COMB (@lem184245) (@lem184244 m)). Qed.
Lemma lem184248 {A : Type'} (t : Prop) : (term68 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem184249 (t : Prop) : (term69 t) = t.
Proof. exact (@lem184248 nat t). Qed.
Lemma lem184250 : term67 = True.
Proof. exact (@lem184249 True). Qed.
Lemma lem184251 (m : nat) : (term71 m) = True.
Proof. exact (TRANS (@lem184246 m) (@lem184250)). Qed.
Lemma lem184252 : term72 = term66.
Proof. exact (fun_ext (fun m : nat => @lem184251 m)). Qed.
Lemma lem184253 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem184254 : term73 = term67.
Proof. exact (MK_COMB (@lem184253) (@lem184252)). Qed.
Lemma lem184256 {A : Type'} (t : Prop) : (term68 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem184257 (t : Prop) : (term69 t) = t.
Proof. exact (@lem184256 nat t). Qed.
Lemma lem184258 : term67 = True.
Proof. exact (@lem184257 True). Qed.
Lemma lem184259 : term73 = True.
Proof. exact (TRANS (@lem184254) (@lem184258)). Qed.
Lemma lem184260 : True = term73.
Proof. exact (SYM (@lem184259)). Qed.
Lemma lem184261 : term73.
Proof. exact (EQ_MP (@lem184260) (@lem0)). Qed.
