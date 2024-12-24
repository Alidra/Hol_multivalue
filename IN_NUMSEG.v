Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_NUMSEG_term_abbrevs.
Require Import numseg_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem5371168 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5371169 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem5371168 _83095 p). Qed.
Lemma lem5371170 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem5371171 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem5371170 _83095 p) (@lem5371169 _83095 p)). Qed.
Lemma lem5371172 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem5371171 _83095 p x). Qed.
Lemma lem5371173 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem5371182 (m : nat) : term5 m.
Proof. exact (@lem5329077 m). Qed.
Lemma lem5371183 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem5371184 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem5371183 m) (@lem5371182 m)). Qed.
Lemma lem5371185 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem5371184 m n). Qed.
Lemma lem5371186 (m : nat) (n : nat) : (term7 m n) = ((dotdot m n) = (term8 m n)).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem5371203 (m : nat) (n : nat) : (dotdot m n) = (term8 m n).
Proof. exact (EQ_MP (@lem5371186 m n) (@lem5371185 m n)). Qed.
Lemma lem5371210 (p : nat) : (@IN nat p) = (@IN nat p).
Proof. exact (eq_refl (@IN nat p)). Qed.
Lemma lem5371211 (p : nat) (m : nat) (n : nat) : (term9 p m n) = (term10 p m n).
Proof. exact (MK_COMB (@lem5371210 p) (@lem5371203 m n)). Qed.
Lemma lem5371213 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5371173 _83095 p x) (@lem5371172 _83095 p x)). Qed.
Lemma lem5371214 (p : nat -> Prop) (x : nat) : (term11 x p) = (p x).
Proof. exact (@lem5371213 nat p x). Qed.
Lemma lem5371215 (m : nat) (n : nat) (p : nat) : (term12 p m n) = (term13 m n p).
Proof. exact (@lem5371214 (term14 m n) p). Qed.
Lemma lem5371216 (m : nat) (x : nat) (n : nat) : (term13 m n x) = (term15 m x n).
Proof. exact (eq_refl (term13 m n x)). Qed.
Lemma lem5371217 (GEN_PVAR_229 : nat) : (@SETSPEC nat GEN_PVAR_229) = (@SETSPEC nat GEN_PVAR_229).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_229)). Qed.
Lemma lem5371218 (GEN_PVAR_229 : nat) (m : nat) (x : nat) (n : nat) : (term16 GEN_PVAR_229 m n x) = (term17 GEN_PVAR_229 m x n).
Proof. exact (MK_COMB (@lem5371217 GEN_PVAR_229) (@lem5371216 m x n)). Qed.
Lemma lem5371219 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5371220 (GEN_PVAR_229 : nat) (m : nat) (n : nat) (x : nat) : (term18 GEN_PVAR_229 m n x) = (term19 GEN_PVAR_229 m n x).
Proof. exact (MK_COMB (@lem5371218 GEN_PVAR_229 m x n) (@lem5371219 x)). Qed.
Lemma lem5371221 (GEN_PVAR_229 : nat) (m : nat) (n : nat) : (term20 GEN_PVAR_229 m n) = (term21 GEN_PVAR_229 m n).
Proof. exact (fun_ext (fun x : nat => @lem5371220 GEN_PVAR_229 m n x)). Qed.
Lemma lem5371222 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5371223 (GEN_PVAR_229 : nat) (m : nat) (n : nat) : (term22 GEN_PVAR_229 m n) = (term23 GEN_PVAR_229 m n).
Proof. exact (MK_COMB (@lem5371222) (@lem5371221 GEN_PVAR_229 m n)). Qed.
Lemma lem5371224 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (fun_ext (fun GEN_PVAR_229 : nat => @lem5371223 GEN_PVAR_229 m n)). Qed.
Lemma lem5371225 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem5371226 (m : nat) (n : nat) : (term26 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem5371225) (@lem5371224 m n)). Qed.
Lemma lem5371227 (p : nat) : (@IN nat p) = (@IN nat p).
Proof. exact (eq_refl (@IN nat p)). Qed.
Lemma lem5371228 (p : nat) (m : nat) (n : nat) : (term12 p m n) = (term10 p m n).
Proof. exact (MK_COMB (@lem5371227 p) (@lem5371226 m n)). Qed.
Lemma lem5371229 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5371230 (p : nat) (m : nat) (n : nat) : (term27 p m n) = (term28 p m n).
Proof. exact (MK_COMB (@lem5371229) (@lem5371228 p m n)). Qed.
Lemma lem5371231 (m : nat) (p : nat) (n : nat) : (term13 m n p) = (term15 m p n).
Proof. exact (eq_refl (term13 m n p)). Qed.
Lemma lem5371232 (m : nat) (p : nat) (n : nat) : ((term12 p m n) = (term13 m n p)) = ((term10 p m n) = (term15 m p n)).
Proof. exact (MK_COMB (@lem5371230 p m n) (@lem5371231 m p n)). Qed.
Lemma lem5371233 (m : nat) (p : nat) (n : nat) : (term10 p m n) = (term15 m p n).
Proof. exact (EQ_MP (@lem5371232 m p n) (@lem5371215 m n p)). Qed.
Lemma lem5371236 (m : nat) (p : nat) (n : nat) : (term9 p m n) = (term15 m p n).
Proof. exact (TRANS (@lem5371211 p m n) (@lem5371233 m p n)). Qed.
Lemma lem5371237 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5371238 (m : nat) (p : nat) (n : nat) : (term29 p m n) = (term30 m p n).
Proof. exact (MK_COMB (@lem5371237) (@lem5371236 m p n)). Qed.
Lemma lem5371241 (m : nat) (p : nat) (n : nat) : (term15 m p n) = (term15 m p n).
Proof. exact (eq_refl (term15 m p n)). Qed.
Lemma lem5371242 (m : nat) (p : nat) (n : nat) : ((term9 p m n) = (term15 m p n)) = ((term15 m p n) = (term15 m p n)).
Proof. exact (MK_COMB (@lem5371238 m p n) (@lem5371241 m p n)). Qed.
Lemma lem5371244 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5371245 (x : Prop) : (x = x) = True.
Proof. exact (@lem5371244 Prop x). Qed.
Lemma lem5371246 (m : nat) (p : nat) (n : nat) : ((term15 m p n) = (term15 m p n)) = True.
Proof. exact (@lem5371245 (term15 m p n)). Qed.
Lemma lem5371247 (m : nat) (p : nat) (n : nat) : ((term9 p m n) = (term15 m p n)) = True.
Proof. exact (TRANS (@lem5371242 m p n) (@lem5371246 m p n)). Qed.
Lemma lem5371248 (m : nat) (n : nat) : (term31 m n) = term32.
Proof. exact (fun_ext (fun p : nat => @lem5371247 m p n)). Qed.
Lemma lem5371249 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371250 (m : nat) (n : nat) : (term33 m n) = term34.
Proof. exact (MK_COMB (@lem5371249) (@lem5371248 m n)). Qed.
Lemma lem5371252 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5371253 (t : Prop) : (term36 t) = t.
Proof. exact (@lem5371252 nat t). Qed.
Lemma lem5371254 : term34 = True.
Proof. exact (@lem5371253 True). Qed.
Lemma lem5371255 (m : nat) (n : nat) : (term33 m n) = True.
Proof. exact (TRANS (@lem5371250 m n) (@lem5371254)). Qed.
Lemma lem5371256 (m : nat) : (term37 m) = term32.
Proof. exact (fun_ext (fun n : nat => @lem5371255 m n)). Qed.
Lemma lem5371257 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371258 (m : nat) : (term38 m) = term34.
Proof. exact (MK_COMB (@lem5371257) (@lem5371256 m)). Qed.
Lemma lem5371260 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5371261 (t : Prop) : (term36 t) = t.
Proof. exact (@lem5371260 nat t). Qed.
Lemma lem5371262 : term34 = True.
Proof. exact (@lem5371261 True). Qed.
Lemma lem5371263 (m : nat) : (term38 m) = True.
Proof. exact (TRANS (@lem5371258 m) (@lem5371262)). Qed.
Lemma lem5371264 : term39 = term32.
Proof. exact (fun_ext (fun m : nat => @lem5371263 m)). Qed.
Lemma lem5371265 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371266 : term40 = term34.
Proof. exact (MK_COMB (@lem5371265) (@lem5371264)). Qed.
Lemma lem5371268 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5371269 (t : Prop) : (term36 t) = t.
Proof. exact (@lem5371268 nat t). Qed.
Lemma lem5371270 : term34 = True.
Proof. exact (@lem5371269 True). Qed.
Lemma lem5371271 : term40 = True.
Proof. exact (TRANS (@lem5371266) (@lem5371270)). Qed.
Lemma lem5371272 : True = term40.
Proof. exact (SYM (@lem5371271)). Qed.
Lemma lem5371273 : term40.
Proof. exact (EQ_MP (@lem5371272) (@lem0)). Qed.
