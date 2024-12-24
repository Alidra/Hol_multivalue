Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MULT_ASSOC_term_abbrevs.
Require Import MULT_CLAUSES_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem82130 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem82131 : term1.
Proof. exact (@lem82130 term2). Qed.
Lemma lem82132 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem82133 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem82134 : term5 = term6.
Proof. exact (MK_COMB (@lem82133) (@lem82132)). Qed.
Lemma lem82135 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem82136 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem82137 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem82136) (@lem82135 m)). Qed.
Lemma lem82138 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem82139 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem82137 m) (@lem82138 m)). Qed.
Lemma lem82140 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem82139 m)). Qed.
Lemma lem82141 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82142 : term17 = term18.
Proof. exact (MK_COMB (@lem82141) (@lem82140)). Qed.
Lemma lem82143 : term19 = term20.
Proof. exact (MK_COMB (@lem82134) (@lem82142)). Qed.
Lemma lem82144 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem82145 : term21 = term22.
Proof. exact (MK_COMB (@lem82144) (@lem82143)). Qed.
Lemma lem82146 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem82147 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem82146 m)). Qed.
Lemma lem82148 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82149 : term24 = term25.
Proof. exact (MK_COMB (@lem82148) (@lem82147)). Qed.
Lemma lem82150 : term1 = term26.
Proof. exact (MK_COMB (@lem82145) (@lem82149)). Qed.
Lemma lem82151 : term26.
Proof. exact (EQ_MP (@lem82150) (@lem82131)). Qed.
Lemma lem82152 (m : nat) (h1 : term8 m) : term8 m.
Proof. exact (h1). Qed.
Lemma lem82192 : term27.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem82193 (n : nat) : term28 n.
Proof. exact (@lem82192 n). Qed.
Lemma lem82194 (n : nat) : (term28 n) = ((term29 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem82207 (n : nat) : (term29 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem82194 n) (@lem82193 n)). Qed.
Lemma lem82208 (n : nat) (p : nat) : (term30 n p) = (NUMERAL 0).
Proof. exact (@lem82207 (Nat.mul n p)). Qed.
Lemma lem82209 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem82210 (n : nat) (p : nat) : (term31 n p) = term32.
Proof. exact (MK_COMB (@lem82209) (@lem82208 n p)). Qed.
Lemma lem82212 (n : nat) : (term29 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem82194 n) (@lem82193 n)). Qed.
Lemma lem82213 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem82214 (n : nat) : (term33 n) = term34.
Proof. exact (MK_COMB (@lem82213) (@lem82212 n)). Qed.
Lemma lem82215 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem82216 (n : nat) (p : nat) : (term35 n p) = (term29 p).
Proof. exact (MK_COMB (@lem82214 n) (@lem82215 p)). Qed.
Lemma lem82218 (n : nat) : (term29 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem82194 n) (@lem82193 n)). Qed.
Lemma lem82219 (p : nat) : (term29 p) = (NUMERAL 0).
Proof. exact (@lem82218 p). Qed.
Lemma lem82220 (n : nat) (p : nat) : (term35 n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem82216 n p) (@lem82219 p)). Qed.
Lemma lem82221 (n : nat) (p : nat) : ((term30 n p) = (term35 n p)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem82210 n p) (@lem82220 n p)). Qed.
Lemma lem82223 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem82224 (x : nat) : (x = x) = True.
Proof. exact (@lem82223 nat x). Qed.
Lemma lem82225 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem82224 (NUMERAL 0)). Qed.
Lemma lem82226 (n : nat) (p : nat) : ((term30 n p) = (term35 n p)) = True.
Proof. exact (TRANS (@lem82221 n p) (@lem82225)). Qed.
Lemma lem82227 (n : nat) : (term36 n) = term37.
Proof. exact (fun_ext (fun p : nat => @lem82226 n p)). Qed.
Lemma lem82228 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82229 (n : nat) : (term38 n) = term39.
Proof. exact (MK_COMB (@lem82228) (@lem82227 n)). Qed.
Lemma lem82231 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem82232 (t : Prop) : (term41 t) = t.
Proof. exact (@lem82231 nat t). Qed.
Lemma lem82233 : term39 = True.
Proof. exact (@lem82232 True). Qed.
Lemma lem82234 (n : nat) : (term38 n) = True.
Proof. exact (TRANS (@lem82229 n) (@lem82233)). Qed.
Lemma lem82235 : term42 = term37.
Proof. exact (fun_ext (fun n : nat => @lem82234 n)). Qed.
Lemma lem82236 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82237 : term4 = term39.
Proof. exact (MK_COMB (@lem82236) (@lem82235)). Qed.
Lemma lem82239 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem82240 (t : Prop) : (term41 t) = t.
Proof. exact (@lem82239 nat t). Qed.
Lemma lem82241 : term39 = True.
Proof. exact (@lem82240 True). Qed.
Lemma lem82242 : term4 = True.
Proof. exact (TRANS (@lem82237) (@lem82241)). Qed.
Lemma lem82243 : True = term4.
Proof. exact (SYM (@lem82242)). Qed.
Lemma lem82244 : term4.
Proof. exact (EQ_MP (@lem82243) (@lem0)). Qed.
Lemma lem82245 (m : nat) : term43 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem82246 (m : nat) : (term43 m) = (term44 m).
Proof. exact (eq_refl (term43 m)). Qed.
Lemma lem82247 (m : nat) : term44 m.
Proof. exact (EQ_MP (@lem82246 m) (@lem82245 m)). Qed.
Lemma lem82248 (m : nat) (n : nat) : term45 m n.
Proof. exact (@lem82247 m n). Qed.
Lemma lem82249 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (eq_refl (term45 m n)). Qed.
Lemma lem82250 (m : nat) (n : nat) : term46 m n.
Proof. exact (EQ_MP (@lem82249 m n) (@lem82248 m n)). Qed.
Lemma lem82251 (m : nat) (n : nat) (p : nat) : term47 m n p.
Proof. exact (@lem82250 m n p). Qed.
Lemma lem82252 (m : nat) (n : nat) (p : nat) : (term47 m n p) = ((term48 m n p) = (term49 m n p)).
Proof. exact (eq_refl (term47 m n p)). Qed.
Lemma lem82254 : term50.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem82255 : term51.
Proof. exact (proj2 (@lem82254)). Qed.
Lemma lem82256 : term52.
Proof. exact (proj2 (@lem82255)). Qed.
Lemma lem82257 : term53.
Proof. exact (proj2 (@lem82256)). Qed.
Lemma lem82265 : term54.
Proof. exact (proj1 (@lem82257)). Qed.
Lemma lem82266 (m : nat) : term55 m.
Proof. exact (@lem82265 m). Qed.
Lemma lem82267 (m : nat) : (term55 m) = (term56 m).
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem82268 (m : nat) : term56 m.
Proof. exact (EQ_MP (@lem82267 m) (@lem82266 m)). Qed.
Lemma lem82269 (m : nat) (n : nat) : term57 m n.
Proof. exact (@lem82268 m n). Qed.
Lemma lem82270 (m : nat) (n : nat) : (term57 m n) = ((term58 m n) = (term59 m n)).
Proof. exact (eq_refl (term57 m n)). Qed.
Lemma lem82288 (n : nat) (m : nat) (h1 : term8 m) : term60 m n.
Proof. exact (@lem82152 m h1 n). Qed.
Lemma lem82289 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (eq_refl (term60 m n)). Qed.
Lemma lem82290 (n : nat) (m : nat) (h1 : term8 m) : term61 m n.
Proof. exact (EQ_MP (@lem82289 m n) (@lem82288 n m h1)). Qed.
Lemma lem82291 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : term62 m n p.
Proof. exact (@lem82290 n m h1 p). Qed.
Lemma lem82292 (m : nat) (n : nat) (p : nat) : (term62 m n p) = ((term63 m n p) = (term64 m n p)).
Proof. exact (eq_refl (term62 m n p)). Qed.
Lemma lem82305 (m : nat) (n : nat) : (term58 m n) = (term59 m n).
Proof. exact (EQ_MP (@lem82270 m n) (@lem82269 m n)). Qed.
Lemma lem82306 (m : nat) (n : nat) (p : nat) : (term65 m n p) = (term66 m n p).
Proof. exact (@lem82305 m (Nat.mul n p)). Qed.
Lemma lem82308 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (term63 m n p) = (term64 m n p).
Proof. exact (EQ_MP (@lem82292 m n p) (@lem82291 n p m h1)). Qed.
Lemma lem82309 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem82310 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (term67 m n p) = (term68 m n p).
Proof. exact (MK_COMB (@lem82309) (@lem82308 n p m h1)). Qed.
Lemma lem82311 (n : nat) (p : nat) : (Nat.mul n p) = (Nat.mul n p).
Proof. exact (eq_refl (Nat.mul n p)). Qed.
Lemma lem82312 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (term66 m n p) = (term69 m n p).
Proof. exact (MK_COMB (@lem82310 n p m h1) (@lem82311 n p)). Qed.
Lemma lem82313 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (term65 m n p) = (term69 m n p).
Proof. exact (TRANS (@lem82306 m n p) (@lem82312 n p m h1)). Qed.
Lemma lem82314 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem82315 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (term70 m n p) = (term71 m n p).
Proof. exact (MK_COMB (@lem82314) (@lem82313 n p m h1)). Qed.
Lemma lem82317 (m : nat) (n : nat) : (term58 m n) = (term59 m n).
Proof. exact (EQ_MP (@lem82270 m n) (@lem82269 m n)). Qed.
Lemma lem82318 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem82319 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (MK_COMB (@lem82318) (@lem82317 m n)). Qed.
Lemma lem82320 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem82321 (m : nat) (n : nat) (p : nat) : (term74 m n p) = (term75 m n p).
Proof. exact (MK_COMB (@lem82319 m n) (@lem82320 p)). Qed.
Lemma lem82323 (m : nat) (n : nat) (p : nat) : (term48 m n p) = (term49 m n p).
Proof. exact (EQ_MP (@lem82252 m n p) (@lem82251 m n p)). Qed.
Lemma lem82324 (m : nat) (n : nat) (p : nat) : (term75 m n p) = (term69 m n p).
Proof. exact (@lem82323 (Nat.mul m n) n p). Qed.
Lemma lem82325 (m : nat) (n : nat) (p : nat) : (term74 m n p) = (term69 m n p).
Proof. exact (TRANS (@lem82321 m n p) (@lem82324 m n p)). Qed.
Lemma lem82326 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : ((term65 m n p) = (term74 m n p)) = ((term69 m n p) = (term69 m n p)).
Proof. exact (MK_COMB (@lem82315 n p m h1) (@lem82325 m n p)). Qed.
Lemma lem82328 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem82329 (x : nat) : (x = x) = True.
Proof. exact (@lem82328 nat x). Qed.
Lemma lem82330 (m : nat) (n : nat) (p : nat) : ((term69 m n p) = (term69 m n p)) = True.
Proof. exact (@lem82329 (term69 m n p)). Qed.
Lemma lem82331 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : ((term65 m n p) = (term74 m n p)) = True.
Proof. exact (TRANS (@lem82326 n p m h1) (@lem82330 m n p)). Qed.
Lemma lem82332 (n : nat) (m : nat) (h1 : term8 m) : (term76 m n) = term37.
Proof. exact (fun_ext (fun p : nat => @lem82331 n p m h1)). Qed.
Lemma lem82333 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82334 (n : nat) (m : nat) (h1 : term8 m) : (term77 m n) = term39.
Proof. exact (MK_COMB (@lem82333) (@lem82332 n m h1)). Qed.
Lemma lem82336 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem82337 (t : Prop) : (term41 t) = t.
Proof. exact (@lem82336 nat t). Qed.
Lemma lem82338 : term39 = True.
Proof. exact (@lem82337 True). Qed.
Lemma lem82339 (n : nat) (m : nat) (h1 : term8 m) : (term77 m n) = True.
Proof. exact (TRANS (@lem82334 n m h1) (@lem82338)). Qed.
Lemma lem82340 (m : nat) (h1 : term8 m) : (term78 m) = term37.
Proof. exact (fun_ext (fun n : nat => @lem82339 n m h1)). Qed.
Lemma lem82341 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82342 (m : nat) (h1 : term8 m) : (term12 m) = term39.
Proof. exact (MK_COMB (@lem82341) (@lem82340 m h1)). Qed.
Lemma lem82344 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem82345 (t : Prop) : (term41 t) = t.
Proof. exact (@lem82344 nat t). Qed.
Lemma lem82346 : term39 = True.
Proof. exact (@lem82345 True). Qed.
Lemma lem82347 (m : nat) (h1 : term8 m) : (term12 m) = True.
Proof. exact (TRANS (@lem82342 m h1) (@lem82346)). Qed.
Lemma lem82348 (m : nat) (h1 : term8 m) : True = (term12 m).
Proof. exact (SYM (@lem82347 m h1)). Qed.
Lemma lem82349 (m : nat) (h1 : term8 m) : term12 m.
Proof. exact (EQ_MP (@lem82348 m h1) (@lem0)). Qed.
Lemma lem82350 (m : nat) : term14 m.
Proof. exact (fun h0 : term8 m => @lem82349 m h0). Qed.
Lemma lem82355 : term18.
Proof. exact (fun m : nat => @lem82350 m). Qed.
Lemma lem82356 : term20.
Proof. exact (conj (@lem82244) (@lem82355)). Qed.
Lemma lem82357 : term25.
Proof. exact (@lem82151 (@lem82356)). Qed.
