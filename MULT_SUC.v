Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MULT_SUC_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm80977_spec.
Lemma lem81123 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem81124 : term1.
Proof. exact (@lem81123 term2). Qed.
Lemma lem81125 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem81126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem81127 : term5 = term6.
Proof. exact (MK_COMB (@lem81126) (@lem81125)). Qed.
Lemma lem81128 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem81129 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem81130 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem81129) (@lem81128 m)). Qed.
Lemma lem81131 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem81132 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem81130 m) (@lem81131 m)). Qed.
Lemma lem81133 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem81132 m)). Qed.
Lemma lem81134 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81135 : term17 = term18.
Proof. exact (MK_COMB (@lem81134) (@lem81133)). Qed.
Lemma lem81136 : term19 = term20.
Proof. exact (MK_COMB (@lem81127) (@lem81135)). Qed.
Lemma lem81137 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem81138 : term21 = term22.
Proof. exact (MK_COMB (@lem81137) (@lem81136)). Qed.
Lemma lem81139 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem81140 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem81139 m)). Qed.
Lemma lem81141 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81142 : term24 = term25.
Proof. exact (MK_COMB (@lem81141) (@lem81140)). Qed.
Lemma lem81143 : term1 = term26.
Proof. exact (MK_COMB (@lem81138) (@lem81142)). Qed.
Lemma lem81144 : term26.
Proof. exact (EQ_MP (@lem81143) (@lem81124)). Qed.
Lemma lem81145 (m : nat) (h1 : term8 m) : term8 m.
Proof. exact (h1). Qed.
Lemma lem81175 : term27.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem81176 (n : nat) : term28 n.
Proof. exact (@lem81175 n). Qed.
Lemma lem81177 (n : nat) : (term28 n) = ((term29 n) = n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem81186 : term30.
Proof. exact (proj1 (@lem80977)). Qed.
Lemma lem81187 (n : nat) : term31 n.
Proof. exact (@lem81186 n). Qed.
Lemma lem81188 (n : nat) : (term31 n) = ((term32 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term31 n)). Qed.
Lemma lem81197 (n : nat) : (term32 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem81188 n) (@lem81187 n)). Qed.
Lemma lem81198 (n : nat) : (term33 n) = (NUMERAL 0).
Proof. exact (@lem81197 (S n)). Qed.
Lemma lem81199 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem81200 (n : nat) : (term34 n) = term35.
Proof. exact (MK_COMB (@lem81199) (@lem81198 n)). Qed.
Lemma lem81202 (n : nat) : (term29 n) = n.
Proof. exact (EQ_MP (@lem81177 n) (@lem81176 n)). Qed.
Lemma lem81203 (n : nat) : (term36 n) = (term32 n).
Proof. exact (@lem81202 (term32 n)). Qed.
Lemma lem81205 (n : nat) : (term32 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem81188 n) (@lem81187 n)). Qed.
Lemma lem81206 (n : nat) : (term36 n) = (NUMERAL 0).
Proof. exact (TRANS (@lem81203 n) (@lem81205 n)). Qed.
Lemma lem81207 (n : nat) : ((term33 n) = (term36 n)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem81200 n) (@lem81206 n)). Qed.
Lemma lem81209 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem81210 (x : nat) : (x = x) = True.
Proof. exact (@lem81209 nat x). Qed.
Lemma lem81211 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem81210 (NUMERAL 0)). Qed.
Lemma lem81212 (n : nat) : ((term33 n) = (term36 n)) = True.
Proof. exact (TRANS (@lem81207 n) (@lem81211)). Qed.
Lemma lem81213 : term37 = term38.
Proof. exact (fun_ext (fun n : nat => @lem81212 n)). Qed.
Lemma lem81214 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81215 : term4 = term39.
Proof. exact (MK_COMB (@lem81214) (@lem81213)). Qed.
Lemma lem81217 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem81218 (t : Prop) : (term41 t) = t.
Proof. exact (@lem81217 nat t). Qed.
Lemma lem81219 : term39 = True.
Proof. exact (@lem81218 True). Qed.
Lemma lem81220 : term4 = True.
Proof. exact (TRANS (@lem81215) (@lem81219)). Qed.
Lemma lem81221 : True = term4.
Proof. exact (SYM (@lem81220)). Qed.
Lemma lem81222 : term4.
Proof. exact (EQ_MP (@lem81221) (@lem0)). Qed.
Lemma lem81223 (m : nat) : term42 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem81224 (m : nat) : (term42 m) = (term43 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem81225 (m : nat) : term43 m.
Proof. exact (EQ_MP (@lem81224 m) (@lem81223 m)). Qed.
Lemma lem81226 (m : nat) (n : nat) : term44 m n.
Proof. exact (@lem81225 m n). Qed.
Lemma lem81227 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (eq_refl (term44 m n)). Qed.
Lemma lem81228 (m : nat) (n : nat) : term45 m n.
Proof. exact (EQ_MP (@lem81227 m n) (@lem81226 m n)). Qed.
Lemma lem81229 (m : nat) (n : nat) (p : nat) : term46 m n p.
Proof. exact (@lem81228 m n p). Qed.
Lemma lem81230 (m : nat) (n : nat) (p : nat) : (term46 m n p) = ((term47 m n p) = (term48 m n p)).
Proof. exact (eq_refl (term46 m n p)). Qed.
Lemma lem81232 : term49.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem81233 : term50.
Proof. exact (proj2 (@lem81232)). Qed.
Lemma lem81234 : term51.
Proof. exact (proj2 (@lem81233)). Qed.
Lemma lem81235 (m : nat) : term52 m.
Proof. exact (@lem81234 m). Qed.
Lemma lem81236 (m : nat) : (term52 m) = (term53 m).
Proof. exact (eq_refl (term52 m)). Qed.
Lemma lem81237 (m : nat) : term53 m.
Proof. exact (EQ_MP (@lem81236 m) (@lem81235 m)). Qed.
Lemma lem81238 (m : nat) (n : nat) : term54 m n.
Proof. exact (@lem81237 m n). Qed.
Lemma lem81239 (m : nat) (n : nat) : (term54 m n) = ((term55 m n) = (term56 m n)).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem81241 : term57.
Proof. exact (proj1 (@lem81233)). Qed.
Lemma lem81242 (m : nat) : term58 m.
Proof. exact (@lem81241 m). Qed.
Lemma lem81243 (m : nat) : (term58 m) = (term59 m).
Proof. exact (eq_refl (term58 m)). Qed.
Lemma lem81244 (m : nat) : term59 m.
Proof. exact (EQ_MP (@lem81243 m) (@lem81242 m)). Qed.
Lemma lem81245 (m : nat) (n : nat) : term60 m n.
Proof. exact (@lem81244 m n). Qed.
Lemma lem81246 (m : nat) (n : nat) : (term60 m n) = ((term61 m n) = (term56 m n)).
Proof. exact (eq_refl (term60 m n)). Qed.
Lemma lem81256 : term62.
Proof. exact (proj2 (@lem80977)). Qed.
Lemma lem81257 (m : nat) : term63 m.
Proof. exact (@lem81256 m). Qed.
Lemma lem81258 (m : nat) : (term63 m) = (term64 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem81259 (m : nat) : term64 m.
Proof. exact (EQ_MP (@lem81258 m) (@lem81257 m)). Qed.
Lemma lem81260 (m : nat) (n : nat) : term65 m n.
Proof. exact (@lem81259 m n). Qed.
Lemma lem81261 (m : nat) (n : nat) : (term65 m n) = ((term66 m n) = (term67 m n)).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem81267 (n : nat) (m : nat) (h1 : term8 m) : term68 m n.
Proof. exact (@lem81145 m h1 n). Qed.
Lemma lem81268 (m : nat) (n : nat) : (term68 m n) = ((term69 m n) = (term70 m n)).
Proof. exact (eq_refl (term68 m n)). Qed.
Lemma lem81277 (m : nat) (n : nat) : (term66 m n) = (term67 m n).
Proof. exact (EQ_MP (@lem81261 m n) (@lem81260 m n)). Qed.
Lemma lem81278 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (@lem81277 m (S n)). Qed.
Lemma lem81280 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (EQ_MP (@lem81239 m n) (@lem81238 m n)). Qed.
Lemma lem81281 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (@lem81280 (term69 m n) n). Qed.
Lemma lem81282 (m : nat) (n : nat) : (term71 m n) = (term73 m n).
Proof. exact (TRANS (@lem81278 m n) (@lem81281 m n)). Qed.
Lemma lem81284 (n : nat) (m : nat) (h1 : term8 m) : (term69 m n) = (term70 m n).
Proof. exact (EQ_MP (@lem81268 m n) (@lem81267 n m h1)). Qed.
Lemma lem81285 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem81286 (n : nat) (m : nat) (h1 : term8 m) : (term74 m n) = (term75 m n).
Proof. exact (MK_COMB (@lem81285) (@lem81284 n m h1)). Qed.
Lemma lem81287 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem81288 (n : nat) (m : nat) (h1 : term8 m) : (term76 m n) = (term77 m n).
Proof. exact (MK_COMB (@lem81286 n m h1) (@lem81287 n)). Qed.
Lemma lem81289 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem81290 (n : nat) (m : nat) (h1 : term8 m) : (term73 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem81289) (@lem81288 n m h1)). Qed.
Lemma lem81291 (n : nat) (m : nat) (h1 : term8 m) : (term71 m n) = (term78 m n).
Proof. exact (TRANS (@lem81282 m n) (@lem81290 n m h1)). Qed.
Lemma lem81292 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem81293 (n : nat) (m : nat) (h1 : term8 m) : (term79 m n) = (term80 m n).
Proof. exact (MK_COMB (@lem81292) (@lem81291 n m h1)). Qed.
Lemma lem81295 (m : nat) (n : nat) : (term61 m n) = (term56 m n).
Proof. exact (EQ_MP (@lem81246 m n) (@lem81245 m n)). Qed.
Lemma lem81296 (m : nat) (n : nat) : (term81 m n) = (term82 m n).
Proof. exact (@lem81295 m (term66 m n)). Qed.
Lemma lem81298 (m : nat) (n : nat) : (term66 m n) = (term67 m n).
Proof. exact (EQ_MP (@lem81261 m n) (@lem81260 m n)). Qed.
Lemma lem81299 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem81300 (m : nat) (n : nat) : (term83 m n) = (term84 m n).
Proof. exact (MK_COMB (@lem81299 m) (@lem81298 m n)). Qed.
Lemma lem81302 (m : nat) (n : nat) (p : nat) : (term47 m n p) = (term48 m n p).
Proof. exact (EQ_MP (@lem81230 m n p) (@lem81229 m n p)). Qed.
Lemma lem81303 (m : nat) (n : nat) : (term84 m n) = (term77 m n).
Proof. exact (@lem81302 m (Nat.mul m n) n). Qed.
Lemma lem81304 (m : nat) (n : nat) : (term83 m n) = (term77 m n).
Proof. exact (TRANS (@lem81300 m n) (@lem81303 m n)). Qed.
Lemma lem81305 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem81306 (m : nat) (n : nat) : (term82 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem81305) (@lem81304 m n)). Qed.
Lemma lem81307 (m : nat) (n : nat) : (term81 m n) = (term78 m n).
Proof. exact (TRANS (@lem81296 m n) (@lem81306 m n)). Qed.
Lemma lem81308 (n : nat) (m : nat) (h1 : term8 m) : ((term71 m n) = (term81 m n)) = ((term78 m n) = (term78 m n)).
Proof. exact (MK_COMB (@lem81293 n m h1) (@lem81307 m n)). Qed.
Lemma lem81310 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem81311 (x : nat) : (x = x) = True.
Proof. exact (@lem81310 nat x). Qed.
Lemma lem81312 (m : nat) (n : nat) : ((term78 m n) = (term78 m n)) = True.
Proof. exact (@lem81311 (term78 m n)). Qed.
Lemma lem81313 (n : nat) (m : nat) (h1 : term8 m) : ((term71 m n) = (term81 m n)) = True.
Proof. exact (TRANS (@lem81308 n m h1) (@lem81312 m n)). Qed.
Lemma lem81314 (m : nat) (h1 : term8 m) : (term85 m) = term38.
Proof. exact (fun_ext (fun n : nat => @lem81313 n m h1)). Qed.
Lemma lem81315 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81316 (m : nat) (h1 : term8 m) : (term12 m) = term39.
Proof. exact (MK_COMB (@lem81315) (@lem81314 m h1)). Qed.
Lemma lem81318 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem81319 (t : Prop) : (term41 t) = t.
Proof. exact (@lem81318 nat t). Qed.
Lemma lem81320 : term39 = True.
Proof. exact (@lem81319 True). Qed.
Lemma lem81321 (m : nat) (h1 : term8 m) : (term12 m) = True.
Proof. exact (TRANS (@lem81316 m h1) (@lem81320)). Qed.
Lemma lem81322 (m : nat) (h1 : term8 m) : True = (term12 m).
Proof. exact (SYM (@lem81321 m h1)). Qed.
Lemma lem81323 (m : nat) (h1 : term8 m) : term12 m.
Proof. exact (EQ_MP (@lem81322 m h1) (@lem0)). Qed.
Lemma lem81324 (m : nat) : term14 m.
Proof. exact (fun h0 : term8 m => @lem81323 m h0). Qed.
Lemma lem81329 : term18.
Proof. exact (fun m : nat => @lem81324 m). Qed.
Lemma lem81330 : term20.
Proof. exact (conj (@lem81222) (@lem81329)). Qed.
Lemma lem81331 : term25.
Proof. exact (@lem81144 (@lem81330)). Qed.
