Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7640378_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm1843_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm7631335_spec.
Require Import thm7637143_spec.
Require Import thm7637144_spec.
Require Import thm7637146_spec.
Require Import thm7637147_spec.
Require Import thm7637176_spec.
Require Import thm7637177_spec.
Lemma lem7637208 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term0 A B f s n.
Proof. exact (EQ_MP (@lem7637177 A B f s n) (@lem7637176 A B f s n)). Qed.
Lemma lem7637209 {M N : Type'} (f : type1559 M N) (s : nat -> Prop) (n : nat) : term1 M N f s n.
Proof. exact (@lem7637208 nat (finite_sum M N) f s n). Qed.
Lemma lem7637210 {M N : Type'} : term2 M N.
Proof. exact (@lem7637209 M N (@mk_finite_sum M N) (term3 M N) (term4 M N)). Qed.
Lemma lem7637226 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7637147 A s) (@lem7637146 A s)). Qed.
Lemma lem7637227 {M : Type'} (s : M -> Prop) : (@dimindex M s) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7637226 M s). Qed.
Lemma lem7637228 {M : Type'} : (@dimindex M (@UNIV M)) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7637227 M (@UNIV M)). Qed.
Lemma lem7637229 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem7637230 {M : Type'} : (term5 M) = (term5 M).
Proof. exact (MK_COMB (@lem7637229) (@lem7637228 M)). Qed.
Lemma lem7637232 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7637147 A s) (@lem7637146 A s)). Qed.
Lemma lem7637233 {N : Type'} (s : N -> Prop) : (@dimindex N s) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7637232 N s). Qed.
Lemma lem7637234 {N : Type'} : (@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7637233 N (@UNIV N)). Qed.
Lemma lem7637235 {M N : Type'} : (term4 M N) = (term4 M N).
Proof. exact (MK_COMB (@lem7637230 M) (@lem7637234 N)). Qed.
Lemma lem7637236 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem7637237 {M N : Type'} : (term3 M N) = (term3 M N).
Proof. exact (MK_COMB (@lem7637236) (@lem7637235 M N)). Qed.
Lemma lem7637238 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem7637239 {M N : Type'} (x : nat) : (term7 M N x) = (term7 M N x).
Proof. exact (MK_COMB (@lem7637238 x) (@lem7637237 M N)). Qed.
Lemma lem7637240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7637241 {M N : Type'} (x : nat) : (term8 M N x) = (term8 M N x).
Proof. exact (MK_COMB (@lem7637240) (@lem7637239 M N x)). Qed.
Lemma lem7637245 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7637147 A s) (@lem7637146 A s)). Qed.
Lemma lem7637246 {M : Type'} (s : M -> Prop) : (@dimindex M s) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7637245 M s). Qed.
Lemma lem7637247 {M : Type'} : (@dimindex M (@UNIV M)) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7637246 M (@UNIV M)). Qed.
Lemma lem7637248 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem7637249 {M : Type'} : (term5 M) = (term5 M).
Proof. exact (MK_COMB (@lem7637248) (@lem7637247 M)). Qed.
Lemma lem7637251 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7637147 A s) (@lem7637146 A s)). Qed.
Lemma lem7637252 {N : Type'} (s : N -> Prop) : (@dimindex N s) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7637251 N s). Qed.
Lemma lem7637253 {N : Type'} : (@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7637252 N (@UNIV N)). Qed.
Lemma lem7637254 {M N : Type'} : (term4 M N) = (term4 M N).
Proof. exact (MK_COMB (@lem7637249 M) (@lem7637253 N)). Qed.
Lemma lem7637255 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem7637256 {M N : Type'} : (term3 M N) = (term3 M N).
Proof. exact (MK_COMB (@lem7637255) (@lem7637254 M N)). Qed.
Lemma lem7637257 (y : nat) : (@IN nat y) = (@IN nat y).
Proof. exact (eq_refl (@IN nat y)). Qed.
Lemma lem7637258 {M N : Type'} (y : nat) : (term7 M N y) = (term7 M N y).
Proof. exact (MK_COMB (@lem7637257 y) (@lem7637256 M N)). Qed.
Lemma lem7637259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7637260 {M N : Type'} (y : nat) : (term8 M N y) = (term8 M N y).
Proof. exact (MK_COMB (@lem7637259) (@lem7637258 M N y)). Qed.
Lemma lem7637263 {M N : Type'} (x : nat) (y : nat) : ((@mk_finite_sum M N x) = (@mk_finite_sum M N y)) = ((@mk_finite_sum M N x) = (@mk_finite_sum M N y)).
Proof. exact (eq_refl ((@mk_finite_sum M N x) = (@mk_finite_sum M N y))). Qed.
Lemma lem7637264 {M N : Type'} (x : nat) (y : nat) : (term9 M N x y) = (term9 M N x y).
Proof. exact (MK_COMB (@lem7637260 M N y) (@lem7637263 M N x y)). Qed.
Lemma lem7637265 {M N : Type'} (x : nat) (y : nat) : (term10 M N x y) = (term10 M N x y).
Proof. exact (MK_COMB (@lem7637241 M N x) (@lem7637264 M N x y)). Qed.
Lemma lem7637266 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7637267 {M N : Type'} (x : nat) (y : nat) : (term11 M N x y) = (term11 M N x y).
Proof. exact (MK_COMB (@lem7637266) (@lem7637265 M N x y)). Qed.
Lemma lem7637270 (x : nat) (y : nat) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem7637271 {M N : Type'} (x : nat) (y : nat) : (term12 M N x y) = (term12 M N x y).
Proof. exact (MK_COMB (@lem7637267 M N x y) (@lem7637270 x y)). Qed.
Lemma lem7637272 {M N : Type'} (x : nat) : (term13 M N x) = (term13 M N x).
Proof. exact (fun_ext (fun y : nat => @lem7637271 M N x y)). Qed.
Lemma lem7637273 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7637274 {M N : Type'} (x : nat) : (term14 M N x) = (term14 M N x).
Proof. exact (MK_COMB (@lem7637273) (@lem7637272 M N x)). Qed.
Lemma lem7637275 {M N : Type'} : (term15 M N) = (term15 M N).
Proof. exact (fun_ext (fun x : nat => @lem7637274 M N x)). Qed.
Lemma lem7637276 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7637277 {M N : Type'} : (term16 M N) = (term16 M N).
Proof. exact (MK_COMB (@lem7637276) (@lem7637275 M N)). Qed.
Lemma lem7637278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7637279 {M N : Type'} : (term17 M N) = (term17 M N).
Proof. exact (MK_COMB (@lem7637278) (@lem7637277 M N)). Qed.
Lemma lem7637281 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7637147 A s) (@lem7637146 A s)). Qed.
Lemma lem7637282 {M : Type'} (s : M -> Prop) : (@dimindex M s) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7637281 M s). Qed.
Lemma lem7637283 {M : Type'} : (@dimindex M (@UNIV M)) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7637282 M (@UNIV M)). Qed.
Lemma lem7637284 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem7637285 {M : Type'} : (term5 M) = (term5 M).
Proof. exact (MK_COMB (@lem7637284) (@lem7637283 M)). Qed.
Lemma lem7637287 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7637147 A s) (@lem7637146 A s)). Qed.
Lemma lem7637288 {N : Type'} (s : N -> Prop) : (@dimindex N s) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7637287 N s). Qed.
Lemma lem7637289 {N : Type'} : (@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7637288 N (@UNIV N)). Qed.
Lemma lem7637290 {M N : Type'} : (term4 M N) = (term4 M N).
Proof. exact (MK_COMB (@lem7637285 M) (@lem7637289 N)). Qed.
Lemma lem7637291 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem7637292 {M N : Type'} : (term3 M N) = (term3 M N).
Proof. exact (MK_COMB (@lem7637291) (@lem7637290 M N)). Qed.
Lemma lem7637293 : (@HAS_SIZE nat) = (@HAS_SIZE nat).
Proof. exact (eq_refl (@HAS_SIZE nat)). Qed.
Lemma lem7637294 {M N : Type'} : (term18 M N) = (term18 M N).
Proof. exact (MK_COMB (@lem7637293) (@lem7637292 M N)). Qed.
Lemma lem7637296 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7637147 A s) (@lem7637146 A s)). Qed.
Lemma lem7637297 {M : Type'} (s : M -> Prop) : (@dimindex M s) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7637296 M s). Qed.
Lemma lem7637298 {M : Type'} : (@dimindex M (@UNIV M)) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7637297 M (@UNIV M)). Qed.
Lemma lem7637299 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem7637300 {M : Type'} : (term5 M) = (term5 M).
Proof. exact (MK_COMB (@lem7637299) (@lem7637298 M)). Qed.
Lemma lem7637302 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7637147 A s) (@lem7637146 A s)). Qed.
Lemma lem7637303 {N : Type'} (s : N -> Prop) : (@dimindex N s) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7637302 N s). Qed.
Lemma lem7637304 {N : Type'} : (@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7637303 N (@UNIV N)). Qed.
Lemma lem7637305 {M N : Type'} : (term4 M N) = (term4 M N).
Proof. exact (MK_COMB (@lem7637300 M) (@lem7637304 N)). Qed.
Lemma lem7637306 {M N : Type'} : (term19 M N) = (term19 M N).
Proof. exact (MK_COMB (@lem7637294 M N) (@lem7637305 M N)). Qed.
Lemma lem7637307 {M N : Type'} : (term20 M N) = (term20 M N).
Proof. exact (MK_COMB (@lem7637279 M N) (@lem7637306 M N)). Qed.
Lemma lem7637308 {M N : Type'} : (term20 M N) = (term20 M N).
Proof. exact (SYM (@lem7637307 M N)). Qed.
Lemma lem7637330 (n : nat) : (term21 n) = True.
Proof. exact (EQ_MP (@lem7637144 n) (@lem7637143 n)). Qed.
Lemma lem7637331 {M N : Type'} : (term19 M N) = True.
Proof. exact (@lem7637330 (term4 M N)). Qed.
Lemma lem7637332 {M N : Type'} : (term17 M N) = (term17 M N).
Proof. exact (eq_refl (term17 M N)). Qed.
Lemma lem7637333 {M N : Type'} : (term20 M N) = (term22 M N).
Proof. exact (MK_COMB (@lem7637332 M N) (@lem7637331 M N)). Qed.
Lemma lem7637335 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem7637336 {M N : Type'} : (term22 M N) = (term16 M N).
Proof. exact (@lem7637335 (term16 M N)). Qed.
Lemma lem7637355 {M N : Type'} : (term20 M N) = (term16 M N).
Proof. exact (TRANS (@lem7637333 M N) (@lem7637336 M N)). Qed.
Lemma lem7637356 {M N : Type'} : (term16 M N) = (term20 M N).
Proof. exact (SYM (@lem7637355 M N)). Qed.
Lemma lem7637358 (p : Prop) : p = (term23 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7637359 {M N : Type'} : (term16 M N) = (term24 M N).
Proof. exact (@lem7637358 (term16 M N)). Qed.
Lemma lem7637360 {M N : Type'} : (term24 M N) = (term16 M N).
Proof. exact (SYM (@lem7637359 M N)). Qed.
Lemma lem7637361 {M N : Type'} (h1 : term25 M N) : term25 M N.
Proof. exact (h1). Qed.
Lemma lem7637362 {M N : Type'} : term26 M N.
Proof. exact (@lem7631335 M N). Qed.
Lemma lem7637364 {B M : Type'} : term27 B M.
Proof. exact (@lem7631335 M B). Qed.
Lemma lem7637365 {B N : Type'} : term27 B N.
Proof. exact (@lem7631335 N B). Qed.
Lemma lem7637368 {A M : Type'} : term26 A M.
Proof. exact (@lem7631335 A M). Qed.
Lemma lem7637369 {A N : Type'} : term26 A N.
Proof. exact (@lem7631335 A N). Qed.
Lemma lem7637374 {A B M N : Type'} (h1 : term28 A B M N) : term28 A B M N.
Proof. exact (h1). Qed.
Lemma lem7637375 {A B M N : Type'} : term29 A B M N.
Proof. exact (fun h0 : term28 A B M N => @lem7637374 A B M N h0). Qed.
Lemma lem7637376 {A B M N : Type'} (h1 : term29 A B M N) : term29 A B M N.
Proof. exact (h1). Qed.
Lemma lem7637377 {A B M N : Type'} (h1 : term28 A B M N) : term28 A B M N.
Proof. exact (h1). Qed.
Lemma lem7637378 {A B M N : Type'} (h1 : term28 A B M N) (h2 : term29 A B M N) : term28 A B M N.
Proof. exact (@lem7637376 A B M N h2 (@lem7637377 A B M N h1)). Qed.
Lemma lem7637379 {A B M N : Type'} (h1 : term28 A B M N) : term30 A B M N.
Proof. exact (fun h0 : term29 A B M N => @lem7637378 A B M N h1 h0). Qed.
Lemma lem7637380 {A B M N : Type'} (h1 : term29 A B M N) : term29 A B M N.
Proof. exact (h1). Qed.
Lemma lem7637381 {A B M N : Type'} (h1 : term28 A B M N) (h2 : term29 A B M N) : term28 A B M N.
Proof. exact (@lem7637379 A B M N h1 (@lem7637380 A B M N h2)). Qed.
Lemma lem7637382 {A B M N : Type'} (h1 : term29 A B M N) : term29 A B M N.
Proof. exact (fun h0 : term28 A B M N => @lem7637381 A B M N h0 h1). Qed.
Lemma lem7637383 {A B M N : Type'} : term31 A B M N.
Proof. exact (fun h0 : term29 A B M N => @lem7637382 A B M N h0). Qed.
Lemma lem7637386 {A B M N : Type'} : term29 A B M N.
Proof. exact (@lem7637383 A B M N (@lem7637375 A B M N)). Qed.
Lemma lem7637387 {A B M N : Type'} : term29 A B M N.
Proof. exact (@lem7637386 A B M N). Qed.
Lemma lem7637465 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7637466 {B N : Type'} : (term32 B N) = (term33 B N).
Proof. exact (@lem7637465 (term27 B N)). Qed.
Lemma lem7637477 {M N : Type'} : (term34 M N) = (term34 M N).
Proof. exact (eq_refl (term34 M N)). Qed.
Lemma lem7637478 {B M N : Type'} : (term35 B M N) = (term36 B M N).
Proof. exact (MK_COMB (@lem7637477 M N) (@lem7637466 B N)). Qed.
Lemma lem7637481 {B M : Type'} : (term37 B M) = (term37 B M).
Proof. exact (eq_refl (term37 B M)). Qed.
Lemma lem7637482 {B M N : Type'} : (term38 B M N) = (term39 B M N).
Proof. exact (MK_COMB (@lem7637481 B M) (@lem7637478 B M N)). Qed.
Lemma lem7637485 {A N : Type'} : (term34 A N) = (term34 A N).
Proof. exact (eq_refl (term34 A N)). Qed.
Lemma lem7637486 {A B M N : Type'} : (term40 A B M N) = (term41 A B M N).
Proof. exact (MK_COMB (@lem7637485 A N) (@lem7637482 B M N)). Qed.
Lemma lem7637489 {A M : Type'} : (term34 A M) = (term34 A M).
Proof. exact (eq_refl (term34 A M)). Qed.
Lemma lem7637490 {A B M N : Type'} : (term42 A B M N) = (term43 A B M N).
Proof. exact (MK_COMB (@lem7637489 A M) (@lem7637486 A B M N)). Qed.
Lemma lem7637493 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (eq_refl (term34 A B)). Qed.
Lemma lem7637494 {A B M N : Type'} : (term44 A B M N) = (term45 A B M N).
Proof. exact (MK_COMB (@lem7637493 A B) (@lem7637490 A B M N)). Qed.
Lemma lem7637497 {M N : Type'} : (term46 M N) = (term46 M N).
Proof. exact (eq_refl (term46 M N)). Qed.
Lemma lem7637504 {A B M N : Type'} : (term28 A B M N) = (term47 A B M N).
Proof. exact (MK_COMB (@lem7637497 M N) (@lem7637494 A B M N)). Qed.
Lemma lem7637509 {B N : Type'} (r : nat) : ((term48 B N r) = ((term49 B N r) = r)) = ((term48 B N r) = ((term49 B N r) = r)).
Proof. exact (eq_refl ((term48 B N r) = ((term49 B N r) = r))). Qed.
Lemma lem7637510 {B N : Type'} : (term50 B N) = (term50 B N).
Proof. exact (fun_ext (fun r : nat => @lem7637509 B N r)). Qed.
Lemma lem7637511 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7637512 {B N : Type'} : (term51 B N) = (term51 B N).
Proof. exact (MK_COMB (@lem7637511) (@lem7637510 B N)). Qed.
Lemma lem7637513 {B N : Type'} (a : finite_sum N B) : ((term52 B N a) = a) = ((term52 B N a) = a).
Proof. exact (eq_refl ((term52 B N a) = a)). Qed.
Lemma lem7637514 {B N : Type'} : (term53 B N) = (term53 B N).
Proof. exact (fun_ext (fun a : finite_sum N B => @lem7637513 B N a)). Qed.
Lemma lem7637515 {B N : Type'} : (@all (finite_sum N B)) = (@all (finite_sum N B)).
Proof. exact (eq_refl (@all (finite_sum N B))). Qed.
Lemma lem7637516 {B N : Type'} : (term54 B N) = (term54 B N).
Proof. exact (MK_COMB (@lem7637515 B N) (@lem7637514 B N)). Qed.
Lemma lem7637517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7637518 {B N : Type'} : (term55 B N) = (term55 B N).
Proof. exact (MK_COMB (@lem7637517) (@lem7637516 B N)). Qed.
Lemma lem7637519 {B N : Type'} : (term27 B N) = (term27 B N).
Proof. exact (MK_COMB (@lem7637518 B N) (@lem7637512 B N)). Qed.
Lemma lem7637520 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7637521 {B N : Type'} : (term33 B N) = (term33 B N).
Proof. exact (MK_COMB (@lem7637520) (@lem7637519 B N)). Qed.
Lemma lem7637526 {M N : Type'} (r : nat) : ((term7 M N r) = ((term56 M N r) = r)) = ((term7 M N r) = ((term56 M N r) = r)).
Proof. exact (eq_refl ((term7 M N r) = ((term56 M N r) = r))). Qed.
Lemma lem7637527 {M N : Type'} : (term57 M N) = (term57 M N).
Proof. exact (fun_ext (fun r : nat => @lem7637526 M N r)). Qed.
Lemma lem7637528 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7637529 {M N : Type'} : (term58 M N) = (term58 M N).
Proof. exact (MK_COMB (@lem7637528) (@lem7637527 M N)). Qed.
Lemma lem7637530 {M N : Type'} (a : finite_sum M N) : ((term59 M N a) = a) = ((term59 M N a) = a).
Proof. exact (eq_refl ((term59 M N a) = a)). Qed.
Lemma lem7637531 {M N : Type'} : (term60 M N) = (term60 M N).
Proof. exact (fun_ext (fun a : finite_sum M N => @lem7637530 M N a)). Qed.
Lemma lem7637532 {M N : Type'} : (@all (finite_sum M N)) = (@all (finite_sum M N)).
Proof. exact (eq_refl (@all (finite_sum M N))). Qed.
Lemma lem7637533 {M N : Type'} : (term61 M N) = (term61 M N).
Proof. exact (MK_COMB (@lem7637532 M N) (@lem7637531 M N)). Qed.
Lemma lem7637534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7637535 {M N : Type'} : (term62 M N) = (term62 M N).
Proof. exact (MK_COMB (@lem7637534) (@lem7637533 M N)). Qed.
Lemma lem7637536 {M N : Type'} : (term26 M N) = (term26 M N).
Proof. exact (MK_COMB (@lem7637535 M N) (@lem7637529 M N)). Qed.
Lemma lem7637537 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7637538 {M N : Type'} : (term34 M N) = (term34 M N).
Proof. exact (MK_COMB (@lem7637537) (@lem7637536 M N)). Qed.
Lemma lem7637539 {B M N : Type'} : (term36 B M N) = (term36 B M N).
Proof. exact (MK_COMB (@lem7637538 M N) (@lem7637521 B N)). Qed.
Lemma lem7637544 {B M : Type'} (r : nat) : ((term48 B M r) = ((term49 B M r) = r)) = ((term48 B M r) = ((term49 B M r) = r)).
Proof. exact (eq_refl ((term48 B M r) = ((term49 B M r) = r))). Qed.
Lemma lem7637545 {B M : Type'} : (term50 B M) = (term50 B M).
Proof. exact (fun_ext (fun r : nat => @lem7637544 B M r)). Qed.
Lemma lem7637546 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7637547 {B M : Type'} : (term51 B M) = (term51 B M).
Proof. exact (MK_COMB (@lem7637546) (@lem7637545 B M)). Qed.
Lemma lem7637548 {B M : Type'} (a : finite_sum M B) : ((term52 B M a) = a) = ((term52 B M a) = a).
Proof. exact (eq_refl ((term52 B M a) = a)). Qed.
Lemma lem7637549 {B M : Type'} : (term53 B M) = (term53 B M).
Proof. exact (fun_ext (fun a : finite_sum M B => @lem7637548 B M a)). Qed.
Lemma lem7637550 {B M : Type'} : (@all (finite_sum M B)) = (@all (finite_sum M B)).
Proof. exact (eq_refl (@all (finite_sum M B))). Qed.
Lemma lem7637551 {B M : Type'} : (term54 B M) = (term54 B M).
Proof. exact (MK_COMB (@lem7637550 B M) (@lem7637549 B M)). Qed.
Lemma lem7637552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7637553 {B M : Type'} : (term55 B M) = (term55 B M).
Proof. exact (MK_COMB (@lem7637552) (@lem7637551 B M)). Qed.
Lemma lem7637554 {B M : Type'} : (term27 B M) = (term27 B M).
Proof. exact (MK_COMB (@lem7637553 B M) (@lem7637547 B M)). Qed.
Lemma lem7637555 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7637556 {B M : Type'} : (term37 B M) = (term37 B M).
Proof. exact (MK_COMB (@lem7637555) (@lem7637554 B M)). Qed.
Lemma lem7637557 {B M N : Type'} : (term39 B M N) = (term39 B M N).
Proof. exact (MK_COMB (@lem7637556 B M) (@lem7637539 B M N)). Qed.
Lemma lem7637562 {A N : Type'} (r : nat) : ((term7 A N r) = ((term56 A N r) = r)) = ((term7 A N r) = ((term56 A N r) = r)).
Proof. exact (eq_refl ((term7 A N r) = ((term56 A N r) = r))). Qed.
Lemma lem7637563 {A N : Type'} : (term57 A N) = (term57 A N).
Proof. exact (fun_ext (fun r : nat => @lem7637562 A N r)). Qed.
Lemma lem7637564 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7637565 {A N : Type'} : (term58 A N) = (term58 A N).
Proof. exact (MK_COMB (@lem7637564) (@lem7637563 A N)). Qed.
Lemma lem7637566 {A N : Type'} (a : finite_sum A N) : ((term59 A N a) = a) = ((term59 A N a) = a).
Proof. exact (eq_refl ((term59 A N a) = a)). Qed.
Lemma lem7637567 {A N : Type'} : (term60 A N) = (term60 A N).
Proof. exact (fun_ext (fun a : finite_sum A N => @lem7637566 A N a)). Qed.
Lemma lem7637568 {A N : Type'} : (@all (finite_sum A N)) = (@all (finite_sum A N)).
Proof. exact (eq_refl (@all (finite_sum A N))). Qed.
Lemma lem7637569 {A N : Type'} : (term61 A N) = (term61 A N).
Proof. exact (MK_COMB (@lem7637568 A N) (@lem7637567 A N)). Qed.
Lemma lem7637570 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7637571 {A N : Type'} : (term62 A N) = (term62 A N).
Proof. exact (MK_COMB (@lem7637570) (@lem7637569 A N)). Qed.
Lemma lem7637572 {A N : Type'} : (term26 A N) = (term26 A N).
Proof. exact (MK_COMB (@lem7637571 A N) (@lem7637565 A N)). Qed.
Lemma lem7637573 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7637574 {A N : Type'} : (term34 A N) = (term34 A N).
Proof. exact (MK_COMB (@lem7637573) (@lem7637572 A N)). Qed.
Lemma lem7637575 {A B M N : Type'} : (term41 A B M N) = (term41 A B M N).
Proof. exact (MK_COMB (@lem7637574 A N) (@lem7637557 B M N)). Qed.
Lemma lem7637580 {A M : Type'} (r : nat) : ((term7 A M r) = ((term56 A M r) = r)) = ((term7 A M r) = ((term56 A M r) = r)).
Proof. exact (eq_refl ((term7 A M r) = ((term56 A M r) = r))). Qed.
Lemma lem7637581 {A M : Type'} : (term57 A M) = (term57 A M).
Proof. exact (fun_ext (fun r : nat => @lem7637580 A M r)). Qed.
Lemma lem7637582 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7637583 {A M : Type'} : (term58 A M) = (term58 A M).
Proof. exact (MK_COMB (@lem7637582) (@lem7637581 A M)). Qed.
Lemma lem7637584 {A M : Type'} (a : finite_sum A M) : ((term59 A M a) = a) = ((term59 A M a) = a).
Proof. exact (eq_refl ((term59 A M a) = a)). Qed.
Lemma lem7637585 {A M : Type'} : (term60 A M) = (term60 A M).
Proof. exact (fun_ext (fun a : finite_sum A M => @lem7637584 A M a)). Qed.
Lemma lem7637586 {A M : Type'} : (@all (finite_sum A M)) = (@all (finite_sum A M)).
Proof. exact (eq_refl (@all (finite_sum A M))). Qed.
Lemma lem7637587 {A M : Type'} : (term61 A M) = (term61 A M).
Proof. exact (MK_COMB (@lem7637586 A M) (@lem7637585 A M)). Qed.
Lemma lem7637588 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7637589 {A M : Type'} : (term62 A M) = (term62 A M).
Proof. exact (MK_COMB (@lem7637588) (@lem7637587 A M)). Qed.
Lemma lem7637590 {A M : Type'} : (term26 A M) = (term26 A M).
Proof. exact (MK_COMB (@lem7637589 A M) (@lem7637583 A M)). Qed.
Lemma lem7637591 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7637592 {A M : Type'} : (term34 A M) = (term34 A M).
Proof. exact (MK_COMB (@lem7637591) (@lem7637590 A M)). Qed.
Lemma lem7637593 {A B M N : Type'} : (term43 A B M N) = (term43 A B M N).
Proof. exact (MK_COMB (@lem7637592 A M) (@lem7637575 A B M N)). Qed.
Lemma lem7637598 {A B : Type'} (r : nat) : ((term7 A B r) = ((term56 A B r) = r)) = ((term7 A B r) = ((term56 A B r) = r)).
Proof. exact (eq_refl ((term7 A B r) = ((term56 A B r) = r))). Qed.
Lemma lem7637599 {A B : Type'} : (term57 A B) = (term57 A B).
Proof. exact (fun_ext (fun r : nat => @lem7637598 A B r)). Qed.
Lemma lem7637600 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7637601 {A B : Type'} : (term58 A B) = (term58 A B).
Proof. exact (MK_COMB (@lem7637600) (@lem7637599 A B)). Qed.
Lemma lem7637602 {A B : Type'} (a : finite_sum A B) : ((term59 A B a) = a) = ((term59 A B a) = a).
Proof. exact (eq_refl ((term59 A B a) = a)). Qed.
Lemma lem7637603 {A B : Type'} : (term60 A B) = (term60 A B).
Proof. exact (fun_ext (fun a : finite_sum A B => @lem7637602 A B a)). Qed.
Lemma lem7637604 {A B : Type'} : (@all (finite_sum A B)) = (@all (finite_sum A B)).
Proof. exact (eq_refl (@all (finite_sum A B))). Qed.
Lemma lem7637605 {A B : Type'} : (term61 A B) = (term61 A B).
Proof. exact (MK_COMB (@lem7637604 A B) (@lem7637603 A B)). Qed.
Lemma lem7637606 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7637607 {A B : Type'} : (term62 A B) = (term62 A B).
Proof. exact (MK_COMB (@lem7637606) (@lem7637605 A B)). Qed.
Lemma lem7637608 {A B : Type'} : (term26 A B) = (term26 A B).
Proof. exact (MK_COMB (@lem7637607 A B) (@lem7637601 A B)). Qed.
Lemma lem7637609 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7637610 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem7637609) (@lem7637608 A B)). Qed.
Lemma lem7637611 {A B M N : Type'} : (term45 A B M N) = (term45 A B M N).
Proof. exact (MK_COMB (@lem7637610 A B) (@lem7637593 A B M N)). Qed.
Lemma lem7637624 {M N : Type'} (x : nat) (y : nat) : (term12 M N x y) = (term12 M N x y).
Proof. exact (eq_refl (term12 M N x y)). Qed.
Lemma lem7637625 {M N : Type'} (x : nat) : (term13 M N x) = (term13 M N x).
Proof. exact (fun_ext (fun y : nat => @lem7637624 M N x y)). Qed.
Lemma lem7637626 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7637627 {M N : Type'} (x : nat) : (term14 M N x) = (term14 M N x).
Proof. exact (MK_COMB (@lem7637626) (@lem7637625 M N x)). Qed.
Lemma lem7637628 {M N : Type'} : (term15 M N) = (term15 M N).
Proof. exact (fun_ext (fun x : nat => @lem7637627 M N x)). Qed.
Lemma lem7637629 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7637630 {M N : Type'} : (term16 M N) = (term16 M N).
Proof. exact (MK_COMB (@lem7637629) (@lem7637628 M N)). Qed.
Lemma lem7637631 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7637632 {M N : Type'} : (term25 M N) = (term25 M N).
Proof. exact (MK_COMB (@lem7637631) (@lem7637630 M N)). Qed.
Lemma lem7637633 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7637634 {M N : Type'} : (term46 M N) = (term46 M N).
Proof. exact (MK_COMB (@lem7637633) (@lem7637632 M N)). Qed.
Lemma lem7637635 {A B M N : Type'} : (term47 A B M N) = (term47 A B M N).
Proof. exact (MK_COMB (@lem7637634 M N) (@lem7637611 A B M N)). Qed.
Lemma lem7637752 {A B M N : Type'} : (term28 A B M N) = (term47 A B M N).
Proof. exact (TRANS (@lem7637504 A B M N) (@lem7637635 A B M N)). Qed.
Lemma lem7637753 {A B M N : Type'} : (term47 A B M N) = (term28 A B M N).
Proof. exact (SYM (@lem7637752 A B M N)). Qed.
Lemma lem7637754 {M N : Type'} (h1 : term25 M N) : term25 M N.
Proof. exact (h1). Qed.
Lemma lem7637759 {M N : Type'} (h1 : term26 M N) : term26 M N.
Proof. exact (h1). Qed.
Lemma lem7637775 {M N : Type'} (x : nat) (y : nat) : (term63 M N x y) = (term64 M N x y).
Proof. exact (@lem17362 (term10 M N x y) (x = y)). Qed.
Lemma lem7637776 (P : nat -> Prop) : (term65 P) = (term66 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7637777 {M N : Type'} (x : nat) : (term67 M N x) = (term68 M N x).
Proof. exact (@lem7637776 (term13 M N x)). Qed.
Lemma lem7637778 {M N : Type'} (x : nat) (y : nat) : (term69 M N x y) = (term12 M N x y).
Proof. exact (eq_refl (term69 M N x y)). Qed.
Lemma lem7637779 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7637780 {M N : Type'} (x : nat) (y : nat) : (term70 M N x y) = (term63 M N x y).
Proof. exact (MK_COMB (@lem7637779) (@lem7637778 M N x y)). Qed.
Lemma lem7637781 {M N : Type'} (x : nat) (y : nat) : (term70 M N x y) = (term64 M N x y).
Proof. exact (TRANS (@lem7637780 M N x y) (@lem7637775 M N x y)). Qed.
Lemma lem7637782 {M N : Type'} (x : nat) : (term71 M N x) = (term72 M N x).
Proof. exact (fun_ext (fun y : nat => @lem7637781 M N x y)). Qed.
Lemma lem7637783 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7637784 {M N : Type'} (x : nat) : (term68 M N x) = (term73 M N x).
Proof. exact (MK_COMB (@lem7637783) (@lem7637782 M N x)). Qed.
Lemma lem7637785 {M N : Type'} (x : nat) : (term67 M N x) = (term73 M N x).
Proof. exact (TRANS (@lem7637777 M N x) (@lem7637784 M N x)). Qed.
Lemma lem7637786 (P : nat -> Prop) : (term65 P) = (term66 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7637787 {M N : Type'} : (term25 M N) = (term74 M N).
Proof. exact (@lem7637786 (term15 M N)). Qed.
Lemma lem7637788 {M N : Type'} (x : nat) : (term75 M N x) = (term14 M N x).
Proof. exact (eq_refl (term75 M N x)). Qed.
Lemma lem7637789 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7637790 {M N : Type'} (x : nat) : (term76 M N x) = (term67 M N x).
Proof. exact (MK_COMB (@lem7637789) (@lem7637788 M N x)). Qed.
Lemma lem7637791 {M N : Type'} (x : nat) : (term76 M N x) = (term73 M N x).
Proof. exact (TRANS (@lem7637790 M N x) (@lem7637785 M N x)). Qed.
Lemma lem7637792 {M N : Type'} : (term77 M N) = (term78 M N).
Proof. exact (fun_ext (fun x : nat => @lem7637791 M N x)). Qed.
Lemma lem7637793 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7637794 {M N : Type'} : (term74 M N) = (term79 M N).
Proof. exact (MK_COMB (@lem7637793) (@lem7637792 M N)). Qed.
Lemma lem7637851 {M N : Type'} : (term25 M N) = (term79 M N).
Proof. exact (TRANS (@lem7637787 M N) (@lem7637794 M N)). Qed.
Lemma lem7637852 {M N : Type'} (h1 : term25 M N) : term79 M N.
Proof. exact (EQ_MP (@lem7637851 M N) (@lem7637754 M N h1)). Qed.
Lemma lem7638485 {M N : Type'} (a : finite_sum M N) : ((term59 M N a) = a) = ((term59 M N a) = a).
Proof. exact (eq_refl ((term59 M N a) = a)). Qed.
Lemma lem7638486 {M N : Type'} : (term60 M N) = (term60 M N).
Proof. exact (fun_ext (fun a : finite_sum M N => @lem7638485 M N a)). Qed.
Lemma lem7638487 {M N : Type'} : (@all (finite_sum M N)) = (@all (finite_sum M N)).
Proof. exact (eq_refl (@all (finite_sum M N))). Qed.
Lemma lem7638488 {M N : Type'} : (term61 M N) = (term61 M N).
Proof. exact (MK_COMB (@lem7638487 M N) (@lem7638486 M N)). Qed.
Lemma lem7638503 {M N : Type'} (r : nat) : ((term7 M N r) = ((term56 M N r) = r)) = (term80 M N r).
Proof. exact (@lem17784 (term7 M N r) ((term56 M N r) = r)). Qed.
Lemma lem7638504 {M N : Type'} : (term57 M N) = (term81 M N).
Proof. exact (fun_ext (fun r : nat => @lem7638503 M N r)). Qed.
Lemma lem7638505 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7638506 {M N : Type'} : (term58 M N) = (term82 M N).
Proof. exact (MK_COMB (@lem7638505) (@lem7638504 M N)). Qed.
Lemma lem7638507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7638508 {M N : Type'} : (term62 M N) = (term62 M N).
Proof. exact (MK_COMB (@lem7638507) (@lem7638488 M N)). Qed.
Lemma lem7638509 {M N : Type'} : (term26 M N) = (term83 M N).
Proof. exact (MK_COMB (@lem7638508 M N) (@lem7638506 M N)). Qed.
Lemma lem7638515 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term84 A P Q) = (term85 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7638516 (P : nat -> Prop) (Q : nat -> Prop) : (term86 P Q) = (term87 P Q).
Proof. exact (@lem7638515 nat P Q). Qed.
Lemma lem7638517 {M N : Type'} : (term88 M N) = (term89 M N).
Proof. exact (@lem7638516 (term90 M N) (term91 M N)). Qed.
Lemma lem7638518 {M N : Type'} (r : nat) : (term92 M N r) = (term93 M N r).
Proof. exact (eq_refl (term92 M N r)). Qed.
Lemma lem7638519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7638520 {M N : Type'} (r : nat) : (term94 M N r) = (term95 M N r).
Proof. exact (MK_COMB (@lem7638519) (@lem7638518 M N r)). Qed.
Lemma lem7638521 {M N : Type'} (r : nat) : (term96 M N r) = (term97 M N r).
Proof. exact (eq_refl (term96 M N r)). Qed.
Lemma lem7638522 {M N : Type'} (r : nat) : (term98 M N r) = (term80 M N r).
Proof. exact (MK_COMB (@lem7638520 M N r) (@lem7638521 M N r)). Qed.
Lemma lem7638523 {M N : Type'} : (term99 M N) = (term81 M N).
Proof. exact (fun_ext (fun r : nat => @lem7638522 M N r)). Qed.
Lemma lem7638524 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7638525 {M N : Type'} : (term88 M N) = (term82 M N).
Proof. exact (MK_COMB (@lem7638524) (@lem7638523 M N)). Qed.
Lemma lem7638526 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7638527 {M N : Type'} : (term100 M N) = (term101 M N).
Proof. exact (MK_COMB (@lem7638526) (@lem7638525 M N)). Qed.
Lemma lem7638528 {M N : Type'} (r : nat) : (term92 M N r) = (term93 M N r).
Proof. exact (eq_refl (term92 M N r)). Qed.
Lemma lem7638529 {M N : Type'} : (term102 M N) = (term90 M N).
Proof. exact (fun_ext (fun r : nat => @lem7638528 M N r)). Qed.
Lemma lem7638530 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7638531 {M N : Type'} : (term103 M N) = (term104 M N).
Proof. exact (MK_COMB (@lem7638530) (@lem7638529 M N)). Qed.
Lemma lem7638532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7638533 {M N : Type'} : (term105 M N) = (term106 M N).
Proof. exact (MK_COMB (@lem7638532) (@lem7638531 M N)). Qed.
Lemma lem7638534 {M N : Type'} (r : nat) : (term96 M N r) = (term97 M N r).
Proof. exact (eq_refl (term96 M N r)). Qed.
Lemma lem7638535 {M N : Type'} : (term107 M N) = (term91 M N).
Proof. exact (fun_ext (fun r : nat => @lem7638534 M N r)). Qed.
Lemma lem7638536 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7638537 {M N : Type'} : (term108 M N) = (term109 M N).
Proof. exact (MK_COMB (@lem7638536) (@lem7638535 M N)). Qed.
Lemma lem7638538 {M N : Type'} : (term89 M N) = (term110 M N).
Proof. exact (MK_COMB (@lem7638533 M N) (@lem7638537 M N)). Qed.
Lemma lem7638539 {M N : Type'} : ((term88 M N) = (term89 M N)) = ((term82 M N) = (term110 M N)).
Proof. exact (MK_COMB (@lem7638527 M N) (@lem7638538 M N)). Qed.
Lemma lem7638540 {M N : Type'} : (term82 M N) = (term110 M N).
Proof. exact (EQ_MP (@lem7638539 M N) (@lem7638517 M N)). Qed.
Lemma lem7638637 {M N : Type'} : (term62 M N) = (term62 M N).
Proof. exact (eq_refl (term62 M N)). Qed.
Lemma lem7638640 {M N : Type'} : (term83 M N) = (term111 M N).
Proof. exact (MK_COMB (@lem7638637 M N) (@lem7638540 M N)). Qed.
Lemma lem7638641 {M N : Type'} : (term26 M N) = (term111 M N).
Proof. exact (TRANS (@lem7638509 M N) (@lem7638640 M N)). Qed.
Lemma lem7638642 {M N : Type'} (h1 : term26 M N) : term111 M N.
Proof. exact (EQ_MP (@lem7638641 M N) (@lem7637759 M N h1)). Qed.
Lemma lem7638801 {M N : Type'} (x : nat) (h1 : term73 M N x) : term73 M N x.
Proof. exact (h1). Qed.
Lemma lem7639217 {M N : Type'} (r : nat) : (term97 M N r) = (term97 M N r).
Proof. exact (eq_refl (term97 M N r)). Qed.
Lemma lem7639218 {M N : Type'} : (term91 M N) = (term91 M N).
Proof. exact (fun_ext (fun r : nat => @lem7639217 M N r)). Qed.
Lemma lem7639219 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7639220 {M N : Type'} : (term109 M N) = (term109 M N).
Proof. exact (MK_COMB (@lem7639219) (@lem7639218 M N)). Qed.
Lemma lem7639255 {M N : Type'} (r : nat) : (term93 M N r) = (term93 M N r).
Proof. exact (eq_refl (term93 M N r)). Qed.
Lemma lem7639256 {M N : Type'} : (term90 M N) = (term90 M N).
Proof. exact (fun_ext (fun r : nat => @lem7639255 M N r)). Qed.
Lemma lem7639257 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7639258 {M N : Type'} : (term104 M N) = (term104 M N).
Proof. exact (MK_COMB (@lem7639257) (@lem7639256 M N)). Qed.
Lemma lem7639259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7639260 {M N : Type'} : (term106 M N) = (term106 M N).
Proof. exact (MK_COMB (@lem7639259) (@lem7639258 M N)). Qed.
Lemma lem7639261 {M N : Type'} : (term110 M N) = (term110 M N).
Proof. exact (MK_COMB (@lem7639260 M N) (@lem7639220 M N)). Qed.
Lemma lem7639270 {M N : Type'} (a : finite_sum M N) : ((term59 M N a) = a) = ((term59 M N a) = a).
Proof. exact (eq_refl ((term59 M N a) = a)). Qed.
Lemma lem7639271 {M N : Type'} : (term60 M N) = (term60 M N).
Proof. exact (fun_ext (fun a : finite_sum M N => @lem7639270 M N a)). Qed.
Lemma lem7639272 {M N : Type'} : (@all (finite_sum M N)) = (@all (finite_sum M N)).
Proof. exact (eq_refl (@all (finite_sum M N))). Qed.
Lemma lem7639273 {M N : Type'} : (term61 M N) = (term61 M N).
Proof. exact (MK_COMB (@lem7639272 M N) (@lem7639271 M N)). Qed.
Lemma lem7639274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7639275 {M N : Type'} : (term62 M N) = (term62 M N).
Proof. exact (MK_COMB (@lem7639274) (@lem7639273 M N)). Qed.
Lemma lem7639276 {M N : Type'} : (term111 M N) = (term111 M N).
Proof. exact (MK_COMB (@lem7639275 M N) (@lem7639261 M N)). Qed.
Lemma lem7639277 {M N : Type'} (h1 : term26 M N) : term111 M N.
Proof. exact (EQ_MP (@lem7639276 M N) (@lem7638642 M N h1)). Qed.
Lemma lem7639440 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : term64 M N x y.
Proof. exact (h1). Qed.
Lemma lem7639442 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : term10 M N x y.
Proof. exact (proj1 (@lem7639440 M N x y h1)). Qed.
Lemma lem7639443 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : term9 M N x y.
Proof. exact (proj2 (@lem7639442 M N x y h1)). Qed.
Lemma lem7639451 {M N : Type'} (h1 : term26 M N) : term110 M N.
Proof. exact (proj2 (@lem7639277 M N h1)). Qed.
Lemma lem7639453 {M N : Type'} (h1 : term26 M N) : term109 M N.
Proof. exact (proj2 (@lem7639451 M N h1)). Qed.
Lemma lem7639547 {M N : Type'} (r : nat) : (term97 M N r) = (term97 M N r).
Proof. exact (eq_refl (term97 M N r)). Qed.
Lemma lem7639548 {M N : Type'} : (term91 M N) = (term91 M N).
Proof. exact (fun_ext (fun r : nat => @lem7639547 M N r)). Qed.
Lemma lem7639549 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7639551 {M N : Type'} : (term109 M N) = (term109 M N).
Proof. exact (MK_COMB (@lem7639549) (@lem7639548 M N)). Qed.
Lemma lem7639552 {M N : Type'} (h1 : term26 M N) : term109 M N.
Proof. exact (EQ_MP (@lem7639551 M N) (@lem7639453 M N h1)). Qed.
Lemma lem7639700 {M N : Type'} (_98425 : nat) (h1 : term26 M N) : term96 M N _98425.
Proof. exact (@lem7639552 M N h1 _98425). Qed.
Lemma lem7639701 {M N : Type'} (_98425 : nat) : (term96 M N _98425) = (term97 M N _98425).
Proof. exact (eq_refl (term96 M N _98425)). Qed.
Lemma lem7639740 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : term112 x y.
Proof. exact (proj2 (@lem7639440 M N x y h1)). Qed.
Lemma lem7639774 {M N : Type'} (_98425 : nat) (h1 : term26 M N) : term97 M N _98425.
Proof. exact (EQ_MP (@lem7639701 M N _98425) (@lem7639700 M N _98425 h1)). Qed.
Lemma lem7639922 {M N : Type'} : (@dest_finite_sum M N) = (@dest_finite_sum M N).
Proof. exact (eq_refl (@dest_finite_sum M N)). Qed.
Lemma lem7639923 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) (h1 : _98460 = _98461) : _98460 = _98461.
Proof. exact (h1). Qed.
Lemma lem7639924 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) (h1 : _98460 = _98461) : (@dest_finite_sum M N _98460) = (@dest_finite_sum M N _98461).
Proof. exact (MK_COMB (@lem7639922 M N) (@lem7639923 M N _98460 _98461 h1)). Qed.
Lemma lem7639925 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : term113 M N _98460 _98461.
Proof. exact (fun h0 : _98460 = _98461 => @lem7639924 M N _98460 _98461 h0). Qed.
Lemma lem7639927 (a : Prop) (b : Prop) : (a -> b) = (term114 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7639928 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : (term113 M N _98460 _98461) = (term115 M N _98460 _98461).
Proof. exact (@lem7639927 (_98460 = _98461) ((@dest_finite_sum M N _98460) = (@dest_finite_sum M N _98461))). Qed.
Lemma lem7639929 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : term115 M N _98460 _98461.
Proof. exact (EQ_MP (@lem7639928 M N _98460 _98461) (@lem7639925 M N _98460 _98461)). Qed.
Lemma lem7640027 (x : nat) (y : nat) (z : nat) : term116 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem7640049 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : (@mk_finite_sum M N x) = (@mk_finite_sum M N y).
Proof. exact (proj2 (@lem7639443 M N x y h1)). Qed.
Lemma lem7640050 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : term117 M N x y.
Proof. exact (fun h0 : term118 M N x y => @lem7640049 M N x y h1). Qed.
Lemma lem7640052 (p : Prop) : (term119 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7640053 {M N : Type'} (x : nat) (y : nat) : (term117 M N x y) = ((@mk_finite_sum M N x) = (@mk_finite_sum M N y)).
Proof. exact (@lem7640052 ((@mk_finite_sum M N x) = (@mk_finite_sum M N y))). Qed.
Lemma lem7640054 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : (@mk_finite_sum M N x) = (@mk_finite_sum M N y).
Proof. exact (EQ_MP (@lem7640053 M N x y) (@lem7640050 M N x y h1)). Qed.
Lemma lem7640060 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7640061 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : (term115 M N _98460 _98461) = (term120 M N _98460 _98461).
Proof. exact (@lem7640060 ((@dest_finite_sum M N _98460) = (@dest_finite_sum M N _98461)) (term121 M N _98460 _98461)). Qed.
Lemma lem7640071 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7640072 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : (term122 M N _98460 _98461) = (term123 M N _98460 _98461).
Proof. exact (MK_COMB (@lem7640071) (@lem7640061 M N _98460 _98461)). Qed.
Lemma lem7640082 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : (term120 M N _98460 _98461) = (term120 M N _98460 _98461).
Proof. exact (eq_refl (term120 M N _98460 _98461)). Qed.
Lemma lem7640083 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : ((term115 M N _98460 _98461) = (term120 M N _98460 _98461)) = ((term120 M N _98460 _98461) = (term120 M N _98460 _98461)).
Proof. exact (MK_COMB (@lem7640072 M N _98460 _98461) (@lem7640082 M N _98460 _98461)). Qed.
Lemma lem7640085 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7640086 (x : Prop) : (x = x) = True.
Proof. exact (@lem7640085 Prop x). Qed.
Lemma lem7640087 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : ((term120 M N _98460 _98461) = (term120 M N _98460 _98461)) = True.
Proof. exact (@lem7640086 (term120 M N _98460 _98461)). Qed.
Lemma lem7640088 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : ((term115 M N _98460 _98461) = (term120 M N _98460 _98461)) = True.
Proof. exact (TRANS (@lem7640083 M N _98460 _98461) (@lem7640087 M N _98460 _98461)). Qed.
Lemma lem7640089 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : True = ((term115 M N _98460 _98461) = (term120 M N _98460 _98461)).
Proof. exact (SYM (@lem7640088 M N _98460 _98461)). Qed.
Lemma lem7640090 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : (term115 M N _98460 _98461) = (term120 M N _98460 _98461).
Proof. exact (EQ_MP (@lem7640089 M N _98460 _98461) (@lem0)). Qed.
Lemma lem7640091 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : term120 M N _98460 _98461.
Proof. exact (EQ_MP (@lem7640090 M N _98460 _98461) (@lem7639929 M N _98460 _98461)). Qed.
Lemma lem7640093 (b : Prop) (a : Prop) : (a \/ b) = (term124 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7640094 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : (term120 M N _98460 _98461) = (term125 M N _98460 _98461).
Proof. exact (@lem7640093 (term121 M N _98460 _98461) ((@dest_finite_sum M N _98460) = (@dest_finite_sum M N _98461))). Qed.
Lemma lem7640096 (a : Prop) : (term126 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7640097 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : (term127 M N _98460 _98461) = (_98460 = _98461).
Proof. exact (@lem7640096 (_98460 = _98461)). Qed.
Lemma lem7640098 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7640099 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : (term128 M N _98460 _98461) = (term129 M N _98460 _98461).
Proof. exact (MK_COMB (@lem7640098) (@lem7640097 M N _98460 _98461)). Qed.
Lemma lem7640100 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : ((@dest_finite_sum M N _98460) = (@dest_finite_sum M N _98461)) = ((@dest_finite_sum M N _98460) = (@dest_finite_sum M N _98461)).
Proof. exact (eq_refl ((@dest_finite_sum M N _98460) = (@dest_finite_sum M N _98461))). Qed.
Lemma lem7640101 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : (term125 M N _98460 _98461) = (term113 M N _98460 _98461).
Proof. exact (MK_COMB (@lem7640099 M N _98460 _98461) (@lem7640100 M N _98460 _98461)). Qed.
Lemma lem7640102 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : (term120 M N _98460 _98461) = (term113 M N _98460 _98461).
Proof. exact (TRANS (@lem7640094 M N _98460 _98461) (@lem7640101 M N _98460 _98461)). Qed.
Lemma lem7640105 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : term113 M N _98460 _98461.
Proof. exact (EQ_MP (@lem7640102 M N _98460 _98461) (@lem7640091 M N _98460 _98461)). Qed.
Lemma lem7640106 {M N : Type'} (_98460 : finite_sum M N) (_98461 : finite_sum M N) : term113 M N _98460 _98461.
Proof. exact (@lem7640105 M N _98460 _98461). Qed.
Lemma lem7640107 {M N : Type'} (x : nat) (y : nat) : term130 M N x y.
Proof. exact (@lem7640106 M N (@mk_finite_sum M N x) (@mk_finite_sum M N y)). Qed.
Lemma lem7640110 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : (term56 M N x) = (term56 M N y).
Proof. exact (@lem7640107 M N x y (@lem7640054 M N x y h1)). Qed.
Lemma lem7640111 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : term131 M N x y.
Proof. exact (fun h0 : term132 M N x y => @lem7640110 M N x y h1). Qed.
Lemma lem7640113 (p : Prop) : (term119 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7640114 {M N : Type'} (x : nat) (y : nat) : (term131 M N x y) = ((term56 M N x) = (term56 M N y)).
Proof. exact (@lem7640113 ((term56 M N x) = (term56 M N y))). Qed.
Lemma lem7640115 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : (term56 M N x) = (term56 M N y).
Proof. exact (EQ_MP (@lem7640114 M N x y) (@lem7640111 M N x y h1)). Qed.
Lemma lem7640117 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : term7 M N x.
Proof. exact (proj1 (@lem7639442 M N x y h1)). Qed.
Lemma lem7640118 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : term133 M N x.
Proof. exact (fun h0 : term134 M N x => @lem7640117 M N x y h1). Qed.
Lemma lem7640120 (p : Prop) : (term119 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7640121 {M N : Type'} (x : nat) : (term133 M N x) = (term7 M N x).
Proof. exact (@lem7640120 (term7 M N x)). Qed.
Lemma lem7640122 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : term7 M N x.
Proof. exact (EQ_MP (@lem7640121 M N x) (@lem7640118 M N x y h1)). Qed.
Lemma lem7640128 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7640129 {M N : Type'} (_98425 : nat) : (term97 M N _98425) = (term135 M N _98425).
Proof. exact (@lem7640128 ((term56 M N _98425) = _98425) (term134 M N _98425)). Qed.
Lemma lem7640137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7640138 {M N : Type'} (_98425 : nat) : (term136 M N _98425) = (term137 M N _98425).
Proof. exact (MK_COMB (@lem7640137) (@lem7640129 M N _98425)). Qed.
Lemma lem7640146 {M N : Type'} (_98425 : nat) : (term135 M N _98425) = (term135 M N _98425).
Proof. exact (eq_refl (term135 M N _98425)). Qed.
Lemma lem7640147 {M N : Type'} (_98425 : nat) : ((term97 M N _98425) = (term135 M N _98425)) = ((term135 M N _98425) = (term135 M N _98425)).
Proof. exact (MK_COMB (@lem7640138 M N _98425) (@lem7640146 M N _98425)). Qed.
Lemma lem7640149 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7640150 (x : Prop) : (x = x) = True.
Proof. exact (@lem7640149 Prop x). Qed.
Lemma lem7640151 {M N : Type'} (_98425 : nat) : ((term135 M N _98425) = (term135 M N _98425)) = True.
Proof. exact (@lem7640150 (term135 M N _98425)). Qed.
Lemma lem7640152 {M N : Type'} (_98425 : nat) : ((term97 M N _98425) = (term135 M N _98425)) = True.
Proof. exact (TRANS (@lem7640147 M N _98425) (@lem7640151 M N _98425)). Qed.
Lemma lem7640153 {M N : Type'} (_98425 : nat) : True = ((term97 M N _98425) = (term135 M N _98425)).
Proof. exact (SYM (@lem7640152 M N _98425)). Qed.
Lemma lem7640154 {M N : Type'} (_98425 : nat) : (term97 M N _98425) = (term135 M N _98425).
Proof. exact (EQ_MP (@lem7640153 M N _98425) (@lem0)). Qed.
Lemma lem7640155 {M N : Type'} (_98425 : nat) (h1 : term26 M N) : term135 M N _98425.
Proof. exact (EQ_MP (@lem7640154 M N _98425) (@lem7639774 M N _98425 h1)). Qed.
Lemma lem7640157 (b : Prop) (a : Prop) : (a \/ b) = (term124 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7640158 {M N : Type'} (_98425 : nat) : (term135 M N _98425) = (term138 M N _98425).
Proof. exact (@lem7640157 (term134 M N _98425) ((term56 M N _98425) = _98425)). Qed.
Lemma lem7640160 (a : Prop) : (term126 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7640161 {M N : Type'} (_98425 : nat) : (term139 M N _98425) = (term7 M N _98425).
Proof. exact (@lem7640160 (term7 M N _98425)). Qed.
Lemma lem7640162 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7640163 {M N : Type'} (_98425 : nat) : (term140 M N _98425) = (term141 M N _98425).
Proof. exact (MK_COMB (@lem7640162) (@lem7640161 M N _98425)). Qed.
Lemma lem7640164 {M N : Type'} (_98425 : nat) : ((term56 M N _98425) = _98425) = ((term56 M N _98425) = _98425).
Proof. exact (eq_refl ((term56 M N _98425) = _98425)). Qed.
Lemma lem7640165 {M N : Type'} (_98425 : nat) : (term138 M N _98425) = (term142 M N _98425).
Proof. exact (MK_COMB (@lem7640163 M N _98425) (@lem7640164 M N _98425)). Qed.
Lemma lem7640166 {M N : Type'} (_98425 : nat) : (term135 M N _98425) = (term142 M N _98425).
Proof. exact (TRANS (@lem7640158 M N _98425) (@lem7640165 M N _98425)). Qed.
Lemma lem7640169 {M N : Type'} (_98425 : nat) (h1 : term26 M N) : term142 M N _98425.
Proof. exact (EQ_MP (@lem7640166 M N _98425) (@lem7640155 M N _98425 h1)). Qed.
Lemma lem7640170 {M N : Type'} (x : nat) (h1 : term26 M N) : term142 M N x.
Proof. exact (@lem7640169 M N x h1). Qed.
Lemma lem7640173 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : (term56 M N x) = x.
Proof. exact (@lem7640170 M N x h1 (@lem7640122 M N x y h2)). Qed.
Lemma lem7640174 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : term143 M N x.
Proof. exact (fun h0 : term144 M N x => @lem7640173 M N x y h1 h2). Qed.
Lemma lem7640176 (p : Prop) : (term119 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7640177 {M N : Type'} (x : nat) : (term143 M N x) = ((term56 M N x) = x).
Proof. exact (@lem7640176 ((term56 M N x) = x)). Qed.
Lemma lem7640178 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : (term56 M N x) = x.
Proof. exact (EQ_MP (@lem7640177 M N x) (@lem7640174 M N x y h1 h2)). Qed.
Lemma lem7640196 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7640197 (y : nat) (x : nat) (z : nat) : (term145 x y z) = (term146 y x z).
Proof. exact (@lem7640196 (y = z) (term112 x z)). Qed.
Lemma lem7640207 (x : nat) (y : nat) : (term147 x y) = (term147 x y).
Proof. exact (eq_refl (term147 x y)). Qed.
Lemma lem7640208 (y : nat) (x : nat) (z : nat) : (term116 x y z) = (term148 y x z).
Proof. exact (MK_COMB (@lem7640207 x y) (@lem7640197 y x z)). Qed.
Lemma lem7640212 (q : Prop) (p : Prop) (r : Prop) : (term149 p q r) = (term149 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7640213 (y : nat) (x : nat) (z : nat) : (term148 y x z) = (term150 y x z).
Proof. exact (@lem7640212 (y = z) (term112 x y) (term112 x z)). Qed.
Lemma lem7640235 (y : nat) (x : nat) (z : nat) : (term116 x y z) = (term150 y x z).
Proof. exact (TRANS (@lem7640208 y x z) (@lem7640213 y x z)). Qed.
Lemma lem7640236 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7640237 (y : nat) (x : nat) (z : nat) : (term151 x y z) = (term152 y x z).
Proof. exact (MK_COMB (@lem7640236) (@lem7640235 y x z)). Qed.
Lemma lem7640259 (y : nat) (x : nat) (z : nat) : (term150 y x z) = (term150 y x z).
Proof. exact (eq_refl (term150 y x z)). Qed.
Lemma lem7640260 (y : nat) (x : nat) (z : nat) : ((term116 x y z) = (term150 y x z)) = ((term150 y x z) = (term150 y x z)).
Proof. exact (MK_COMB (@lem7640237 y x z) (@lem7640259 y x z)). Qed.
Lemma lem7640262 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7640263 (x : Prop) : (x = x) = True.
Proof. exact (@lem7640262 Prop x). Qed.
Lemma lem7640264 (y : nat) (x : nat) (z : nat) : ((term150 y x z) = (term150 y x z)) = True.
Proof. exact (@lem7640263 (term150 y x z)). Qed.
Lemma lem7640265 (y : nat) (x : nat) (z : nat) : ((term116 x y z) = (term150 y x z)) = True.
Proof. exact (TRANS (@lem7640260 y x z) (@lem7640264 y x z)). Qed.
Lemma lem7640266 (y : nat) (x : nat) (z : nat) : True = ((term116 x y z) = (term150 y x z)).
Proof. exact (SYM (@lem7640265 y x z)). Qed.
Lemma lem7640267 (y : nat) (x : nat) (z : nat) : (term116 x y z) = (term150 y x z).
Proof. exact (EQ_MP (@lem7640266 y x z) (@lem0)). Qed.
Lemma lem7640268 (y : nat) (x : nat) (z : nat) : term150 y x z.
Proof. exact (EQ_MP (@lem7640267 y x z) (@lem7640027 x y z)). Qed.
Lemma lem7640270 (b : Prop) (a : Prop) : (a \/ b) = (term124 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7640271 (x : nat) (y : nat) (z : nat) : (term150 y x z) = (term153 x y z).
Proof. exact (@lem7640270 (term154 y x z) (y = z)). Qed.
Lemma lem7640273 (a : Prop) (b : Prop) : (term155 a b) = (term156 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7640274 (y : nat) (x : nat) (z : nat) : (term157 y x z) = (term158 y x z).
Proof. exact (@lem7640273 (term112 x y) (term112 x z)). Qed.
Lemma lem7640276 (a : Prop) : (term126 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7640277 (x : nat) (y : nat) : (term159 x y) = (x = y).
Proof. exact (@lem7640276 (x = y)). Qed.
Lemma lem7640278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7640279 (x : nat) (y : nat) : (term160 x y) = (term161 x y).
Proof. exact (MK_COMB (@lem7640278) (@lem7640277 x y)). Qed.
Lemma lem7640281 (a : Prop) : (term126 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7640282 (x : nat) (z : nat) : (term159 x z) = (x = z).
Proof. exact (@lem7640281 (x = z)). Qed.
Lemma lem7640283 (y : nat) (x : nat) (z : nat) : (term158 y x z) = (term162 y x z).
Proof. exact (MK_COMB (@lem7640279 x y) (@lem7640282 x z)). Qed.
Lemma lem7640284 (y : nat) (x : nat) (z : nat) : (term157 y x z) = (term162 y x z).
Proof. exact (TRANS (@lem7640274 y x z) (@lem7640283 y x z)). Qed.
Lemma lem7640285 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7640286 (y : nat) (x : nat) (z : nat) : (term163 y x z) = (term164 y x z).
Proof. exact (MK_COMB (@lem7640285) (@lem7640284 y x z)). Qed.
Lemma lem7640287 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7640288 (x : nat) (y : nat) (z : nat) : (term153 x y z) = (term165 x y z).
Proof. exact (MK_COMB (@lem7640286 y x z) (@lem7640287 y z)). Qed.
Lemma lem7640289 (x : nat) (y : nat) (z : nat) : (term150 y x z) = (term165 x y z).
Proof. exact (TRANS (@lem7640271 x y z) (@lem7640288 x y z)). Qed.
Lemma lem7640291 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : term166 M N y x.
Proof. exact (conj (@lem7640115 M N x y h2) (@lem7640178 M N x y h1 h2)). Qed.
Lemma lem7640293 (x : nat) (y : nat) (z : nat) : term165 x y z.
Proof. exact (EQ_MP (@lem7640289 x y z) (@lem7640268 y x z)). Qed.
Lemma lem7640294 {M N : Type'} (y : nat) (x : nat) : term167 M N y x.
Proof. exact (@lem7640293 (term56 M N x) (term56 M N y) x). Qed.
Lemma lem7640297 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : (term56 M N y) = x.
Proof. exact (@lem7640294 M N y x (@lem7640291 M N x y h1 h2)). Qed.
Lemma lem7640298 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : term168 M N y x.
Proof. exact (fun h0 : term169 M N y x => @lem7640297 M N x y h1 h2). Qed.
Lemma lem7640300 (p : Prop) : (term119 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7640301 {M N : Type'} (y : nat) (x : nat) : (term168 M N y x) = ((term56 M N y) = x).
Proof. exact (@lem7640300 ((term56 M N y) = x)). Qed.
Lemma lem7640302 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : (term56 M N y) = x.
Proof. exact (EQ_MP (@lem7640301 M N y x) (@lem7640298 M N x y h1 h2)). Qed.
Lemma lem7640304 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : term7 M N y.
Proof. exact (proj1 (@lem7639443 M N x y h1)). Qed.
Lemma lem7640305 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : term133 M N y.
Proof. exact (fun h0 : term134 M N y => @lem7640304 M N x y h1). Qed.
Lemma lem7640307 (p : Prop) : (term119 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7640308 {M N : Type'} (y : nat) : (term133 M N y) = (term7 M N y).
Proof. exact (@lem7640307 (term7 M N y)). Qed.
Lemma lem7640309 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : term7 M N y.
Proof. exact (EQ_MP (@lem7640308 M N y) (@lem7640305 M N x y h1)). Qed.
Lemma lem7640311 {M N : Type'} (_98425 : nat) (h1 : term26 M N) : term142 M N _98425.
Proof. exact (EQ_MP (@lem7640166 M N _98425) (@lem7640155 M N _98425 h1)). Qed.
Lemma lem7640312 {M N : Type'} (y : nat) (h1 : term26 M N) : term142 M N y.
Proof. exact (@lem7640311 M N y h1). Qed.
Lemma lem7640315 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : (term56 M N y) = y.
Proof. exact (@lem7640312 M N y h1 (@lem7640309 M N x y h2)). Qed.
Lemma lem7640316 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : term143 M N y.
Proof. exact (fun h0 : term144 M N y => @lem7640315 M N x y h1 h2). Qed.
Lemma lem7640318 (p : Prop) : (term119 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7640319 {M N : Type'} (y : nat) : (term143 M N y) = ((term56 M N y) = y).
Proof. exact (@lem7640318 ((term56 M N y) = y)). Qed.
Lemma lem7640320 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : (term56 M N y) = y.
Proof. exact (EQ_MP (@lem7640319 M N y) (@lem7640316 M N x y h1 h2)). Qed.
Lemma lem7640321 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : term170 M N x y.
Proof. exact (conj (@lem7640302 M N x y h1 h2) (@lem7640320 M N x y h1 h2)). Qed.
Lemma lem7640323 (x : nat) (y : nat) (z : nat) : term165 x y z.
Proof. exact (EQ_MP (@lem7640289 x y z) (@lem7640268 y x z)). Qed.
Lemma lem7640324 {M N : Type'} (x : nat) (y : nat) : term171 M N x y.
Proof. exact (@lem7640323 (term56 M N y) x y). Qed.
Lemma lem7640327 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : x = y.
Proof. exact (@lem7640324 M N x y (@lem7640321 M N x y h1 h2)). Qed.
Lemma lem7640328 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : term172 x y.
Proof. exact (fun h0 : term112 x y => @lem7640327 M N x y h1 h2). Qed.
Lemma lem7640330 (p : Prop) : (term119 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7640331 (x : nat) (y : nat) : (term172 x y) = (x = y).
Proof. exact (@lem7640330 (x = y)). Qed.
Lemma lem7640332 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : x = y.
Proof. exact (EQ_MP (@lem7640331 x y) (@lem7640328 M N x y h1 h2)). Qed.
Lemma lem7640335 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7640337 (x : nat) (y : nat) : (term112 x y) = (term173 x y).
Proof. exact (@lem7640335 (x = y)). Qed.
Lemma lem7640340 {M N : Type'} (x : nat) (y : nat) (h1 : term64 M N x y) : term173 x y.
Proof. exact (EQ_MP (@lem7640337 x y) (@lem7639740 M N x y h1)). Qed.
Lemma lem7640343 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : False.
Proof. exact (@lem7640340 M N x y h2 (@lem7640332 M N x y h1 h2)). Qed.
Lemma lem7640344 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : term174.
Proof. exact (fun h0 : ~ False => @lem7640343 M N x y h1 h2). Qed.
Lemma lem7640346 (p : Prop) : (term119 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7640347 : term174 = False.
Proof. exact (@lem7640346 False). Qed.
Lemma lem7640348 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : False.
Proof. exact (EQ_MP (@lem7640347) (@lem7640344 M N x y h1 h2)). Qed.
Lemma lem7640349 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : (term64 M N x y) = False.
Proof. exact (prop_ext (fun h3 : term64 M N x y => @lem7640348 M N x y h1 h2) (fun h3 : False => @lem7639440 M N x y h2)). Qed.
Lemma lem7640350 {M N : Type'} (x : nat) (y : nat) (h1 : term26 M N) (h2 : term64 M N x y) : False.
Proof. exact (EQ_MP (@lem7640349 M N x y h1 h2) (@lem7639440 M N x y h2)). Qed.
Lemma lem7640351 {M N : Type'} (x : nat) (h1 : term73 M N x) (h2 : term26 M N) : False.
Proof. exact (ex_elim (@lem7638801 M N x h1) (fun y : nat => fun h0 : term72 M N x y => @lem7640350 M N x y h2 h0)). Qed.
Lemma lem7640352 {M N : Type'} (h1 : term25 M N) (h2 : term26 M N) : False.
Proof. exact (ex_elim (@lem7637852 M N h1) (fun x : nat => fun h0 : term78 M N x => @lem7640351 M N x h0 h2)). Qed.
Lemma lem7640353 {B M N : Type'} (h1 : term25 M N) (h2 : term26 M N) : term32 B N.
Proof. exact (fun h0 : term27 B N => @lem7640352 M N h1 h2). Qed.
Lemma lem7640354 {B N : Type'} : (term32 B N) = (term33 B N).
Proof. exact (@lem69 (term27 B N)). Qed.
Lemma lem7640355 {B M N : Type'} (h1 : term25 M N) (h2 : term26 M N) : term33 B N.
Proof. exact (EQ_MP (@lem7640354 B N) (@lem7640353 B M N h1 h2)). Qed.
Lemma lem7640356 {B M N : Type'} (h1 : term25 M N) : term36 B M N.
Proof. exact (fun h0 : term26 M N => @lem7640355 B M N h1 h0). Qed.
Lemma lem7640357 {B M N : Type'} (h1 : term25 M N) : term39 B M N.
Proof. exact (fun h0 : term27 B M => @lem7640356 B M N h1). Qed.
Lemma lem7640358 {A B M N : Type'} (h1 : term25 M N) : term41 A B M N.
Proof. exact (fun h0 : term26 A N => @lem7640357 B M N h1). Qed.
Lemma lem7640359 {A B M N : Type'} (h1 : term25 M N) : term43 A B M N.
Proof. exact (fun h0 : term26 A M => @lem7640358 A B M N h1). Qed.
Lemma lem7640360 {A B M N : Type'} (h1 : term25 M N) : term45 A B M N.
Proof. exact (fun h0 : term26 A B => @lem7640359 A B M N h1). Qed.
Lemma lem7640361 {A B M N : Type'} : term47 A B M N.
Proof. exact (fun h0 : term25 M N => @lem7640360 A B M N h0). Qed.
Lemma lem7640362 {A B M N : Type'} : term28 A B M N.
Proof. exact (EQ_MP (@lem7637753 A B M N) (@lem7640361 A B M N)). Qed.
Lemma lem7640364 {A B M N : Type'} : term28 A B M N.
Proof. exact (@lem7637387 A B M N (@lem7640362 A B M N)). Qed.
Lemma lem7640365 {A B M N : Type'} (h1 : term25 M N) : term44 A B M N.
Proof. exact (@lem7640364 A B M N (@lem7637361 M N h1)). Qed.
Lemma lem7640366 {A B M N : Type'} (h1 : term25 M N) : term42 A B M N.
Proof. exact (@lem7640365 A B M N h1 (@lem7631335 A B)). Qed.
Lemma lem7640367 {A B M N : Type'} (h1 : term25 M N) : term40 A B M N.
Proof. exact (@lem7640366 A B M N h1 (@lem7637368 A M)). Qed.
Lemma lem7640368 {B M N : Type'} (h1 : term25 M N) : term38 B M N.
Proof. exact (@lem7640367 Prop B M N h1 (@lem7637369 Prop N)). Qed.
Lemma lem7640369 {B M N : Type'} (h1 : term25 M N) : term35 B M N.
Proof. exact (@lem7640368 B M N h1 (@lem7637364 B M)). Qed.
Lemma lem7640370 {B M N : Type'} (h1 : term25 M N) : term32 B N.
Proof. exact (@lem7640369 B M N h1 (@lem7637362 M N)). Qed.
Lemma lem7640371 {M N : Type'} (h1 : term25 M N) : False.
Proof. exact (@lem7640370 Prop M N h1 (@lem7637365 Prop N)). Qed.
Lemma lem7640372 {M N : Type'} (h1 : term25 M N) : (term25 M N) = False.
Proof. exact (prop_ext (fun h2 : term25 M N => @lem7640371 M N h1) (fun h2 : False => @lem7637361 M N h1)). Qed.
Lemma lem7640373 {M N : Type'} (h1 : term25 M N) : False.
Proof. exact (EQ_MP (@lem7640372 M N h1) (@lem7637361 M N h1)). Qed.
Lemma lem7640374 {M N : Type'} : term24 M N.
Proof. exact (fun h0 : term25 M N => @lem7640373 M N h0). Qed.
Lemma lem7640375 {M N : Type'} : term16 M N.
Proof. exact (EQ_MP (@lem7637360 M N) (@lem7640374 M N)). Qed.
Lemma lem7640376 {M N : Type'} : term20 M N.
Proof. exact (EQ_MP (@lem7637356 M N) (@lem7640375 M N)). Qed.
Lemma lem7640377 {M N : Type'} : term20 M N.
Proof. exact (EQ_MP (@lem7637308 M N) (@lem7640376 M N)). Qed.
Lemma lem7640378 {M N : Type'} : term175 M N.
Proof. exact (@lem7637210 M N (@lem7640377 M N)). Qed.
