Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_PCROSS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_PCROSS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm19490_spec.
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
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem8027157 {_100044 : Type'} (s : _100044 -> Prop) : term0 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem8027158 {_100044 : Type'} (s : _100044 -> Prop) : (term0 _100044 s) = (term1 _100044 s).
Proof. exact (eq_refl (term0 _100044 s)). Qed.
Lemma lem8027159 {_100044 : Type'} (s : _100044 -> Prop) : term1 _100044 s.
Proof. exact (EQ_MP (@lem8027158 _100044 s) (@lem8027157 _100044 s)). Qed.
Lemma lem8027160 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term2 _100044 s n.
Proof. exact (@lem8027159 _100044 s n). Qed.
Lemma lem8027161 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term2 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term3 _100044 s n)).
Proof. exact (eq_refl (term2 _100044 s n)). Qed.
Lemma lem8027184 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term3 _100044 s n).
Proof. exact (EQ_MP (@lem8027161 _100044 s n) (@lem8027160 _100044 s n)). Qed.
Lemma lem8027185 {A M : Type'} (s : type24 A M) (n : nat) : (@HAS_SIZE (cart A M) s n) = (term4 A M s n).
Proof. exact (@lem8027184 (cart A M) s n). Qed.
Lemma lem8027186 {A M : Type'} (s : type24 A M) (m : nat) : (@HAS_SIZE (cart A M) s m) = (term4 A M s m).
Proof. exact (@lem8027185 A M s m). Qed.
Lemma lem8027191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8027192 {A M : Type'} (s : type24 A M) (m : nat) : (term5 A M s m) = (term6 A M s m).
Proof. exact (MK_COMB (@lem8027191) (@lem8027186 A M s m)). Qed.
Lemma lem8027194 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term3 _100044 s n).
Proof. exact (EQ_MP (@lem8027161 _100044 s n) (@lem8027160 _100044 s n)). Qed.
Lemma lem8027195 {A N : Type'} (s : type24 A N) (n : nat) : (@HAS_SIZE (cart A N) s n) = (term4 A N s n).
Proof. exact (@lem8027194 (cart A N) s n). Qed.
Lemma lem8027196 {A N : Type'} (t : type24 A N) (n : nat) : (@HAS_SIZE (cart A N) t n) = (term4 A N t n).
Proof. exact (@lem8027195 A N t n). Qed.
Lemma lem8027201 {A M N : Type'} (s : type24 A M) (m : nat) (t : type24 A N) (n : nat) : (term7 A M N s m t n) = (term8 A M N s m t n).
Proof. exact (MK_COMB (@lem8027192 A M s m) (@lem8027196 A N t n)). Qed.
Lemma lem8027204 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8027205 {A M N : Type'} (s : type24 A M) (m : nat) (t : type24 A N) (n : nat) : (term9 A M N s m t n) = (term10 A M N s m t n).
Proof. exact (MK_COMB (@lem8027204) (@lem8027201 A M N s m t n)). Qed.
Lemma lem8027207 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term3 _100044 s n).
Proof. exact (EQ_MP (@lem8027161 _100044 s n) (@lem8027160 _100044 s n)). Qed.
Lemma lem8027208 {A M N : Type'} (s : type16 A M N) (n : nat) : (@HAS_SIZE (cart A (finite_sum M N)) s n) = (term11 A M N s n).
Proof. exact (@lem8027207 (type2 A M N) s n). Qed.
Lemma lem8027209 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : (term12 A M N s t m n) = (term13 A M N s t m n).
Proof. exact (@lem8027208 A M N (@PCROSS A M N s t) (Nat.mul m n)). Qed.
Lemma lem8027214 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : (term14 A M N s t m n) = (term15 A M N s t m n).
Proof. exact (MK_COMB (@lem8027205 A M N s m t n) (@lem8027209 A M N s t m n)). Qed.
Lemma lem8027217 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) : (term16 A M N s t m) = (term17 A M N s t m).
Proof. exact (fun_ext (fun n : nat => @lem8027214 A M N s t m n)). Qed.
Lemma lem8027218 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8027219 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) : (term18 A M N s t m) = (term19 A M N s t m).
Proof. exact (MK_COMB (@lem8027218) (@lem8027217 A M N s t m)). Qed.
Lemma lem8027224 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term20 A M N s t) = (term21 A M N s t).
Proof. exact (fun_ext (fun m : nat => @lem8027219 A M N s t m)). Qed.
Lemma lem8027225 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8027226 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term22 A M N s t) = (term23 A M N s t).
Proof. exact (MK_COMB (@lem8027225) (@lem8027224 A M N s t)). Qed.
Lemma lem8027231 {A M N : Type'} (s : type24 A M) : (term24 A M N s) = (term25 A M N s).
Proof. exact (fun_ext (fun t : type24 A N => @lem8027226 A M N s t)). Qed.
Lemma lem8027232 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem8027233 {A M N : Type'} (s : type24 A M) : (term26 A M N s) = (term27 A M N s).
Proof. exact (MK_COMB (@lem8027232 A N) (@lem8027231 A M N s)). Qed.
Lemma lem8027238 {A M N : Type'} : (term28 A M N) = (term29 A M N).
Proof. exact (fun_ext (fun s : type24 A M => @lem8027233 A M N s)). Qed.
Lemma lem8027239 {A M : Type'} : (@all ((cart A M) -> Prop)) = (@all ((cart A M) -> Prop)).
Proof. exact (eq_refl (@all ((cart A M) -> Prop))). Qed.
Lemma lem8027240 {A M N : Type'} : (term30 A M N) = (term31 A M N).
Proof. exact (MK_COMB (@lem8027239 A M) (@lem8027238 A M N)). Qed.
Lemma lem8027245 {A M N : Type'} : term31 A M N.
Proof. exact (EQ_MP (@lem8027240 A M N) (@lem8027156 A M N)). Qed.
Lemma lem8027246 (t1 : Prop) : term32 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem8027247 (t1 : Prop) : (term32 t1) = (term33 t1).
Proof. exact (eq_refl (term32 t1)). Qed.
Lemma lem8027248 (t1 : Prop) : term33 t1.
Proof. exact (EQ_MP (@lem8027247 t1) (@lem8027246 t1)). Qed.
Lemma lem8027249 (t1 : Prop) (t2 : Prop) : term34 t1 t2.
Proof. exact (@lem8027248 t1 t2). Qed.
Lemma lem8027250 (t1 : Prop) (t2 : Prop) : (term34 t1 t2) = (term35 t1 t2).
Proof. exact (eq_refl (term34 t1 t2)). Qed.
Lemma lem8027251 (t1 : Prop) (t2 : Prop) : term35 t1 t2.
Proof. exact (EQ_MP (@lem8027250 t1 t2) (@lem8027249 t1 t2)). Qed.
Lemma lem8027252 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term36 t1 t2 t3.
Proof. exact (@lem8027251 t1 t2 t3). Qed.
Lemma lem8027253 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term36 t1 t2 t3) = ((term37 t1 t2 t3) = (term38 t1 t2 t3)).
Proof. exact (eq_refl (term36 t1 t2 t3)). Qed.
Lemma lem8027254 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term37 t1 t2 t3) = (term38 t1 t2 t3).
Proof. exact (EQ_MP (@lem8027253 t1 t2 t3) (@lem8027252 t1 t2 t3)). Qed.
Lemma lem8027255 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term38 t1 t2 t3) = (term37 t1 t2 t3).
Proof. exact (SYM (@lem8027254 t1 t2 t3)). Qed.
Lemma lem8027257 (p : Prop) : p = (term39 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8027258 {A M N : Type'} : (term40 A M N) = (term41 A M N).
Proof. exact (@lem8027257 (term40 A M N)). Qed.
Lemma lem8027259 {A M N : Type'} : (term41 A M N) = (term40 A M N).
Proof. exact (SYM (@lem8027258 A M N)). Qed.
Lemma lem8027260 {A M N : Type'} (h1 : term42 A M N) : term42 A M N.
Proof. exact (h1). Qed.
Lemma lem8027261 {A M N : Type'} : term31 A M N.
Proof. exact (@lem8027245 A M N). Qed.
Lemma lem8027262 {A N : Type'} : term43 A N.
Proof. exact (@lem8027245 A N N). Qed.
Lemma lem8027263 {A M N : Type'} : term44 A M N.
Proof. exact (@lem8027245 A (finite_sum M N) N). Qed.
Lemma lem8027264 {A M : Type'} : term43 A M.
Proof. exact (@lem8027245 A M M). Qed.
Lemma lem8027266 {A M N : Type'} : term45 A M N.
Proof. exact (@lem8027245 A M (finite_sum M N)). Qed.
Lemma lem8027271 {A M N : Type'} (h1 : term46 A M N) : term46 A M N.
Proof. exact (h1). Qed.
Lemma lem8027272 {A M N : Type'} : term47 A M N.
Proof. exact (fun h0 : term46 A M N => @lem8027271 A M N h0). Qed.
Lemma lem8027273 {A M N : Type'} (h1 : term47 A M N) : term47 A M N.
Proof. exact (h1). Qed.
Lemma lem8027274 {A M N : Type'} (h1 : term46 A M N) : term46 A M N.
Proof. exact (h1). Qed.
Lemma lem8027275 {A M N : Type'} (h1 : term46 A M N) (h2 : term47 A M N) : term46 A M N.
Proof. exact (@lem8027273 A M N h2 (@lem8027274 A M N h1)). Qed.
Lemma lem8027276 {A M N : Type'} (h1 : term46 A M N) : term48 A M N.
Proof. exact (fun h0 : term47 A M N => @lem8027275 A M N h1 h0). Qed.
Lemma lem8027277 {A M N : Type'} (h1 : term47 A M N) : term47 A M N.
Proof. exact (h1). Qed.
Lemma lem8027278 {A M N : Type'} (h1 : term46 A M N) (h2 : term47 A M N) : term46 A M N.
Proof. exact (@lem8027276 A M N h1 (@lem8027277 A M N h2)). Qed.
Lemma lem8027279 {A M N : Type'} (h1 : term47 A M N) : term47 A M N.
Proof. exact (fun h0 : term46 A M N => @lem8027278 A M N h0 h1). Qed.
Lemma lem8027280 {A M N : Type'} : term49 A M N.
Proof. exact (fun h0 : term47 A M N => @lem8027279 A M N h0). Qed.
Lemma lem8027283 {A M N : Type'} : term47 A M N.
Proof. exact (@lem8027280 A M N (@lem8027272 A M N)). Qed.
Lemma lem8027284 {A M N : Type'} : term47 A M N.
Proof. exact (@lem8027283 A M N). Qed.
Lemma lem8027412 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8027413 {A M N : Type'} : (term50 A M N) = (term51 A M N).
Proof. exact (@lem8027412 (term44 A M N)). Qed.
Lemma lem8027440 {A N : Type'} : (term52 A N) = (term52 A N).
Proof. exact (eq_refl (term52 A N)). Qed.
Lemma lem8027441 {A M N : Type'} : (term53 A M N) = (term54 A M N).
Proof. exact (MK_COMB (@lem8027440 A N) (@lem8027413 A M N)). Qed.
Lemma lem8027444 {A M N : Type'} : (term55 A M N) = (term55 A M N).
Proof. exact (eq_refl (term55 A M N)). Qed.
Lemma lem8027445 {A M N : Type'} : (term56 A M N) = (term57 A M N).
Proof. exact (MK_COMB (@lem8027444 A M N) (@lem8027441 A M N)). Qed.
Lemma lem8027448 {A M N : Type'} : (term58 A M N) = (term58 A M N).
Proof. exact (eq_refl (term58 A M N)). Qed.
Lemma lem8027449 {A M N : Type'} : (term59 A M N) = (term60 A M N).
Proof. exact (MK_COMB (@lem8027448 A M N) (@lem8027445 A M N)). Qed.
Lemma lem8027452 {A M : Type'} : (term52 A M) = (term52 A M).
Proof. exact (eq_refl (term52 A M)). Qed.
Lemma lem8027453 {A M N : Type'} : (term61 A M N) = (term62 A M N).
Proof. exact (MK_COMB (@lem8027452 A M) (@lem8027449 A M N)). Qed.
Lemma lem8027456 {A M N : Type'} : (term63 A M N) = (term63 A M N).
Proof. exact (eq_refl (term63 A M N)). Qed.
Lemma lem8027463 {A M N : Type'} : (term46 A M N) = (term64 A M N).
Proof. exact (MK_COMB (@lem8027456 A M N) (@lem8027453 A M N)). Qed.
Lemma lem8027484 {A M N : Type'} (s : type16 A M N) (t : type24 A N) (m : nat) (n : nat) : (term65 A M N s t m n) = (term65 A M N s t m n).
Proof. exact (eq_refl (term65 A M N s t m n)). Qed.
Lemma lem8027485 {A M N : Type'} (s : type16 A M N) (t : type24 A N) (m : nat) : (term66 A M N s t m) = (term66 A M N s t m).
Proof. exact (fun_ext (fun n : nat => @lem8027484 A M N s t m n)). Qed.
Lemma lem8027486 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8027487 {A M N : Type'} (s : type16 A M N) (t : type24 A N) (m : nat) : (term67 A M N s t m) = (term67 A M N s t m).
Proof. exact (MK_COMB (@lem8027486) (@lem8027485 A M N s t m)). Qed.
Lemma lem8027488 {A M N : Type'} (s : type16 A M N) (t : type24 A N) : (term68 A M N s t) = (term68 A M N s t).
Proof. exact (fun_ext (fun m : nat => @lem8027487 A M N s t m)). Qed.
Lemma lem8027489 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8027490 {A M N : Type'} (s : type16 A M N) (t : type24 A N) : (term69 A M N s t) = (term69 A M N s t).
Proof. exact (MK_COMB (@lem8027489) (@lem8027488 A M N s t)). Qed.
Lemma lem8027491 {A M N : Type'} (s : type16 A M N) : (term70 A M N s) = (term70 A M N s).
Proof. exact (fun_ext (fun t : type24 A N => @lem8027490 A M N s t)). Qed.
Lemma lem8027492 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem8027493 {A M N : Type'} (s : type16 A M N) : (term71 A M N s) = (term71 A M N s).
Proof. exact (MK_COMB (@lem8027492 A N) (@lem8027491 A M N s)). Qed.
Lemma lem8027494 {A M N : Type'} : (term72 A M N) = (term72 A M N).
Proof. exact (fun_ext (fun s : type16 A M N => @lem8027493 A M N s)). Qed.
Lemma lem8027495 {A M N : Type'} : (@all ((cart A (finite_sum M N)) -> Prop)) = (@all ((cart A (finite_sum M N)) -> Prop)).
Proof. exact (eq_refl (@all ((cart A (finite_sum M N)) -> Prop))). Qed.
Lemma lem8027496 {A M N : Type'} : (term44 A M N) = (term44 A M N).
Proof. exact (MK_COMB (@lem8027495 A M N) (@lem8027494 A M N)). Qed.
Lemma lem8027497 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8027498 {A M N : Type'} : (term51 A M N) = (term51 A M N).
Proof. exact (MK_COMB (@lem8027497) (@lem8027496 A M N)). Qed.
Lemma lem8027519 {A N : Type'} (s : type24 A N) (t : type24 A N) (m : nat) (n : nat) : (term73 A N s t m n) = (term73 A N s t m n).
Proof. exact (eq_refl (term73 A N s t m n)). Qed.
Lemma lem8027520 {A N : Type'} (s : type24 A N) (t : type24 A N) (m : nat) : (term74 A N s t m) = (term74 A N s t m).
Proof. exact (fun_ext (fun n : nat => @lem8027519 A N s t m n)). Qed.
Lemma lem8027521 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8027522 {A N : Type'} (s : type24 A N) (t : type24 A N) (m : nat) : (term75 A N s t m) = (term75 A N s t m).
Proof. exact (MK_COMB (@lem8027521) (@lem8027520 A N s t m)). Qed.
Lemma lem8027523 {A N : Type'} (s : type24 A N) (t : type24 A N) : (term76 A N s t) = (term76 A N s t).
Proof. exact (fun_ext (fun m : nat => @lem8027522 A N s t m)). Qed.
Lemma lem8027524 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8027525 {A N : Type'} (s : type24 A N) (t : type24 A N) : (term77 A N s t) = (term77 A N s t).
Proof. exact (MK_COMB (@lem8027524) (@lem8027523 A N s t)). Qed.
Lemma lem8027526 {A N : Type'} (s : type24 A N) : (term78 A N s) = (term78 A N s).
Proof. exact (fun_ext (fun t : type24 A N => @lem8027525 A N s t)). Qed.
Lemma lem8027527 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem8027528 {A N : Type'} (s : type24 A N) : (term79 A N s) = (term79 A N s).
Proof. exact (MK_COMB (@lem8027527 A N) (@lem8027526 A N s)). Qed.
Lemma lem8027529 {A N : Type'} : (term80 A N) = (term80 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem8027528 A N s)). Qed.
Lemma lem8027530 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem8027531 {A N : Type'} : (term43 A N) = (term43 A N).
Proof. exact (MK_COMB (@lem8027530 A N) (@lem8027529 A N)). Qed.
Lemma lem8027532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8027533 {A N : Type'} : (term52 A N) = (term52 A N).
Proof. exact (MK_COMB (@lem8027532) (@lem8027531 A N)). Qed.
Lemma lem8027534 {A M N : Type'} : (term54 A M N) = (term54 A M N).
Proof. exact (MK_COMB (@lem8027533 A N) (@lem8027498 A M N)). Qed.
Lemma lem8027555 {A M N : Type'} (s : type24 A M) (t : type16 A M N) (m : nat) (n : nat) : (term81 A M N s t m n) = (term81 A M N s t m n).
Proof. exact (eq_refl (term81 A M N s t m n)). Qed.
Lemma lem8027556 {A M N : Type'} (s : type24 A M) (t : type16 A M N) (m : nat) : (term82 A M N s t m) = (term82 A M N s t m).
Proof. exact (fun_ext (fun n : nat => @lem8027555 A M N s t m n)). Qed.
Lemma lem8027557 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8027558 {A M N : Type'} (s : type24 A M) (t : type16 A M N) (m : nat) : (term83 A M N s t m) = (term83 A M N s t m).
Proof. exact (MK_COMB (@lem8027557) (@lem8027556 A M N s t m)). Qed.
Lemma lem8027559 {A M N : Type'} (s : type24 A M) (t : type16 A M N) : (term84 A M N s t) = (term84 A M N s t).
Proof. exact (fun_ext (fun m : nat => @lem8027558 A M N s t m)). Qed.
Lemma lem8027560 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8027561 {A M N : Type'} (s : type24 A M) (t : type16 A M N) : (term85 A M N s t) = (term85 A M N s t).
Proof. exact (MK_COMB (@lem8027560) (@lem8027559 A M N s t)). Qed.
Lemma lem8027562 {A M N : Type'} (s : type24 A M) : (term86 A M N s) = (term86 A M N s).
Proof. exact (fun_ext (fun t : type16 A M N => @lem8027561 A M N s t)). Qed.
Lemma lem8027563 {A M N : Type'} : (@all ((cart A (finite_sum M N)) -> Prop)) = (@all ((cart A (finite_sum M N)) -> Prop)).
Proof. exact (eq_refl (@all ((cart A (finite_sum M N)) -> Prop))). Qed.
Lemma lem8027564 {A M N : Type'} (s : type24 A M) : (term87 A M N s) = (term87 A M N s).
Proof. exact (MK_COMB (@lem8027563 A M N) (@lem8027562 A M N s)). Qed.
Lemma lem8027565 {A M N : Type'} : (term88 A M N) = (term88 A M N).
Proof. exact (fun_ext (fun s : type24 A M => @lem8027564 A M N s)). Qed.
Lemma lem8027566 {A M : Type'} : (@all ((cart A M) -> Prop)) = (@all ((cart A M) -> Prop)).
Proof. exact (eq_refl (@all ((cart A M) -> Prop))). Qed.
Lemma lem8027567 {A M N : Type'} : (term45 A M N) = (term45 A M N).
Proof. exact (MK_COMB (@lem8027566 A M) (@lem8027565 A M N)). Qed.
Lemma lem8027568 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8027569 {A M N : Type'} : (term55 A M N) = (term55 A M N).
Proof. exact (MK_COMB (@lem8027568) (@lem8027567 A M N)). Qed.
Lemma lem8027570 {A M N : Type'} : (term57 A M N) = (term57 A M N).
Proof. exact (MK_COMB (@lem8027569 A M N) (@lem8027534 A M N)). Qed.
Lemma lem8027591 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : (term15 A M N s t m n) = (term15 A M N s t m n).
Proof. exact (eq_refl (term15 A M N s t m n)). Qed.
Lemma lem8027592 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) : (term17 A M N s t m) = (term17 A M N s t m).
Proof. exact (fun_ext (fun n : nat => @lem8027591 A M N s t m n)). Qed.
Lemma lem8027593 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8027594 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) : (term19 A M N s t m) = (term19 A M N s t m).
Proof. exact (MK_COMB (@lem8027593) (@lem8027592 A M N s t m)). Qed.
Lemma lem8027595 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term21 A M N s t) = (term21 A M N s t).
Proof. exact (fun_ext (fun m : nat => @lem8027594 A M N s t m)). Qed.
Lemma lem8027596 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8027597 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term23 A M N s t) = (term23 A M N s t).
Proof. exact (MK_COMB (@lem8027596) (@lem8027595 A M N s t)). Qed.
Lemma lem8027598 {A M N : Type'} (s : type24 A M) : (term25 A M N s) = (term25 A M N s).
Proof. exact (fun_ext (fun t : type24 A N => @lem8027597 A M N s t)). Qed.
Lemma lem8027599 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem8027600 {A M N : Type'} (s : type24 A M) : (term27 A M N s) = (term27 A M N s).
Proof. exact (MK_COMB (@lem8027599 A N) (@lem8027598 A M N s)). Qed.
Lemma lem8027601 {A M N : Type'} : (term29 A M N) = (term29 A M N).
Proof. exact (fun_ext (fun s : type24 A M => @lem8027600 A M N s)). Qed.
Lemma lem8027602 {A M : Type'} : (@all ((cart A M) -> Prop)) = (@all ((cart A M) -> Prop)).
Proof. exact (eq_refl (@all ((cart A M) -> Prop))). Qed.
Lemma lem8027603 {A M N : Type'} : (term31 A M N) = (term31 A M N).
Proof. exact (MK_COMB (@lem8027602 A M) (@lem8027601 A M N)). Qed.
Lemma lem8027604 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8027605 {A M N : Type'} : (term58 A M N) = (term58 A M N).
Proof. exact (MK_COMB (@lem8027604) (@lem8027603 A M N)). Qed.
Lemma lem8027606 {A M N : Type'} : (term60 A M N) = (term60 A M N).
Proof. exact (MK_COMB (@lem8027605 A M N) (@lem8027570 A M N)). Qed.
Lemma lem8027627 {A M : Type'} (s : type24 A M) (t : type24 A M) (m : nat) (n : nat) : (term73 A M s t m n) = (term73 A M s t m n).
Proof. exact (eq_refl (term73 A M s t m n)). Qed.
Lemma lem8027628 {A M : Type'} (s : type24 A M) (t : type24 A M) (m : nat) : (term74 A M s t m) = (term74 A M s t m).
Proof. exact (fun_ext (fun n : nat => @lem8027627 A M s t m n)). Qed.
Lemma lem8027629 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8027630 {A M : Type'} (s : type24 A M) (t : type24 A M) (m : nat) : (term75 A M s t m) = (term75 A M s t m).
Proof. exact (MK_COMB (@lem8027629) (@lem8027628 A M s t m)). Qed.
Lemma lem8027631 {A M : Type'} (s : type24 A M) (t : type24 A M) : (term76 A M s t) = (term76 A M s t).
Proof. exact (fun_ext (fun m : nat => @lem8027630 A M s t m)). Qed.
Lemma lem8027632 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8027633 {A M : Type'} (s : type24 A M) (t : type24 A M) : (term77 A M s t) = (term77 A M s t).
Proof. exact (MK_COMB (@lem8027632) (@lem8027631 A M s t)). Qed.
Lemma lem8027634 {A M : Type'} (s : type24 A M) : (term78 A M s) = (term78 A M s).
Proof. exact (fun_ext (fun t : type24 A M => @lem8027633 A M s t)). Qed.
Lemma lem8027635 {A M : Type'} : (@all ((cart A M) -> Prop)) = (@all ((cart A M) -> Prop)).
Proof. exact (eq_refl (@all ((cart A M) -> Prop))). Qed.
Lemma lem8027636 {A M : Type'} (s : type24 A M) : (term79 A M s) = (term79 A M s).
Proof. exact (MK_COMB (@lem8027635 A M) (@lem8027634 A M s)). Qed.
Lemma lem8027637 {A M : Type'} : (term80 A M) = (term80 A M).
Proof. exact (fun_ext (fun s : type24 A M => @lem8027636 A M s)). Qed.
Lemma lem8027638 {A M : Type'} : (@all ((cart A M) -> Prop)) = (@all ((cart A M) -> Prop)).
Proof. exact (eq_refl (@all ((cart A M) -> Prop))). Qed.
Lemma lem8027639 {A M : Type'} : (term43 A M) = (term43 A M).
Proof. exact (MK_COMB (@lem8027638 A M) (@lem8027637 A M)). Qed.
Lemma lem8027640 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8027641 {A M : Type'} : (term52 A M) = (term52 A M).
Proof. exact (MK_COMB (@lem8027640) (@lem8027639 A M)). Qed.
Lemma lem8027642 {A M N : Type'} : (term62 A M N) = (term62 A M N).
Proof. exact (MK_COMB (@lem8027641 A M) (@lem8027606 A M N)). Qed.
Lemma lem8027651 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term89 A M N s t) = (term89 A M N s t).
Proof. exact (eq_refl (term89 A M N s t)). Qed.
Lemma lem8027652 {A M N : Type'} (s : type24 A M) : (term90 A M N s) = (term90 A M N s).
Proof. exact (fun_ext (fun t : type24 A N => @lem8027651 A M N s t)). Qed.
Lemma lem8027653 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem8027654 {A M N : Type'} (s : type24 A M) : (term91 A M N s) = (term91 A M N s).
Proof. exact (MK_COMB (@lem8027653 A N) (@lem8027652 A M N s)). Qed.
Lemma lem8027655 {A M N : Type'} : (term92 A M N) = (term92 A M N).
Proof. exact (fun_ext (fun s : type24 A M => @lem8027654 A M N s)). Qed.
Lemma lem8027656 {A M : Type'} : (@all ((cart A M) -> Prop)) = (@all ((cart A M) -> Prop)).
Proof. exact (eq_refl (@all ((cart A M) -> Prop))). Qed.
Lemma lem8027657 {A M N : Type'} : (term40 A M N) = (term40 A M N).
Proof. exact (MK_COMB (@lem8027656 A M) (@lem8027655 A M N)). Qed.
Lemma lem8027658 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8027659 {A M N : Type'} : (term42 A M N) = (term42 A M N).
Proof. exact (MK_COMB (@lem8027658) (@lem8027657 A M N)). Qed.
Lemma lem8027660 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8027661 {A M N : Type'} : (term63 A M N) = (term63 A M N).
Proof. exact (MK_COMB (@lem8027660) (@lem8027659 A M N)). Qed.
Lemma lem8027662 {A M N : Type'} : (term64 A M N) = (term64 A M N).
Proof. exact (MK_COMB (@lem8027661 A M N) (@lem8027642 A M N)). Qed.
Lemma lem8027861 {A M N : Type'} : (term46 A M N) = (term64 A M N).
Proof. exact (TRANS (@lem8027463 A M N) (@lem8027662 A M N)). Qed.
Lemma lem8027862 {A M N : Type'} : (term64 A M N) = (term46 A M N).
Proof. exact (SYM (@lem8027861 A M N)). Qed.
Lemma lem8027863 {A M N : Type'} (h1 : term42 A M N) : term42 A M N.
Proof. exact (h1). Qed.
Lemma lem8027865 {A M N : Type'} (h1 : term31 A M N) : term31 A M N.
Proof. exact (h1). Qed.
Lemma lem8027879 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term93 A M N s t) = (term94 A M N s t).
Proof. exact (@lem17362 (term95 A M N s t) (term96 A M N s t)). Qed.
Lemma lem8027880 {A N : Type'} (P : type56 A N) : (term97 A N P) = (term98 A N P).
Proof. exact (@lem18392 (type24 A N) P). Qed.
Lemma lem8027881 {A M N : Type'} (s : type24 A M) : (term99 A M N s) = (term100 A M N s).
Proof. exact (@lem8027880 A N (term90 A M N s)). Qed.
Lemma lem8027882 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term101 A M N s t) = (term89 A M N s t).
Proof. exact (eq_refl (term101 A M N s t)). Qed.
Lemma lem8027883 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8027884 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term102 A M N s t) = (term93 A M N s t).
Proof. exact (MK_COMB (@lem8027883) (@lem8027882 A M N s t)). Qed.
Lemma lem8027885 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term102 A M N s t) = (term94 A M N s t).
Proof. exact (TRANS (@lem8027884 A M N s t) (@lem8027879 A M N s t)). Qed.
Lemma lem8027886 {A M N : Type'} (s : type24 A M) : (term103 A M N s) = (term104 A M N s).
Proof. exact (fun_ext (fun t : type24 A N => @lem8027885 A M N s t)). Qed.
Lemma lem8027887 {A N : Type'} : (@ex ((cart A N) -> Prop)) = (@ex ((cart A N) -> Prop)).
Proof. exact (eq_refl (@ex ((cart A N) -> Prop))). Qed.
Lemma lem8027888 {A M N : Type'} (s : type24 A M) : (term100 A M N s) = (term105 A M N s).
Proof. exact (MK_COMB (@lem8027887 A N) (@lem8027886 A M N s)). Qed.
Lemma lem8027889 {A M N : Type'} (s : type24 A M) : (term99 A M N s) = (term105 A M N s).
Proof. exact (TRANS (@lem8027881 A M N s) (@lem8027888 A M N s)). Qed.
Lemma lem8027890 {A M : Type'} (P : type56 A M) : (term97 A M P) = (term98 A M P).
Proof. exact (@lem18392 (type24 A M) P). Qed.
Lemma lem8027891 {A M N : Type'} : (term42 A M N) = (term106 A M N).
Proof. exact (@lem8027890 A M (term92 A M N)). Qed.
Lemma lem8027892 {A M N : Type'} (s : type24 A M) : (term107 A M N s) = (term91 A M N s).
Proof. exact (eq_refl (term107 A M N s)). Qed.
Lemma lem8027893 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8027894 {A M N : Type'} (s : type24 A M) : (term108 A M N s) = (term99 A M N s).
Proof. exact (MK_COMB (@lem8027893) (@lem8027892 A M N s)). Qed.
Lemma lem8027895 {A M N : Type'} (s : type24 A M) : (term108 A M N s) = (term105 A M N s).
Proof. exact (TRANS (@lem8027894 A M N s) (@lem8027889 A M N s)). Qed.
Lemma lem8027896 {A M N : Type'} : (term109 A M N) = (term110 A M N).
Proof. exact (fun_ext (fun s : type24 A M => @lem8027895 A M N s)). Qed.
Lemma lem8027897 {A M : Type'} : (@ex ((cart A M) -> Prop)) = (@ex ((cart A M) -> Prop)).
Proof. exact (eq_refl (@ex ((cart A M) -> Prop))). Qed.
Lemma lem8027898 {A M N : Type'} : (term106 A M N) = (term111 A M N).
Proof. exact (MK_COMB (@lem8027897 A M) (@lem8027896 A M N)). Qed.
Lemma lem8027955 {A M N : Type'} : (term42 A M N) = (term111 A M N).
Proof. exact (TRANS (@lem8027891 A M N) (@lem8027898 A M N)). Qed.
Lemma lem8027956 {A M N : Type'} (h1 : term42 A M N) : term111 A M N.
Proof. exact (EQ_MP (@lem8027955 A M N) (@lem8027863 A M N h1)). Qed.
Lemma lem8028069 {A M : Type'} (s : type24 A M) (m : nat) : (term112 A M s m) = (term113 A M s m).
Proof. exact (@lem17045 (@FINITE (cart A M) s) ((@CARD (cart A M) s) = m)). Qed.
Lemma lem8028076 {A N : Type'} (t : type24 A N) (n : nat) : (term112 A N t n) = (term113 A N t n).
Proof. exact (@lem17045 (@FINITE (cart A N) t) ((@CARD (cart A N) t) = n)). Qed.
Lemma lem8028077 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8028078 {A M : Type'} (s : type24 A M) (m : nat) : (term114 A M s m) = (term115 A M s m).
Proof. exact (MK_COMB (@lem8028077) (@lem8028069 A M s m)). Qed.
Lemma lem8028079 {A M N : Type'} (s : type24 A M) (m : nat) (t : type24 A N) (n : nat) : (term116 A M N s m t n) = (term117 A M N s m t n).
Proof. exact (MK_COMB (@lem8028078 A M s m) (@lem8028076 A N t n)). Qed.
Lemma lem8028080 {A M N : Type'} (s : type24 A M) (m : nat) (t : type24 A N) (n : nat) : (term118 A M N s m t n) = (term116 A M N s m t n).
Proof. exact (@lem17045 (term4 A M s m) (term4 A N t n)). Qed.
Lemma lem8028081 {A M N : Type'} (s : type24 A M) (m : nat) (t : type24 A N) (n : nat) : (term118 A M N s m t n) = (term117 A M N s m t n).
Proof. exact (TRANS (@lem8028080 A M N s m t n) (@lem8028079 A M N s m t n)). Qed.
Lemma lem8028086 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : (term13 A M N s t m n) = (term13 A M N s t m n).
Proof. exact (eq_refl (term13 A M N s t m n)). Qed.
Lemma lem8028087 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8028088 {A M N : Type'} (s : type24 A M) (m : nat) (t : type24 A N) (n : nat) : (term119 A M N s m t n) = (term120 A M N s m t n).
Proof. exact (MK_COMB (@lem8028087) (@lem8028081 A M N s m t n)). Qed.
Lemma lem8028089 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : (term121 A M N s t m n) = (term122 A M N s t m n).
Proof. exact (MK_COMB (@lem8028088 A M N s m t n) (@lem8028086 A M N s t m n)). Qed.
Lemma lem8028090 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : (term15 A M N s t m n) = (term121 A M N s t m n).
Proof. exact (@lem17265 (term8 A M N s m t n) (term13 A M N s t m n)). Qed.
Lemma lem8028091 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : (term15 A M N s t m n) = (term122 A M N s t m n).
Proof. exact (TRANS (@lem8028090 A M N s t m n) (@lem8028089 A M N s t m n)). Qed.
Lemma lem8028092 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) : (term17 A M N s t m) = (term123 A M N s t m).
Proof. exact (fun_ext (fun n : nat => @lem8028091 A M N s t m n)). Qed.
Lemma lem8028093 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8028094 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) : (term19 A M N s t m) = (term124 A M N s t m).
Proof. exact (MK_COMB (@lem8028093) (@lem8028092 A M N s t m)). Qed.
Lemma lem8028095 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term21 A M N s t) = (term125 A M N s t).
Proof. exact (fun_ext (fun m : nat => @lem8028094 A M N s t m)). Qed.
Lemma lem8028096 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8028097 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term23 A M N s t) = (term126 A M N s t).
Proof. exact (MK_COMB (@lem8028096) (@lem8028095 A M N s t)). Qed.
Lemma lem8028098 {A M N : Type'} (s : type24 A M) : (term25 A M N s) = (term127 A M N s).
Proof. exact (fun_ext (fun t : type24 A N => @lem8028097 A M N s t)). Qed.
Lemma lem8028099 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem8028100 {A M N : Type'} (s : type24 A M) : (term27 A M N s) = (term128 A M N s).
Proof. exact (MK_COMB (@lem8028099 A N) (@lem8028098 A M N s)). Qed.
Lemma lem8028101 {A M N : Type'} : (term29 A M N) = (term129 A M N).
Proof. exact (fun_ext (fun s : type24 A M => @lem8028100 A M N s)). Qed.
Lemma lem8028102 {A M : Type'} : (@all ((cart A M) -> Prop)) = (@all ((cart A M) -> Prop)).
Proof. exact (eq_refl (@all ((cart A M) -> Prop))). Qed.
Lemma lem8028167 {A M N : Type'} : (term31 A M N) = (term130 A M N).
Proof. exact (MK_COMB (@lem8028102 A M) (@lem8028101 A M N)). Qed.
Lemma lem8028168 {A M N : Type'} (h1 : term31 A M N) : term130 A M N.
Proof. exact (EQ_MP (@lem8028167 A M N) (@lem8027865 A M N h1)). Qed.
Lemma lem8028487 {A M N : Type'} (s : type24 A M) (h1 : term105 A M N s) : term105 A M N s.
Proof. exact (h1). Qed.
Lemma lem8028631 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : (term122 A M N s t m n) = (term122 A M N s t m n).
Proof. exact (eq_refl (term122 A M N s t m n)). Qed.
Lemma lem8028632 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) : (term123 A M N s t m) = (term123 A M N s t m).
Proof. exact (fun_ext (fun n : nat => @lem8028631 A M N s t m n)). Qed.
Lemma lem8028633 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8028634 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) : (term124 A M N s t m) = (term124 A M N s t m).
Proof. exact (MK_COMB (@lem8028633) (@lem8028632 A M N s t m)). Qed.
Lemma lem8028635 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term125 A M N s t) = (term125 A M N s t).
Proof. exact (fun_ext (fun m : nat => @lem8028634 A M N s t m)). Qed.
Lemma lem8028636 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8028637 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term126 A M N s t) = (term126 A M N s t).
Proof. exact (MK_COMB (@lem8028636) (@lem8028635 A M N s t)). Qed.
Lemma lem8028638 {A M N : Type'} (s : type24 A M) : (term127 A M N s) = (term127 A M N s).
Proof. exact (fun_ext (fun t : type24 A N => @lem8028637 A M N s t)). Qed.
Lemma lem8028639 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem8028640 {A M N : Type'} (s : type24 A M) : (term128 A M N s) = (term128 A M N s).
Proof. exact (MK_COMB (@lem8028639 A N) (@lem8028638 A M N s)). Qed.
Lemma lem8028641 {A M N : Type'} : (term129 A M N) = (term129 A M N).
Proof. exact (fun_ext (fun s : type24 A M => @lem8028640 A M N s)). Qed.
Lemma lem8028642 {A M : Type'} : (@all ((cart A M) -> Prop)) = (@all ((cart A M) -> Prop)).
Proof. exact (eq_refl (@all ((cart A M) -> Prop))). Qed.
Lemma lem8028643 {A M N : Type'} : (term130 A M N) = (term130 A M N).
Proof. exact (MK_COMB (@lem8028642 A M) (@lem8028641 A M N)). Qed.
Lemma lem8028644 {A M N : Type'} (h1 : term31 A M N) : term130 A M N.
Proof. exact (EQ_MP (@lem8028643 A M N) (@lem8028168 A M N h1)). Qed.
Lemma lem8028900 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term94 A M N s t) : term94 A M N s t.
Proof. exact (h1). Qed.
Lemma lem8028902 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term94 A M N s t) : term95 A M N s t.
Proof. exact (proj1 (@lem8028900 A M N s t h1)). Qed.
Lemma lem8028990 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : (term122 A M N s t m n) = (term131 A M N s t m n).
Proof. exact (@lem19490 (term96 A M N s t) (term117 A M N s m t n) ((term132 A M N s t) = (Nat.mul m n))). Qed.
Lemma lem8028991 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) : (term123 A M N s t m) = (term133 A M N s t m).
Proof. exact (fun_ext (fun n : nat => @lem8028990 A M N s t m n)). Qed.
Lemma lem8028992 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8028993 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) : (term124 A M N s t m) = (term134 A M N s t m).
Proof. exact (MK_COMB (@lem8028992) (@lem8028991 A M N s t m)). Qed.
Lemma lem8028994 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term125 A M N s t) = (term135 A M N s t).
Proof. exact (fun_ext (fun m : nat => @lem8028993 A M N s t m)). Qed.
Lemma lem8028995 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8028996 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term126 A M N s t) = (term136 A M N s t).
Proof. exact (MK_COMB (@lem8028995) (@lem8028994 A M N s t)). Qed.
Lemma lem8028997 {A M N : Type'} (s : type24 A M) : (term127 A M N s) = (term137 A M N s).
Proof. exact (fun_ext (fun t : type24 A N => @lem8028996 A M N s t)). Qed.
Lemma lem8028998 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem8028999 {A M N : Type'} (s : type24 A M) : (term128 A M N s) = (term138 A M N s).
Proof. exact (MK_COMB (@lem8028998 A N) (@lem8028997 A M N s)). Qed.
Lemma lem8029000 {A M N : Type'} : (term129 A M N) = (term139 A M N).
Proof. exact (fun_ext (fun s : type24 A M => @lem8028999 A M N s)). Qed.
Lemma lem8029001 {A M : Type'} : (@all ((cart A M) -> Prop)) = (@all ((cart A M) -> Prop)).
Proof. exact (eq_refl (@all ((cart A M) -> Prop))). Qed.
Lemma lem8029003 {A M N : Type'} : (term130 A M N) = (term140 A M N).
Proof. exact (MK_COMB (@lem8029001 A M) (@lem8029000 A M N)). Qed.
Lemma lem8029004 {A M N : Type'} (h1 : term31 A M N) : term140 A M N.
Proof. exact (EQ_MP (@lem8029003 A M N) (@lem8028644 A M N h1)). Qed.
Lemma lem8029179 {A M N : Type'} (_105969 : type24 A M) (h1 : term31 A M N) : term141 A M N _105969.
Proof. exact (@lem8029004 A M N h1 _105969). Qed.
Lemma lem8029180 {A M N : Type'} (_105969 : type24 A M) : (term141 A M N _105969) = (term138 A M N _105969).
Proof. exact (eq_refl (term141 A M N _105969)). Qed.
Lemma lem8029181 {A M N : Type'} (_105969 : type24 A M) (h1 : term31 A M N) : term138 A M N _105969.
Proof. exact (EQ_MP (@lem8029180 A M N _105969) (@lem8029179 A M N _105969 h1)). Qed.
Lemma lem8029182 {A M N : Type'} (_105969 : type24 A M) (_105970 : type24 A N) (h1 : term31 A M N) : term142 A M N _105969 _105970.
Proof. exact (@lem8029181 A M N _105969 h1 _105970). Qed.
Lemma lem8029183 {A M N : Type'} (_105969 : type24 A M) (_105970 : type24 A N) : (term142 A M N _105969 _105970) = (term136 A M N _105969 _105970).
Proof. exact (eq_refl (term142 A M N _105969 _105970)). Qed.
Lemma lem8029184 {A M N : Type'} (_105969 : type24 A M) (_105970 : type24 A N) (h1 : term31 A M N) : term136 A M N _105969 _105970.
Proof. exact (EQ_MP (@lem8029183 A M N _105969 _105970) (@lem8029182 A M N _105969 _105970 h1)). Qed.
Lemma lem8029185 {A M N : Type'} (_105969 : type24 A M) (_105970 : type24 A N) (_105971 : nat) (h1 : term31 A M N) : term143 A M N _105969 _105970 _105971.
Proof. exact (@lem8029184 A M N _105969 _105970 h1 _105971). Qed.
Lemma lem8029186 {A M N : Type'} (_105969 : type24 A M) (_105970 : type24 A N) (_105971 : nat) : (term143 A M N _105969 _105970 _105971) = (term134 A M N _105969 _105970 _105971).
Proof. exact (eq_refl (term143 A M N _105969 _105970 _105971)). Qed.
Lemma lem8029187 {A M N : Type'} (_105969 : type24 A M) (_105970 : type24 A N) (_105971 : nat) (h1 : term31 A M N) : term134 A M N _105969 _105970 _105971.
Proof. exact (EQ_MP (@lem8029186 A M N _105969 _105970 _105971) (@lem8029185 A M N _105969 _105970 _105971 h1)). Qed.
Lemma lem8029188 {A M N : Type'} (_105969 : type24 A M) (_105970 : type24 A N) (_105971 : nat) (_105972 : nat) (h1 : term31 A M N) : term144 A M N _105969 _105970 _105971 _105972.
Proof. exact (@lem8029187 A M N _105969 _105970 _105971 h1 _105972). Qed.
Lemma lem8029189 {A M N : Type'} (_105969 : type24 A M) (_105970 : type24 A N) (_105971 : nat) (_105972 : nat) : (term144 A M N _105969 _105970 _105971 _105972) = (term131 A M N _105969 _105970 _105971 _105972).
Proof. exact (eq_refl (term144 A M N _105969 _105970 _105971 _105972)). Qed.
Lemma lem8029190 {A M N : Type'} (_105969 : type24 A M) (_105970 : type24 A N) (_105971 : nat) (_105972 : nat) (h1 : term31 A M N) : term131 A M N _105969 _105970 _105971 _105972.
Proof. exact (EQ_MP (@lem8029189 A M N _105969 _105970 _105971 _105972) (@lem8029188 A M N _105969 _105970 _105971 _105972 h1)). Qed.
Lemma lem8029234 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) (h1 : term31 A M N) : term145 A M N _105971 _105972 _105969 _105970.
Proof. exact (proj1 (@lem8029190 A M N _105969 _105970 _105971 _105972 h1)). Qed.
Lemma lem8029238 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term94 A M N s t) : term146 A M N s t.
Proof. exact (proj2 (@lem8028900 A M N s t h1)). Qed.
Lemma lem8029390 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term145 A M N _105971 _105972 _105969 _105970) = (term147 A M N _105971 _105972 _105969 _105970).
Proof. exact (@lem8027255 (term113 A M _105969 _105971) (term113 A N _105970 _105972) (term96 A M N _105969 _105970)). Qed.
Lemma lem8029397 {A M N : Type'} (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term148 A M N _105972 _105969 _105970) = (term149 A M N _105972 _105969 _105970).
Proof. exact (@lem8027255 (term150 A N _105970) (term151 A N _105970 _105972) (term96 A M N _105969 _105970)). Qed.
Lemma lem8029398 {A M : Type'} (_105969 : type24 A M) (_105971 : nat) : (term115 A M _105969 _105971) = (term115 A M _105969 _105971).
Proof. exact (eq_refl (term115 A M _105969 _105971)). Qed.
Lemma lem8029399 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term147 A M N _105971 _105972 _105969 _105970) = (term152 A M N _105971 _105972 _105969 _105970).
Proof. exact (MK_COMB (@lem8029398 A M _105969 _105971) (@lem8029397 A M N _105972 _105969 _105970)). Qed.
Lemma lem8029406 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term152 A M N _105971 _105972 _105969 _105970) = (term153 A M N _105971 _105972 _105969 _105970).
Proof. exact (@lem8027255 (term150 A M _105969) (term151 A M _105969 _105971) (term149 A M N _105972 _105969 _105970)). Qed.
Lemma lem8029407 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term147 A M N _105971 _105972 _105969 _105970) = (term153 A M N _105971 _105972 _105969 _105970).
Proof. exact (TRANS (@lem8029399 A M N _105971 _105972 _105969 _105970) (@lem8029406 A M N _105971 _105972 _105969 _105970)). Qed.
Lemma lem8029409 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term145 A M N _105971 _105972 _105969 _105970) = (term153 A M N _105971 _105972 _105969 _105970).
Proof. exact (TRANS (@lem8029390 A M N _105971 _105972 _105969 _105970) (@lem8029407 A M N _105971 _105972 _105969 _105970)). Qed.
Lemma lem8029410 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) (h1 : term31 A M N) : term153 A M N _105971 _105972 _105969 _105970.
Proof. exact (EQ_MP (@lem8029409 A M N _105971 _105972 _105969 _105970) (@lem8029234 A M N _105971 _105972 _105969 _105970 h1)). Qed.
Lemma lem8029730 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term94 A M N s t) : @FINITE (cart A M) s.
Proof. exact (proj1 (@lem8028902 A M N s t h1)). Qed.
Lemma lem8029731 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term94 A M N s t) : term154 A M s.
Proof. exact (fun h0 : term150 A M s => @lem8029730 A M N s t h1). Qed.
Lemma lem8029733 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8029734 {A M : Type'} (s : type24 A M) : (term154 A M s) = (@FINITE (cart A M) s).
Proof. exact (@lem8029733 (@FINITE (cart A M) s)). Qed.
Lemma lem8029735 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term94 A M N s t) : @FINITE (cart A M) s.
Proof. exact (EQ_MP (@lem8029734 A M s) (@lem8029731 A M N s t h1)). Qed.
Lemma lem8029737 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem8029738 {A M : Type'} (s : type24 A M) : (@CARD (cart A M) s) = (@CARD (cart A M) s).
Proof. exact (@lem8029737 (@CARD (cart A M) s)). Qed.
Lemma lem8029739 {A M : Type'} (s : type24 A M) : term156 A M s.
Proof. exact (fun h0 : term157 A M s => @lem8029738 A M s). Qed.
Lemma lem8029741 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8029742 {A M : Type'} (s : type24 A M) : (term156 A M s) = ((@CARD (cart A M) s) = (@CARD (cart A M) s)).
Proof. exact (@lem8029741 ((@CARD (cart A M) s) = (@CARD (cart A M) s))). Qed.
Lemma lem8029743 {A M : Type'} (s : type24 A M) : (@CARD (cart A M) s) = (@CARD (cart A M) s).
Proof. exact (EQ_MP (@lem8029742 A M s) (@lem8029739 A M s)). Qed.
Lemma lem8029745 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term94 A M N s t) : @FINITE (cart A N) t.
Proof. exact (proj2 (@lem8028902 A M N s t h1)). Qed.
Lemma lem8029746 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term94 A M N s t) : term154 A N t.
Proof. exact (fun h0 : term150 A N t => @lem8029745 A M N s t h1). Qed.
Lemma lem8029748 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8029749 {A N : Type'} (t : type24 A N) : (term154 A N t) = (@FINITE (cart A N) t).
Proof. exact (@lem8029748 (@FINITE (cart A N) t)). Qed.
Lemma lem8029750 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term94 A M N s t) : @FINITE (cart A N) t.
Proof. exact (EQ_MP (@lem8029749 A N t) (@lem8029746 A M N s t h1)). Qed.
Lemma lem8029752 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem8029753 {A N : Type'} (t : type24 A N) : (@CARD (cart A N) t) = (@CARD (cart A N) t).
Proof. exact (@lem8029752 (@CARD (cart A N) t)). Qed.
Lemma lem8029754 {A N : Type'} (t : type24 A N) : term156 A N t.
Proof. exact (fun h0 : term157 A N t => @lem8029753 A N t). Qed.
Lemma lem8029756 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8029757 {A N : Type'} (t : type24 A N) : (term156 A N t) = ((@CARD (cart A N) t) = (@CARD (cart A N) t)).
Proof. exact (@lem8029756 ((@CARD (cart A N) t) = (@CARD (cart A N) t))). Qed.
Lemma lem8029758 {A N : Type'} (t : type24 A N) : (@CARD (cart A N) t) = (@CARD (cart A N) t).
Proof. exact (EQ_MP (@lem8029757 A N t) (@lem8029754 A N t)). Qed.
Lemma lem8029764 (q : Prop) (p : Prop) (r : Prop) : (term37 p q r) = (term37 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8029765 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term153 A M N _105971 _105972 _105969 _105970) = (term158 A M N _105971 _105972 _105969 _105970).
Proof. exact (@lem8029764 (term151 A M _105969 _105971) (term150 A M _105969) (term149 A M N _105972 _105969 _105970)). Qed.
Lemma lem8029791 (q : Prop) (p : Prop) (r : Prop) : (term37 p q r) = (term37 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8029792 {A M N : Type'} (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term149 A M N _105972 _105969 _105970) = (term159 A M N _105972 _105969 _105970).
Proof. exact (@lem8029791 (term151 A N _105970 _105972) (term150 A N _105970) (term96 A M N _105969 _105970)). Qed.
Lemma lem8029808 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8029809 {A M N : Type'} (_105969 : type24 A M) (_105970 : type24 A N) : (term160 A M N _105969 _105970) = (term161 A M N _105969 _105970).
Proof. exact (@lem8029808 (term96 A M N _105969 _105970) (term150 A N _105970)). Qed.
Lemma lem8029815 {A N : Type'} (_105970 : type24 A N) (_105972 : nat) : (term162 A N _105970 _105972) = (term162 A N _105970 _105972).
Proof. exact (eq_refl (term162 A N _105970 _105972)). Qed.
Lemma lem8029816 {A M N : Type'} (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term159 A M N _105972 _105969 _105970) = (term163 A M N _105972 _105969 _105970).
Proof. exact (MK_COMB (@lem8029815 A N _105970 _105972) (@lem8029809 A M N _105969 _105970)). Qed.
Lemma lem8029820 (q : Prop) (p : Prop) (r : Prop) : (term37 p q r) = (term37 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8029821 {A M N : Type'} (_105969 : type24 A M) (_105972 : nat) (_105970 : type24 A N) : (term163 A M N _105972 _105969 _105970) = (term164 A M N _105969 _105972 _105970).
Proof. exact (@lem8029820 (term96 A M N _105969 _105970) (term151 A N _105970 _105972) (term150 A N _105970)). Qed.
Lemma lem8029839 {A M N : Type'} (_105969 : type24 A M) (_105972 : nat) (_105970 : type24 A N) : (term159 A M N _105972 _105969 _105970) = (term164 A M N _105969 _105972 _105970).
Proof. exact (TRANS (@lem8029816 A M N _105972 _105969 _105970) (@lem8029821 A M N _105969 _105972 _105970)). Qed.
Lemma lem8029840 {A M N : Type'} (_105969 : type24 A M) (_105972 : nat) (_105970 : type24 A N) : (term149 A M N _105972 _105969 _105970) = (term164 A M N _105969 _105972 _105970).
Proof. exact (TRANS (@lem8029792 A M N _105972 _105969 _105970) (@lem8029839 A M N _105969 _105972 _105970)). Qed.
Lemma lem8029841 {A M : Type'} (_105969 : type24 A M) : (term165 A M _105969) = (term165 A M _105969).
Proof. exact (eq_refl (term165 A M _105969)). Qed.
Lemma lem8029842 {A M N : Type'} (_105969 : type24 A M) (_105972 : nat) (_105970 : type24 A N) : (term166 A M N _105972 _105969 _105970) = (term167 A M N _105969 _105972 _105970).
Proof. exact (MK_COMB (@lem8029841 A M _105969) (@lem8029840 A M N _105969 _105972 _105970)). Qed.
Lemma lem8029846 (q : Prop) (p : Prop) (r : Prop) : (term37 p q r) = (term37 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8029847 {A M N : Type'} (_105969 : type24 A M) (_105972 : nat) (_105970 : type24 A N) : (term167 A M N _105969 _105972 _105970) = (term168 A M N _105969 _105972 _105970).
Proof. exact (@lem8029846 (term96 A M N _105969 _105970) (term150 A M _105969) (term169 A N _105972 _105970)). Qed.
Lemma lem8029861 (q : Prop) (p : Prop) (r : Prop) : (term37 p q r) = (term37 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8029862 {A M N : Type'} (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term170 A M N _105969 _105972 _105970) = (term171 A M N _105972 _105969 _105970).
Proof. exact (@lem8029861 (term151 A N _105970 _105972) (term150 A M _105969) (term150 A N _105970)). Qed.
Lemma lem8029880 {A M N : Type'} (_105969 : type24 A M) (_105970 : type24 A N) : (term172 A M N _105969 _105970) = (term172 A M N _105969 _105970).
Proof. exact (eq_refl (term172 A M N _105969 _105970)). Qed.
Lemma lem8029881 {A M N : Type'} (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term168 A M N _105969 _105972 _105970) = (term173 A M N _105972 _105969 _105970).
Proof. exact (MK_COMB (@lem8029880 A M N _105969 _105970) (@lem8029862 A M N _105972 _105969 _105970)). Qed.
Lemma lem8029892 {A M N : Type'} (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term167 A M N _105969 _105972 _105970) = (term173 A M N _105972 _105969 _105970).
Proof. exact (TRANS (@lem8029847 A M N _105969 _105972 _105970) (@lem8029881 A M N _105972 _105969 _105970)). Qed.
Lemma lem8029893 {A M N : Type'} (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term166 A M N _105972 _105969 _105970) = (term173 A M N _105972 _105969 _105970).
Proof. exact (TRANS (@lem8029842 A M N _105969 _105972 _105970) (@lem8029892 A M N _105972 _105969 _105970)). Qed.
Lemma lem8029894 {A M : Type'} (_105969 : type24 A M) (_105971 : nat) : (term162 A M _105969 _105971) = (term162 A M _105969 _105971).
Proof. exact (eq_refl (term162 A M _105969 _105971)). Qed.
Lemma lem8029895 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term158 A M N _105971 _105972 _105969 _105970) = (term174 A M N _105971 _105972 _105969 _105970).
Proof. exact (MK_COMB (@lem8029894 A M _105969 _105971) (@lem8029893 A M N _105972 _105969 _105970)). Qed.
Lemma lem8029899 (q : Prop) (p : Prop) (r : Prop) : (term37 p q r) = (term37 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8029900 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term174 A M N _105971 _105972 _105969 _105970) = (term175 A M N _105971 _105972 _105969 _105970).
Proof. exact (@lem8029899 (term96 A M N _105969 _105970) (term151 A M _105969 _105971) (term171 A M N _105972 _105969 _105970)). Qed.
Lemma lem8029940 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term158 A M N _105971 _105972 _105969 _105970) = (term175 A M N _105971 _105972 _105969 _105970).
Proof. exact (TRANS (@lem8029895 A M N _105971 _105972 _105969 _105970) (@lem8029900 A M N _105971 _105972 _105969 _105970)). Qed.
Lemma lem8029941 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term153 A M N _105971 _105972 _105969 _105970) = (term175 A M N _105971 _105972 _105969 _105970).
Proof. exact (TRANS (@lem8029765 A M N _105971 _105972 _105969 _105970) (@lem8029940 A M N _105971 _105972 _105969 _105970)). Qed.
Lemma lem8029942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8029943 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term176 A M N _105971 _105972 _105969 _105970) = (term177 A M N _105971 _105972 _105969 _105970).
Proof. exact (MK_COMB (@lem8029942) (@lem8029941 A M N _105971 _105972 _105969 _105970)). Qed.
Lemma lem8029957 (q : Prop) (p : Prop) (r : Prop) : (term37 p q r) = (term37 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8029958 {A M N : Type'} (_105971 : nat) (_105969 : type24 A M) (_105970 : type24 A N) (_105972 : nat) : (term178 A M N _105969 _105971 _105970 _105972) = (term179 A M N _105971 _105969 _105970 _105972).
Proof. exact (@lem8029957 (term151 A M _105969 _105971) (term150 A M _105969) (term113 A N _105970 _105972)). Qed.
Lemma lem8029984 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8029985 {A N : Type'} (_105972 : nat) (_105970 : type24 A N) : (term113 A N _105970 _105972) = (term169 A N _105972 _105970).
Proof. exact (@lem8029984 (term151 A N _105970 _105972) (term150 A N _105970)). Qed.
Lemma lem8029993 {A M : Type'} (_105969 : type24 A M) : (term165 A M _105969) = (term165 A M _105969).
Proof. exact (eq_refl (term165 A M _105969)). Qed.
Lemma lem8029994 {A M N : Type'} (_105969 : type24 A M) (_105972 : nat) (_105970 : type24 A N) : (term180 A M N _105969 _105970 _105972) = (term170 A M N _105969 _105972 _105970).
Proof. exact (MK_COMB (@lem8029993 A M _105969) (@lem8029985 A N _105972 _105970)). Qed.
Lemma lem8029998 (q : Prop) (p : Prop) (r : Prop) : (term37 p q r) = (term37 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8029999 {A M N : Type'} (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term170 A M N _105969 _105972 _105970) = (term171 A M N _105972 _105969 _105970).
Proof. exact (@lem8029998 (term151 A N _105970 _105972) (term150 A M _105969) (term150 A N _105970)). Qed.
Lemma lem8030017 {A M N : Type'} (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term180 A M N _105969 _105970 _105972) = (term171 A M N _105972 _105969 _105970).
Proof. exact (TRANS (@lem8029994 A M N _105969 _105972 _105970) (@lem8029999 A M N _105972 _105969 _105970)). Qed.
Lemma lem8030018 {A M : Type'} (_105969 : type24 A M) (_105971 : nat) : (term162 A M _105969 _105971) = (term162 A M _105969 _105971).
Proof. exact (eq_refl (term162 A M _105969 _105971)). Qed.
Lemma lem8030019 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term179 A M N _105971 _105969 _105970 _105972) = (term181 A M N _105971 _105972 _105969 _105970).
Proof. exact (MK_COMB (@lem8030018 A M _105969 _105971) (@lem8030017 A M N _105972 _105969 _105970)). Qed.
Lemma lem8030030 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term178 A M N _105969 _105971 _105970 _105972) = (term181 A M N _105971 _105972 _105969 _105970).
Proof. exact (TRANS (@lem8029958 A M N _105971 _105969 _105970 _105972) (@lem8030019 A M N _105971 _105972 _105969 _105970)). Qed.
Lemma lem8030031 {A M N : Type'} (_105969 : type24 A M) (_105970 : type24 A N) : (term172 A M N _105969 _105970) = (term172 A M N _105969 _105970).
Proof. exact (eq_refl (term172 A M N _105969 _105970)). Qed.
Lemma lem8030032 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term182 A M N _105969 _105971 _105970 _105972) = (term175 A M N _105971 _105972 _105969 _105970).
Proof. exact (MK_COMB (@lem8030031 A M N _105969 _105970) (@lem8030030 A M N _105971 _105972 _105969 _105970)). Qed.
Lemma lem8030043 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : ((term153 A M N _105971 _105972 _105969 _105970) = (term182 A M N _105969 _105971 _105970 _105972)) = ((term175 A M N _105971 _105972 _105969 _105970) = (term175 A M N _105971 _105972 _105969 _105970)).
Proof. exact (MK_COMB (@lem8029943 A M N _105971 _105972 _105969 _105970) (@lem8030032 A M N _105971 _105972 _105969 _105970)). Qed.
Lemma lem8030045 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8030046 (x : Prop) : (x = x) = True.
Proof. exact (@lem8030045 Prop x). Qed.
Lemma lem8030047 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : ((term175 A M N _105971 _105972 _105969 _105970) = (term175 A M N _105971 _105972 _105969 _105970)) = True.
Proof. exact (@lem8030046 (term175 A M N _105971 _105972 _105969 _105970)). Qed.
Lemma lem8030048 {A M N : Type'} (_105969 : type24 A M) (_105971 : nat) (_105970 : type24 A N) (_105972 : nat) : ((term153 A M N _105971 _105972 _105969 _105970) = (term182 A M N _105969 _105971 _105970 _105972)) = True.
Proof. exact (TRANS (@lem8030043 A M N _105971 _105972 _105969 _105970) (@lem8030047 A M N _105971 _105972 _105969 _105970)). Qed.
Lemma lem8030049 {A M N : Type'} (_105969 : type24 A M) (_105971 : nat) (_105970 : type24 A N) (_105972 : nat) : True = ((term153 A M N _105971 _105972 _105969 _105970) = (term182 A M N _105969 _105971 _105970 _105972)).
Proof. exact (SYM (@lem8030048 A M N _105969 _105971 _105970 _105972)). Qed.
Lemma lem8030050 {A M N : Type'} (_105969 : type24 A M) (_105971 : nat) (_105970 : type24 A N) (_105972 : nat) : (term153 A M N _105971 _105972 _105969 _105970) = (term182 A M N _105969 _105971 _105970 _105972).
Proof. exact (EQ_MP (@lem8030049 A M N _105969 _105971 _105970 _105972) (@lem0)). Qed.
Lemma lem8030051 {A M N : Type'} (_105969 : type24 A M) (_105971 : nat) (_105970 : type24 A N) (_105972 : nat) (h1 : term31 A M N) : term182 A M N _105969 _105971 _105970 _105972.
Proof. exact (EQ_MP (@lem8030050 A M N _105969 _105971 _105970 _105972) (@lem8029410 A M N _105971 _105972 _105969 _105970 h1)). Qed.
Lemma lem8030053 (b : Prop) (a : Prop) : (a \/ b) = (term183 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8030054 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term182 A M N _105969 _105971 _105970 _105972) = (term184 A M N _105971 _105972 _105969 _105970).
Proof. exact (@lem8030053 (term178 A M N _105969 _105971 _105970 _105972) (term96 A M N _105969 _105970)). Qed.
Lemma lem8030056 (a : Prop) (b : Prop) : (term185 a b) = (term186 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8030057 {A M N : Type'} (_105969 : type24 A M) (_105971 : nat) (_105970 : type24 A N) (_105972 : nat) : (term187 A M N _105969 _105971 _105970 _105972) = (term188 A M N _105969 _105971 _105970 _105972).
Proof. exact (@lem8030056 (term150 A M _105969) (term189 A M N _105969 _105971 _105970 _105972)). Qed.
Lemma lem8030059 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8030060 {A M : Type'} (_105969 : type24 A M) : (term191 A M _105969) = (@FINITE (cart A M) _105969).
Proof. exact (@lem8030059 (@FINITE (cart A M) _105969)). Qed.
Lemma lem8030061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8030062 {A M : Type'} (_105969 : type24 A M) : (term192 A M _105969) = (term193 A M _105969).
Proof. exact (MK_COMB (@lem8030061) (@lem8030060 A M _105969)). Qed.
Lemma lem8030064 (a : Prop) (b : Prop) : (term185 a b) = (term186 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8030065 {A M N : Type'} (_105969 : type24 A M) (_105971 : nat) (_105970 : type24 A N) (_105972 : nat) : (term194 A M N _105969 _105971 _105970 _105972) = (term195 A M N _105969 _105971 _105970 _105972).
Proof. exact (@lem8030064 (term151 A M _105969 _105971) (term113 A N _105970 _105972)). Qed.
Lemma lem8030067 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8030068 {A M : Type'} (_105969 : type24 A M) (_105971 : nat) : (term196 A M _105969 _105971) = ((@CARD (cart A M) _105969) = _105971).
Proof. exact (@lem8030067 ((@CARD (cart A M) _105969) = _105971)). Qed.
Lemma lem8030069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8030070 {A M : Type'} (_105969 : type24 A M) (_105971 : nat) : (term197 A M _105969 _105971) = (term198 A M _105969 _105971).
Proof. exact (MK_COMB (@lem8030069) (@lem8030068 A M _105969 _105971)). Qed.
Lemma lem8030072 (a : Prop) (b : Prop) : (term185 a b) = (term186 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8030073 {A N : Type'} (_105970 : type24 A N) (_105972 : nat) : (term199 A N _105970 _105972) = (term200 A N _105970 _105972).
Proof. exact (@lem8030072 (term150 A N _105970) (term151 A N _105970 _105972)). Qed.
Lemma lem8030075 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8030076 {A N : Type'} (_105970 : type24 A N) : (term191 A N _105970) = (@FINITE (cart A N) _105970).
Proof. exact (@lem8030075 (@FINITE (cart A N) _105970)). Qed.
Lemma lem8030077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8030078 {A N : Type'} (_105970 : type24 A N) : (term192 A N _105970) = (term193 A N _105970).
Proof. exact (MK_COMB (@lem8030077) (@lem8030076 A N _105970)). Qed.
Lemma lem8030080 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8030081 {A N : Type'} (_105970 : type24 A N) (_105972 : nat) : (term196 A N _105970 _105972) = ((@CARD (cart A N) _105970) = _105972).
Proof. exact (@lem8030080 ((@CARD (cart A N) _105970) = _105972)). Qed.
Lemma lem8030082 {A N : Type'} (_105970 : type24 A N) (_105972 : nat) : (term200 A N _105970 _105972) = (term4 A N _105970 _105972).
Proof. exact (MK_COMB (@lem8030078 A N _105970) (@lem8030081 A N _105970 _105972)). Qed.
Lemma lem8030083 {A N : Type'} (_105970 : type24 A N) (_105972 : nat) : (term199 A N _105970 _105972) = (term4 A N _105970 _105972).
Proof. exact (TRANS (@lem8030073 A N _105970 _105972) (@lem8030082 A N _105970 _105972)). Qed.
Lemma lem8030084 {A M N : Type'} (_105969 : type24 A M) (_105971 : nat) (_105970 : type24 A N) (_105972 : nat) : (term195 A M N _105969 _105971 _105970 _105972) = (term201 A M N _105969 _105971 _105970 _105972).
Proof. exact (MK_COMB (@lem8030070 A M _105969 _105971) (@lem8030083 A N _105970 _105972)). Qed.
Lemma lem8030085 {A M N : Type'} (_105969 : type24 A M) (_105971 : nat) (_105970 : type24 A N) (_105972 : nat) : (term194 A M N _105969 _105971 _105970 _105972) = (term201 A M N _105969 _105971 _105970 _105972).
Proof. exact (TRANS (@lem8030065 A M N _105969 _105971 _105970 _105972) (@lem8030084 A M N _105969 _105971 _105970 _105972)). Qed.
Lemma lem8030086 {A M N : Type'} (_105969 : type24 A M) (_105971 : nat) (_105970 : type24 A N) (_105972 : nat) : (term188 A M N _105969 _105971 _105970 _105972) = (term202 A M N _105969 _105971 _105970 _105972).
Proof. exact (MK_COMB (@lem8030062 A M _105969) (@lem8030085 A M N _105969 _105971 _105970 _105972)). Qed.
Lemma lem8030087 {A M N : Type'} (_105969 : type24 A M) (_105971 : nat) (_105970 : type24 A N) (_105972 : nat) : (term187 A M N _105969 _105971 _105970 _105972) = (term202 A M N _105969 _105971 _105970 _105972).
Proof. exact (TRANS (@lem8030057 A M N _105969 _105971 _105970 _105972) (@lem8030086 A M N _105969 _105971 _105970 _105972)). Qed.
Lemma lem8030088 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8030089 {A M N : Type'} (_105969 : type24 A M) (_105971 : nat) (_105970 : type24 A N) (_105972 : nat) : (term203 A M N _105969 _105971 _105970 _105972) = (term204 A M N _105969 _105971 _105970 _105972).
Proof. exact (MK_COMB (@lem8030088) (@lem8030087 A M N _105969 _105971 _105970 _105972)). Qed.
Lemma lem8030090 {A M N : Type'} (_105969 : type24 A M) (_105970 : type24 A N) : (term96 A M N _105969 _105970) = (term96 A M N _105969 _105970).
Proof. exact (eq_refl (term96 A M N _105969 _105970)). Qed.
Lemma lem8030091 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term184 A M N _105971 _105972 _105969 _105970) = (term205 A M N _105971 _105972 _105969 _105970).
Proof. exact (MK_COMB (@lem8030089 A M N _105969 _105971 _105970 _105972) (@lem8030090 A M N _105969 _105970)). Qed.
Lemma lem8030092 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) : (term182 A M N _105969 _105971 _105970 _105972) = (term205 A M N _105971 _105972 _105969 _105970).
Proof. exact (TRANS (@lem8030054 A M N _105971 _105972 _105969 _105970) (@lem8030091 A M N _105971 _105972 _105969 _105970)). Qed.
Lemma lem8030094 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term94 A M N s t) : term206 A N t.
Proof. exact (conj (@lem8029750 A M N s t h1) (@lem8029758 A N t)). Qed.
Lemma lem8030095 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term94 A M N s t) : term207 A M N s t.
Proof. exact (conj (@lem8029743 A M s) (@lem8030094 A M N s t h1)). Qed.
Lemma lem8030096 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term94 A M N s t) : term208 A M N s t.
Proof. exact (conj (@lem8029735 A M N s t h1) (@lem8030095 A M N s t h1)). Qed.
Lemma lem8030098 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) (h1 : term31 A M N) : term205 A M N _105971 _105972 _105969 _105970.
Proof. exact (EQ_MP (@lem8030092 A M N _105971 _105972 _105969 _105970) (@lem8030051 A M N _105969 _105971 _105970 _105972 h1)). Qed.
Lemma lem8030099 {A M N : Type'} (_105971 : nat) (_105972 : nat) (_105969 : type24 A M) (_105970 : type24 A N) (h1 : term31 A M N) : term205 A M N _105971 _105972 _105969 _105970.
Proof. exact (@lem8030098 A M N _105971 _105972 _105969 _105970 h1). Qed.
Lemma lem8030100 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term31 A M N) : term209 A M N s t.
Proof. exact (@lem8030099 A M N (@CARD (cart A M) s) (@CARD (cart A N) t) s t h1). Qed.
Lemma lem8030103 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term31 A M N) (h2 : term94 A M N s t) : term96 A M N s t.
Proof. exact (@lem8030100 A M N s t h1 (@lem8030096 A M N s t h2)). Qed.
Lemma lem8030104 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term31 A M N) (h2 : term94 A M N s t) : term210 A M N s t.
Proof. exact (fun h0 : term146 A M N s t => @lem8030103 A M N s t h1 h2). Qed.
Lemma lem8030106 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8030107 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term210 A M N s t) = (term96 A M N s t).
Proof. exact (@lem8030106 (term96 A M N s t)). Qed.
Lemma lem8030108 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term31 A M N) (h2 : term94 A M N s t) : term96 A M N s t.
Proof. exact (EQ_MP (@lem8030107 A M N s t) (@lem8030104 A M N s t h1 h2)). Qed.
Lemma lem8030111 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8030113 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term146 A M N s t) = (term211 A M N s t).
Proof. exact (@lem8030111 (term96 A M N s t)). Qed.
Lemma lem8030116 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term94 A M N s t) : term211 A M N s t.
Proof. exact (EQ_MP (@lem8030113 A M N s t) (@lem8029238 A M N s t h1)). Qed.
Lemma lem8030119 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term31 A M N) (h2 : term94 A M N s t) : False.
Proof. exact (@lem8030116 A M N s t h2 (@lem8030108 A M N s t h1 h2)). Qed.
Lemma lem8030120 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term31 A M N) (h2 : term94 A M N s t) : term212.
Proof. exact (fun h0 : ~ False => @lem8030119 A M N s t h1 h2). Qed.
Lemma lem8030122 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8030123 : term212 = False.
Proof. exact (@lem8030122 False). Qed.
Lemma lem8030124 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term31 A M N) (h2 : term94 A M N s t) : False.
Proof. exact (EQ_MP (@lem8030123) (@lem8030120 A M N s t h1 h2)). Qed.
Lemma lem8030125 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term31 A M N) (h2 : term94 A M N s t) : (term94 A M N s t) = False.
Proof. exact (prop_ext (fun h3 : term94 A M N s t => @lem8030124 A M N s t h1 h2) (fun h3 : False => @lem8028900 A M N s t h2)). Qed.
Lemma lem8030126 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term31 A M N) (h2 : term94 A M N s t) : False.
Proof. exact (EQ_MP (@lem8030125 A M N s t h1 h2) (@lem8028900 A M N s t h2)). Qed.
Lemma lem8030127 {A M N : Type'} (s : type24 A M) (h1 : term31 A M N) (h2 : term105 A M N s) : False.
Proof. exact (ex_elim (@lem8028487 A M N s h2) (fun t : type24 A N => fun h0 : term104 A M N s t => @lem8030126 A M N s t h1 h0)). Qed.
Lemma lem8030128 {A M N : Type'} (h1 : term31 A M N) (h2 : term42 A M N) : False.
Proof. exact (ex_elim (@lem8027956 A M N h2) (fun s : type24 A M => fun h0 : term110 A M N s => @lem8030127 A M N s h1 h0)). Qed.
Lemma lem8030129 {A M N : Type'} (h1 : term31 A M N) (h2 : term42 A M N) : term50 A M N.
Proof. exact (fun h0 : term44 A M N => @lem8030128 A M N h1 h2). Qed.
Lemma lem8030130 {A M N : Type'} : (term50 A M N) = (term51 A M N).
Proof. exact (@lem69 (term44 A M N)). Qed.
Lemma lem8030131 {A M N : Type'} (h1 : term31 A M N) (h2 : term42 A M N) : term51 A M N.
Proof. exact (EQ_MP (@lem8030130 A M N) (@lem8030129 A M N h1 h2)). Qed.
Lemma lem8030132 {A M N : Type'} (h1 : term31 A M N) (h2 : term42 A M N) : term54 A M N.
Proof. exact (fun h0 : term43 A N => @lem8030131 A M N h1 h2). Qed.
Lemma lem8030133 {A M N : Type'} (h1 : term31 A M N) (h2 : term42 A M N) : term57 A M N.
Proof. exact (fun h0 : term45 A M N => @lem8030132 A M N h1 h2). Qed.
Lemma lem8030134 {A M N : Type'} (h1 : term42 A M N) : term60 A M N.
Proof. exact (fun h0 : term31 A M N => @lem8030133 A M N h0 h1). Qed.
Lemma lem8030135 {A M N : Type'} (h1 : term42 A M N) : term62 A M N.
Proof. exact (fun h0 : term43 A M => @lem8030134 A M N h1). Qed.
Lemma lem8030136 {A M N : Type'} : term64 A M N.
Proof. exact (fun h0 : term42 A M N => @lem8030135 A M N h0). Qed.
Lemma lem8030137 {A M N : Type'} : term46 A M N.
Proof. exact (EQ_MP (@lem8027862 A M N) (@lem8030136 A M N)). Qed.
Lemma lem8030139 {A M N : Type'} : term46 A M N.
Proof. exact (@lem8027284 A M N (@lem8030137 A M N)). Qed.
Lemma lem8030140 {A M N : Type'} (h1 : term42 A M N) : term61 A M N.
Proof. exact (@lem8030139 A M N (@lem8027260 A M N h1)). Qed.
Lemma lem8030141 {A M N : Type'} (h1 : term42 A M N) : term59 A M N.
Proof. exact (@lem8030140 A M N h1 (@lem8027264 A M)). Qed.
Lemma lem8030142 {A M N : Type'} (h1 : term42 A M N) : term56 A M N.
Proof. exact (@lem8030141 A M N h1 (@lem8027261 A M N)). Qed.
Lemma lem8030143 {A M N : Type'} (h1 : term42 A M N) : term53 A M N.
Proof. exact (@lem8030142 A M N h1 (@lem8027266 A M N)). Qed.
Lemma lem8030144 {A M N : Type'} (h1 : term42 A M N) : term50 A M N.
Proof. exact (@lem8030143 A M N h1 (@lem8027262 A N)). Qed.
Lemma lem8030145 {A M N : Type'} (h1 : term42 A M N) : False.
Proof. exact (@lem8030144 A M N h1 (@lem8027263 A M N)). Qed.
Lemma lem8030146 {A M N : Type'} (h1 : term42 A M N) : (term42 A M N) = False.
Proof. exact (prop_ext (fun h2 : term42 A M N => @lem8030145 A M N h1) (fun h2 : False => @lem8027260 A M N h1)). Qed.
Lemma lem8030147 {A M N : Type'} (h1 : term42 A M N) : False.
Proof. exact (EQ_MP (@lem8030146 A M N h1) (@lem8027260 A M N h1)). Qed.
Lemma lem8030148 {A M N : Type'} : term41 A M N.
Proof. exact (fun h0 : term42 A M N => @lem8030147 A M N h0). Qed.
Lemma lem8030149 {A M N : Type'} : term40 A M N.
Proof. exact (EQ_MP (@lem8027259 A M N) (@lem8030148 A M N)). Qed.
