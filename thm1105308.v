Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1105308_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1105192 {_25569 : Type'} (EL' : type1587 _25569) (h1 : (term0 _25569 EL') = (term1 _25569)) : (term0 _25569 EL') = (term1 _25569).
Proof. exact (h1). Qed.
Lemma lem1105193 {_25569 : Type'} (l : list _25569) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1105194 {_25569 : Type'} (l : list _25569) (EL' : type1587 _25569) (h1 : (term0 _25569 EL') = (term1 _25569)) : (term2 _25569 EL' l) = (term3 _25569 l).
Proof. exact (MK_COMB (@lem1105192 _25569 EL' h1) (@lem1105193 _25569 l)). Qed.
Lemma lem1105195 {_25569 : Type'} (l : list _25569) : (term3 _25569 l) = (@hd _25569 l).
Proof. exact (eq_refl (term3 _25569 l)). Qed.
Lemma lem1105196 {_25569 : Type'} (EL' : type1587 _25569) (l : list _25569) : (term4 _25569 EL' l) = (term4 _25569 EL' l).
Proof. exact (eq_refl (term4 _25569 EL' l)). Qed.
Lemma lem1105197 {_25569 : Type'} (EL' : type1587 _25569) (l : list _25569) : ((term2 _25569 EL' l) = (term3 _25569 l)) = ((term2 _25569 EL' l) = (@hd _25569 l)).
Proof. exact (MK_COMB (@lem1105196 _25569 EL' l) (@lem1105195 _25569 l)). Qed.
Lemma lem1105198 {_25569 : Type'} (l : list _25569) (EL' : type1587 _25569) (h1 : (term0 _25569 EL') = (term1 _25569)) : (term2 _25569 EL' l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105197 _25569 EL' l) (@lem1105194 _25569 l EL' h1)). Qed.
Lemma lem1105199 {_25569 : Type'} (EL' : type1587 _25569) (h1 : (term0 _25569 EL') = (term1 _25569)) : term5 _25569 EL'.
Proof. exact (fun l : list _25569 => @lem1105198 _25569 l EL' h1). Qed.
Lemma lem1105200 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term6 _25569 EL') : term6 _25569 EL'.
Proof. exact (h1). Qed.
Lemma lem1105201 {_25569 : Type'} (n : nat) (EL' : type1587 _25569) (h1 : term6 _25569 EL') : term7 _25569 EL' n.
Proof. exact (@lem1105200 _25569 EL' h1 n). Qed.
Lemma lem1105202 {_25569 : Type'} (EL' : type1587 _25569) (n : nat) : (term7 _25569 EL' n) = ((term8 _25569 EL' n) = (term9 _25569 EL' n)).
Proof. exact (eq_refl (term7 _25569 EL' n)). Qed.
Lemma lem1105203 {_25569 : Type'} (n : nat) (EL' : type1587 _25569) (h1 : term6 _25569 EL') : (term8 _25569 EL' n) = (term9 _25569 EL' n).
Proof. exact (EQ_MP (@lem1105202 _25569 EL' n) (@lem1105201 _25569 n EL' h1)). Qed.
Lemma lem1105204 {_25569 : Type'} (l : list _25569) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1105205 {_25569 : Type'} (n : nat) (l : list _25569) (EL' : type1587 _25569) (h1 : term6 _25569 EL') : (term10 _25569 EL' n l) = (term11 _25569 EL' n l).
Proof. exact (MK_COMB (@lem1105203 _25569 n EL' h1) (@lem1105204 _25569 l)). Qed.
Lemma lem1105206 {_25569 : Type'} (EL' : type1587 _25569) (n : nat) (l : list _25569) : (term11 _25569 EL' n l) = (term12 _25569 EL' n l).
Proof. exact (eq_refl (term11 _25569 EL' n l)). Qed.
Lemma lem1105207 {_25569 : Type'} (EL' : type1587 _25569) (n : nat) (l : list _25569) : (term13 _25569 EL' n l) = (term13 _25569 EL' n l).
Proof. exact (eq_refl (term13 _25569 EL' n l)). Qed.
Lemma lem1105208 {_25569 : Type'} (EL' : type1587 _25569) (n : nat) (l : list _25569) : ((term10 _25569 EL' n l) = (term11 _25569 EL' n l)) = ((term10 _25569 EL' n l) = (term12 _25569 EL' n l)).
Proof. exact (MK_COMB (@lem1105207 _25569 EL' n l) (@lem1105206 _25569 EL' n l)). Qed.
Lemma lem1105209 {_25569 : Type'} (n : nat) (l : list _25569) (EL' : type1587 _25569) (h1 : term6 _25569 EL') : (term10 _25569 EL' n l) = (term12 _25569 EL' n l).
Proof. exact (EQ_MP (@lem1105208 _25569 EL' n l) (@lem1105205 _25569 n l EL' h1)). Qed.
Lemma lem1105210 {_25569 : Type'} (n : nat) (EL' : type1587 _25569) (h1 : term6 _25569 EL') : term14 _25569 EL' n.
Proof. exact (fun l : list _25569 => @lem1105209 _25569 n l EL' h1). Qed.
Lemma lem1105211 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term6 _25569 EL') : term15 _25569 EL'.
Proof. exact (fun n : nat => @lem1105210 _25569 n EL' h1). Qed.
Lemma lem1105212 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term16 _25569 EL') : term16 _25569 EL'.
Proof. exact (h1). Qed.
Lemma lem1105213 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term16 _25569 EL') : term6 _25569 EL'.
Proof. exact (proj2 (@lem1105212 _25569 EL' h1)). Qed.
Lemma lem1105214 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term16 _25569 EL') : (term0 _25569 EL') = (term1 _25569).
Proof. exact (proj1 (@lem1105212 _25569 EL' h1)). Qed.
Lemma lem1105215 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term16 _25569 EL') : ((term0 _25569 EL') = (term1 _25569)) = (term5 _25569 EL').
Proof. exact (prop_ext (fun h2 : (term0 _25569 EL') = (term1 _25569) => @lem1105199 _25569 EL' h2) (fun h2 : term5 _25569 EL' => @lem1105214 _25569 EL' h1)). Qed.
Lemma lem1105216 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term16 _25569 EL') : term5 _25569 EL'.
Proof. exact (EQ_MP (@lem1105215 _25569 EL' h1) (@lem1105214 _25569 EL' h1)). Qed.
Lemma lem1105217 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term16 _25569 EL') : (term6 _25569 EL') = (term15 _25569 EL').
Proof. exact (prop_ext (fun h2 : term6 _25569 EL' => @lem1105211 _25569 EL' h2) (fun h2 : term15 _25569 EL' => @lem1105213 _25569 EL' h1)). Qed.
Lemma lem1105218 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term16 _25569 EL') : term15 _25569 EL'.
Proof. exact (EQ_MP (@lem1105217 _25569 EL' h1) (@lem1105213 _25569 EL' h1)). Qed.
Lemma lem1105219 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term16 _25569 EL') : term17 _25569 EL'.
Proof. exact (conj (@lem1105216 _25569 EL' h1) (@lem1105218 _25569 EL' h1)). Qed.
Lemma lem1105220 {A : Type'} (e : A) : term18 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem1105221 {A : Type'} (e : A) : (term18 A e) = (term19 A e).
Proof. exact (eq_refl (term18 A e)). Qed.
Lemma lem1105222 {A : Type'} (e : A) : term19 A e.
Proof. exact (EQ_MP (@lem1105221 A e) (@lem1105220 A e)). Qed.
Lemma lem1105223 {A : Type'} (e : A) (f : type1423 A) : term20 A e f.
Proof. exact (@lem1105222 A e f). Qed.
Lemma lem1105224 {A : Type'} (e : A) (f : type1423 A) : (term20 A e f) = (term21 A e f).
Proof. exact (eq_refl (term20 A e f)). Qed.
Lemma lem1105225 {A : Type'} (e : A) (f : type1423 A) : term21 A e f.
Proof. exact (EQ_MP (@lem1105224 A e f) (@lem1105223 A e f)). Qed.
Lemma lem1105226 {_25569 : Type'} (e : type1141 _25569) (f : type276 _25569) : term22 _25569 e f.
Proof. exact (@lem1105225 (type1141 _25569) e f). Qed.
Lemma lem1105227 {_25569 : Type'} : term23 _25569.
Proof. exact (@lem1105226 _25569 (term1 _25569) (term24 _25569)). Qed.
Lemma lem1105228 {_25569 : Type'} (fn : type1587 _25569) (n : nat) : (term25 _25569 fn n) = (term26 _25569 fn n).
Proof. exact (eq_refl (term25 _25569 fn n)). Qed.
Lemma lem1105229 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1105230 {_25569 : Type'} (fn : type1587 _25569) (n : nat) : (term27 _25569 fn n) = (term28 _25569 fn n).
Proof. exact (MK_COMB (@lem1105228 _25569 fn n) (@lem1105229 n)). Qed.
Lemma lem1105231 {_25569 : Type'} (fn : type1587 _25569) (n : nat) : (term28 _25569 fn n) = (term9 _25569 fn n).
Proof. exact (eq_refl (term28 _25569 fn n)). Qed.
Lemma lem1105232 {_25569 : Type'} (fn : type1587 _25569) (n : nat) : (term27 _25569 fn n) = (term9 _25569 fn n).
Proof. exact (TRANS (@lem1105230 _25569 fn n) (@lem1105231 _25569 fn n)). Qed.
Lemma lem1105233 {_25569 : Type'} (fn : type1587 _25569) (n : nat) : (term29 _25569 fn n) = (term29 _25569 fn n).
Proof. exact (eq_refl (term29 _25569 fn n)). Qed.
Lemma lem1105234 {_25569 : Type'} (fn : type1587 _25569) (n : nat) : ((term8 _25569 fn n) = (term27 _25569 fn n)) = ((term8 _25569 fn n) = (term9 _25569 fn n)).
Proof. exact (MK_COMB (@lem1105233 _25569 fn n) (@lem1105232 _25569 fn n)). Qed.
Lemma lem1105235 {_25569 : Type'} (fn : type1587 _25569) : (term30 _25569 fn) = (term31 _25569 fn).
Proof. exact (fun_ext (fun n : nat => @lem1105234 _25569 fn n)). Qed.
Lemma lem1105236 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1105237 {_25569 : Type'} (fn : type1587 _25569) : (term32 _25569 fn) = (term6 _25569 fn).
Proof. exact (MK_COMB (@lem1105236) (@lem1105235 _25569 fn)). Qed.
Lemma lem1105238 {_25569 : Type'} (fn : type1587 _25569) : (term33 _25569 fn) = (term33 _25569 fn).
Proof. exact (eq_refl (term33 _25569 fn)). Qed.
Lemma lem1105239 {_25569 : Type'} (fn : type1587 _25569) : (term34 _25569 fn) = (term16 _25569 fn).
Proof. exact (MK_COMB (@lem1105238 _25569 fn) (@lem1105237 _25569 fn)). Qed.
Lemma lem1105240 {_25569 : Type'} : (term35 _25569) = (term36 _25569).
Proof. exact (fun_ext (fun fn : type1587 _25569 => @lem1105239 _25569 fn)). Qed.
Lemma lem1105241 {_25569 : Type'} : (@ex (nat -> (list _25569) -> _25569)) = (@ex (nat -> (list _25569) -> _25569)).
Proof. exact (eq_refl (@ex (nat -> (list _25569) -> _25569))). Qed.
Lemma lem1105242 {_25569 : Type'} : (term23 _25569) = (term37 _25569).
Proof. exact (MK_COMB (@lem1105241 _25569) (@lem1105240 _25569)). Qed.
Lemma lem1105243 {_25569 : Type'} : term37 _25569.
Proof. exact (EQ_MP (@lem1105242 _25569) (@lem1105227 _25569)). Qed.
Lemma lem1105244 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term16 _25569 EL') : term16 _25569 EL'.
Proof. exact (h1). Qed.
Lemma lem1105245 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term16 _25569 EL') : term6 _25569 EL'.
Proof. exact (proj2 (@lem1105244 _25569 EL' h1)). Qed.
Lemma lem1105246 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term16 _25569 EL') : (term0 _25569 EL') = (term1 _25569).
Proof. exact (proj1 (@lem1105244 _25569 EL' h1)). Qed.
Lemma lem1105247 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term16 _25569 EL') : term16 _25569 EL'.
Proof. exact (conj (@lem1105246 _25569 EL' h1) (@lem1105245 _25569 EL' h1)). Qed.
Lemma lem1105248 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term16 _25569 EL') : term37 _25569.
Proof. exact (ex_intro (term36 _25569) EL' (@lem1105247 _25569 EL' h1)). Qed.
Lemma lem1105249 {_25569 : Type'} (h1 : term37 _25569) : term37 _25569.
Proof. exact (h1). Qed.
Lemma lem1105250 {_25569 : Type'} (h1 : term37 _25569) : term37 _25569.
Proof. exact (ex_elim (@lem1105249 _25569 h1) (fun EL' : type1587 _25569 => fun h0 : term36 _25569 EL' => @lem1105248 _25569 EL' h0)). Qed.
Lemma lem1105251 {_25569 : Type'} : (term37 _25569) = (term37 _25569).
Proof. exact (prop_ext (fun h1 : term37 _25569 => @lem1105250 _25569 h1) (fun h1 : term37 _25569 => @lem1105243 _25569)). Qed.
Lemma lem1105252 {_25569 : Type'} : term37 _25569.
Proof. exact (EQ_MP (@lem1105251 _25569) (@lem1105243 _25569)). Qed.
Lemma lem1105253 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term16 _25569 EL') : term38 _25569.
Proof. exact (ex_intro (term39 _25569) EL' (@lem1105219 _25569 EL' h1)). Qed.
Lemma lem1105254 {_25569 : Type'} (h1 : term37 _25569) : term37 _25569.
Proof. exact (h1). Qed.
Lemma lem1105255 {_25569 : Type'} (h1 : term37 _25569) : term38 _25569.
Proof. exact (ex_elim (@lem1105254 _25569 h1) (fun EL' : type1587 _25569 => fun h0 : term36 _25569 EL' => @lem1105253 _25569 EL' h0)). Qed.
Lemma lem1105256 {_25569 : Type'} : (term37 _25569) = (term38 _25569).
Proof. exact (prop_ext (fun h1 : term37 _25569 => @lem1105255 _25569 h1) (fun h1 : term38 _25569 => @lem1105252 _25569)). Qed.
Lemma lem1105257 {_25569 : Type'} : term38 _25569.
Proof. exact (EQ_MP (@lem1105256 _25569) (@lem1105252 _25569)). Qed.
Lemma lem1105260 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term17 _25569 EL') : term17 _25569 EL'.
Proof. exact (h1). Qed.
Lemma lem1105261 {_25569 : Type'} (EL' : type1587 _25569) (h1 : term17 _25569 EL') : term38 _25569.
Proof. exact (ex_intro (term39 _25569) EL' (@lem1105260 _25569 EL' h1)). Qed.
Lemma lem1105262 {_25569 : Type'} (h1 : term38 _25569) : term38 _25569.
Proof. exact (h1). Qed.
Lemma lem1105263 {_25569 : Type'} (h1 : term38 _25569) : term38 _25569.
Proof. exact (ex_elim (@lem1105262 _25569 h1) (fun EL' : type1587 _25569 => fun h0 : term39 _25569 EL' => @lem1105261 _25569 EL' h0)). Qed.
Lemma lem1105264 {_25569 : Type'} : (term38 _25569) = (term38 _25569).
Proof. exact (prop_ext (fun h1 : term38 _25569 => @lem1105263 _25569 h1) (fun h1 : term38 _25569 => @lem1105257 _25569)). Qed.
Lemma lem1105265 {_25569 : Type'} : term38 _25569.
Proof. exact (EQ_MP (@lem1105264 _25569) (@lem1105257 _25569)). Qed.
Lemma lem1105266 {_25569 : Type'} : term40 _25569.
Proof. exact (fun _18015 : prod nat nat => @lem1105265 _25569). Qed.
Lemma lem1105267 {A B : Type'} (P : type1413 A B) : term41 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1105268 {A B : Type'} (P : type1413 A B) : (term41 A B P) = ((term42 A B P) = (term43 A B P)).
Proof. exact (eq_refl (term41 A B P)). Qed.
Lemma lem1105271 {A B : Type'} (P : type1413 A B) : (term42 A B P) = (term43 A B P).
Proof. exact (EQ_MP (@lem1105268 A B P) (@lem1105267 A B P)). Qed.
Lemma lem1105272 {_25569 : Type'} (P : type1318 _25569) : (term44 _25569 P) = (term45 _25569 P).
Proof. exact (@lem1105271 (prod nat nat) (type1587 _25569) P). Qed.
Lemma lem1105273 {_25569 : Type'} : (term46 _25569) = (term47 _25569).
Proof. exact (@lem1105272 _25569 (term48 _25569)). Qed.
Lemma lem1105274 {_25569 : Type'} (_18015 : prod nat nat) : (term49 _25569 _18015) = (term39 _25569).
Proof. exact (eq_refl (term49 _25569 _18015)). Qed.
Lemma lem1105275 {_25569 : Type'} (EL' : type1587 _25569) : EL' = EL'.
Proof. exact (eq_refl EL'). Qed.
Lemma lem1105276 {_25569 : Type'} (_18015 : prod nat nat) (EL' : type1587 _25569) : (term50 _25569 _18015 EL') = (term51 _25569 EL').
Proof. exact (MK_COMB (@lem1105274 _25569 _18015) (@lem1105275 _25569 EL')). Qed.
Lemma lem1105277 {_25569 : Type'} (EL' : type1587 _25569) : (term51 _25569 EL') = (term17 _25569 EL').
Proof. exact (eq_refl (term51 _25569 EL')). Qed.
Lemma lem1105278 {_25569 : Type'} (_18015 : prod nat nat) (EL' : type1587 _25569) : (term50 _25569 _18015 EL') = (term17 _25569 EL').
Proof. exact (TRANS (@lem1105276 _25569 _18015 EL') (@lem1105277 _25569 EL')). Qed.
Lemma lem1105279 {_25569 : Type'} (_18015 : prod nat nat) : (term52 _25569 _18015) = (term39 _25569).
Proof. exact (fun_ext (fun EL' : type1587 _25569 => @lem1105278 _25569 _18015 EL')). Qed.
Lemma lem1105280 {_25569 : Type'} : (@ex (nat -> (list _25569) -> _25569)) = (@ex (nat -> (list _25569) -> _25569)).
Proof. exact (eq_refl (@ex (nat -> (list _25569) -> _25569))). Qed.
Lemma lem1105281 {_25569 : Type'} (_18015 : prod nat nat) : (term53 _25569 _18015) = (term38 _25569).
Proof. exact (MK_COMB (@lem1105280 _25569) (@lem1105279 _25569 _18015)). Qed.
Lemma lem1105282 {_25569 : Type'} : (term54 _25569) = (term55 _25569).
Proof. exact (fun_ext (fun _18015 : prod nat nat => @lem1105281 _25569 _18015)). Qed.
Lemma lem1105283 : (@all (prod nat nat)) = (@all (prod nat nat)).
Proof. exact (eq_refl (@all (prod nat nat))). Qed.
Lemma lem1105284 {_25569 : Type'} : (term46 _25569) = (term40 _25569).
Proof. exact (MK_COMB (@lem1105283) (@lem1105282 _25569)). Qed.
Lemma lem1105285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1105286 {_25569 : Type'} : (term56 _25569) = (term57 _25569).
Proof. exact (MK_COMB (@lem1105285) (@lem1105284 _25569)). Qed.
Lemma lem1105287 {_25569 : Type'} (_18015 : prod nat nat) : (term49 _25569 _18015) = (term39 _25569).
Proof. exact (eq_refl (term49 _25569 _18015)). Qed.
Lemma lem1105288 {_25569 : Type'} (EL' : type1322 _25569) (_18015 : prod nat nat) : (EL' _18015) = (EL' _18015).
Proof. exact (eq_refl (EL' _18015)). Qed.
Lemma lem1105289 {_25569 : Type'} (EL' : type1322 _25569) (_18015 : prod nat nat) : (term58 _25569 EL' _18015) = (term59 _25569 EL' _18015).
Proof. exact (MK_COMB (@lem1105287 _25569 _18015) (@lem1105288 _25569 EL' _18015)). Qed.
Lemma lem1105290 {_25569 : Type'} (EL' : type1322 _25569) (_18015 : prod nat nat) : (term59 _25569 EL' _18015) = (term60 _25569 EL' _18015).
Proof. exact (eq_refl (term59 _25569 EL' _18015)). Qed.
Lemma lem1105291 {_25569 : Type'} (EL' : type1322 _25569) (_18015 : prod nat nat) : (term58 _25569 EL' _18015) = (term60 _25569 EL' _18015).
Proof. exact (TRANS (@lem1105289 _25569 EL' _18015) (@lem1105290 _25569 EL' _18015)). Qed.
Lemma lem1105292 {_25569 : Type'} (EL' : type1322 _25569) : (term61 _25569 EL') = (term62 _25569 EL').
Proof. exact (fun_ext (fun _18015 : prod nat nat => @lem1105291 _25569 EL' _18015)). Qed.
Lemma lem1105293 : (@all (prod nat nat)) = (@all (prod nat nat)).
Proof. exact (eq_refl (@all (prod nat nat))). Qed.
Lemma lem1105294 {_25569 : Type'} (EL' : type1322 _25569) : (term63 _25569 EL') = (term64 _25569 EL').
Proof. exact (MK_COMB (@lem1105293) (@lem1105292 _25569 EL')). Qed.
Lemma lem1105295 {_25569 : Type'} : (term65 _25569) = (term66 _25569).
Proof. exact (fun_ext (fun EL' : type1322 _25569 => @lem1105294 _25569 EL')). Qed.
Lemma lem1105296 {_25569 : Type'} : (@ex ((prod nat nat) -> nat -> (list _25569) -> _25569)) = (@ex ((prod nat nat) -> nat -> (list _25569) -> _25569)).
Proof. exact (eq_refl (@ex ((prod nat nat) -> nat -> (list _25569) -> _25569))). Qed.
Lemma lem1105297 {_25569 : Type'} : (term47 _25569) = (term67 _25569).
Proof. exact (MK_COMB (@lem1105296 _25569) (@lem1105295 _25569)). Qed.
Lemma lem1105298 {_25569 : Type'} : ((term46 _25569) = (term47 _25569)) = ((term40 _25569) = (term67 _25569)).
Proof. exact (MK_COMB (@lem1105286 _25569) (@lem1105297 _25569)). Qed.
Lemma lem1105299 {_25569 : Type'} : (term40 _25569) = (term67 _25569).
Proof. exact (EQ_MP (@lem1105298 _25569) (@lem1105273 _25569)). Qed.
Lemma lem1105300 {_25569 : Type'} : term67 _25569.
Proof. exact (EQ_MP (@lem1105299 _25569) (@lem1105266 _25569)). Qed.
Lemma lem1105302 {A : Type'} : (@ex A) = (term68 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1105303 {_25569 : Type'} : (@ex ((prod nat nat) -> nat -> (list _25569) -> _25569)) = (term69 _25569).
Proof. exact (@lem1105302 (type1322 _25569)). Qed.
Lemma lem1105304 {_25569 : Type'} : (term66 _25569) = (term66 _25569).
Proof. exact (eq_refl (term66 _25569)). Qed.
Lemma lem1105305 {_25569 : Type'} : (term67 _25569) = (term70 _25569).
Proof. exact (MK_COMB (@lem1105303 _25569) (@lem1105304 _25569)). Qed.
Lemma lem1105306 {_25569 : Type'} : (term70 _25569) = (term71 _25569).
Proof. exact (eq_refl (term70 _25569)). Qed.
Lemma lem1105307 {_25569 : Type'} : (term67 _25569) = (term71 _25569).
Proof. exact (TRANS (@lem1105305 _25569) (@lem1105306 _25569)). Qed.
Lemma lem1105308 {_25569 : Type'} : term71 _25569.
Proof. exact (EQ_MP (@lem1105307 _25569) (@lem1105300 _25569)). Qed.
