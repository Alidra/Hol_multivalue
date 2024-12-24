Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4784335_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem4784222 {A : Type'} (set_of_list' : type1136 A) (h1 : (set_of_list' (@nil A)) = (@EMPTY A)) : (set_of_list' (@nil A)) = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4784223 {A : Type'} (set_of_list' : type1136 A) (h1 : term0 A set_of_list') : term0 A set_of_list'.
Proof. exact (h1). Qed.
Lemma lem4784224 {A : Type'} (h : A) (set_of_list' : type1136 A) (h1 : term0 A set_of_list') : term1 A set_of_list' h.
Proof. exact (@lem4784223 A set_of_list' h1 h). Qed.
Lemma lem4784225 {A : Type'} (h : A) (set_of_list' : type1136 A) : (term1 A set_of_list' h) = (term2 A h set_of_list').
Proof. exact (eq_refl (term1 A set_of_list' h)). Qed.
Lemma lem4784226 {A : Type'} (h : A) (set_of_list' : type1136 A) (h1 : term0 A set_of_list') : term2 A h set_of_list'.
Proof. exact (EQ_MP (@lem4784225 A h set_of_list') (@lem4784224 A h set_of_list' h1)). Qed.
Lemma lem4784227 {A : Type'} (h : A) (t : list A) (set_of_list' : type1136 A) (h1 : term0 A set_of_list') : term3 A h set_of_list' t.
Proof. exact (@lem4784226 A h set_of_list' h1 t). Qed.
Lemma lem4784228 {A : Type'} (h : A) (set_of_list' : type1136 A) (t : list A) : (term3 A h set_of_list' t) = ((term4 A set_of_list' h t) = (term5 A h set_of_list' t)).
Proof. exact (eq_refl (term3 A h set_of_list' t)). Qed.
Lemma lem4784229 {A : Type'} (h : A) (t : list A) (set_of_list' : type1136 A) (h1 : term0 A set_of_list') : (term4 A set_of_list' h t) = (term5 A h set_of_list' t).
Proof. exact (EQ_MP (@lem4784228 A h set_of_list' t) (@lem4784227 A h t set_of_list' h1)). Qed.
Lemma lem4784230 {A : Type'} (h : A) (set_of_list' : type1136 A) (h1 : term0 A set_of_list') : term2 A h set_of_list'.
Proof. exact (fun t : list A => @lem4784229 A h t set_of_list' h1). Qed.
Lemma lem4784231 {A : Type'} (set_of_list' : type1136 A) (h1 : term0 A set_of_list') : term0 A set_of_list'.
Proof. exact (fun h : A => @lem4784230 A h set_of_list' h1). Qed.
Lemma lem4784232 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : term6 A set_of_list'.
Proof. exact (h1). Qed.
Lemma lem4784233 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : term0 A set_of_list'.
Proof. exact (proj2 (@lem4784232 A set_of_list' h1)). Qed.
Lemma lem4784234 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : (set_of_list' (@nil A)) = (@EMPTY A).
Proof. exact (proj1 (@lem4784232 A set_of_list' h1)). Qed.
Lemma lem4784235 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : ((set_of_list' (@nil A)) = (@EMPTY A)) = ((set_of_list' (@nil A)) = (@EMPTY A)).
Proof. exact (prop_ext (fun h2 : (set_of_list' (@nil A)) = (@EMPTY A) => @lem4784222 A set_of_list' h2) (fun h2 : (set_of_list' (@nil A)) = (@EMPTY A) => @lem4784234 A set_of_list' h1)). Qed.
Lemma lem4784236 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : (set_of_list' (@nil A)) = (@EMPTY A).
Proof. exact (EQ_MP (@lem4784235 A set_of_list' h1) (@lem4784234 A set_of_list' h1)). Qed.
Lemma lem4784237 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : (term0 A set_of_list') = (term0 A set_of_list').
Proof. exact (prop_ext (fun h2 : term0 A set_of_list' => @lem4784231 A set_of_list' h2) (fun h2 : term0 A set_of_list' => @lem4784233 A set_of_list' h1)). Qed.
Lemma lem4784238 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : term0 A set_of_list'.
Proof. exact (EQ_MP (@lem4784237 A set_of_list' h1) (@lem4784233 A set_of_list' h1)). Qed.
Lemma lem4784239 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : term6 A set_of_list'.
Proof. exact (conj (@lem4784236 A set_of_list' h1) (@lem4784238 A set_of_list' h1)). Qed.
Lemma lem4784240 {A Z : Type'} (NIL' : Z) : term7 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem4784241 {A Z : Type'} (NIL' : Z) : (term7 A Z NIL') = (term8 A Z NIL').
Proof. exact (eq_refl (term7 A Z NIL')). Qed.
Lemma lem4784242 {A Z : Type'} (NIL' : Z) : term8 A Z NIL'.
Proof. exact (EQ_MP (@lem4784241 A Z NIL') (@lem4784240 A Z NIL')). Qed.
Lemma lem4784243 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term9 A Z NIL' CONS'.
Proof. exact (@lem4784242 A Z NIL' CONS'). Qed.
Lemma lem4784244 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term9 A Z NIL' CONS') = (term10 A Z NIL' CONS').
Proof. exact (eq_refl (term9 A Z NIL' CONS')). Qed.
Lemma lem4784245 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term10 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem4784244 A Z NIL' CONS') (@lem4784243 A Z NIL' CONS')). Qed.
Lemma lem4784246 {A : Type'} (NIL' : A -> Prop) (CONS' : type1390 A) : term11 A NIL' CONS'.
Proof. exact (@lem4784245 A (A -> Prop) NIL' CONS'). Qed.
Lemma lem4784247 {A : Type'} : term12 A.
Proof. exact (@lem4784246 A (@EMPTY A) (term13 A)). Qed.
Lemma lem4784248 {A : Type'} (a0 : A) : (term14 A a0) = (term15 A a0).
Proof. exact (eq_refl (term14 A a0)). Qed.
Lemma lem4784249 {A : Type'} (a1 : list A) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem4784250 {A : Type'} (a0 : A) (a1 : list A) : (term16 A a0 a1) = (term17 A a0 a1).
Proof. exact (MK_COMB (@lem4784248 A a0) (@lem4784249 A a1)). Qed.
Lemma lem4784251 {A : Type'} (a1 : list A) (a0 : A) : (term17 A a0 a1) = (term18 A a0).
Proof. exact (eq_refl (term17 A a0 a1)). Qed.
Lemma lem4784252 {A : Type'} (a1 : list A) (a0 : A) : (term16 A a0 a1) = (term18 A a0).
Proof. exact (TRANS (@lem4784250 A a0 a1) (@lem4784251 A a1 a0)). Qed.
Lemma lem4784253 {A : Type'} (fn : type1136 A) (a1 : list A) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem4784254 {A : Type'} (a0 : A) (fn : type1136 A) (a1 : list A) : (term19 A a0 fn a1) = (term20 A a0 fn a1).
Proof. exact (MK_COMB (@lem4784252 A a1 a0) (@lem4784253 A fn a1)). Qed.
Lemma lem4784255 {A : Type'} (a0 : A) (fn : type1136 A) (a1 : list A) : (term20 A a0 fn a1) = (term5 A a0 fn a1).
Proof. exact (eq_refl (term20 A a0 fn a1)). Qed.
Lemma lem4784256 {A : Type'} (a0 : A) (fn : type1136 A) (a1 : list A) : (term19 A a0 fn a1) = (term5 A a0 fn a1).
Proof. exact (TRANS (@lem4784254 A a0 fn a1) (@lem4784255 A a0 fn a1)). Qed.
Lemma lem4784257 {A : Type'} (fn : type1136 A) (a0 : A) (a1 : list A) : (term21 A fn a0 a1) = (term21 A fn a0 a1).
Proof. exact (eq_refl (term21 A fn a0 a1)). Qed.
Lemma lem4784258 {A : Type'} (a0 : A) (fn : type1136 A) (a1 : list A) : ((term4 A fn a0 a1) = (term19 A a0 fn a1)) = ((term4 A fn a0 a1) = (term5 A a0 fn a1)).
Proof. exact (MK_COMB (@lem4784257 A fn a0 a1) (@lem4784256 A a0 fn a1)). Qed.
Lemma lem4784259 {A : Type'} (a0 : A) (fn : type1136 A) : (term22 A a0 fn) = (term23 A a0 fn).
Proof. exact (fun_ext (fun a1 : list A => @lem4784258 A a0 fn a1)). Qed.
Lemma lem4784260 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem4784261 {A : Type'} (a0 : A) (fn : type1136 A) : (term24 A a0 fn) = (term2 A a0 fn).
Proof. exact (MK_COMB (@lem4784260 A) (@lem4784259 A a0 fn)). Qed.
Lemma lem4784262 {A : Type'} (fn : type1136 A) : (term25 A fn) = (term26 A fn).
Proof. exact (fun_ext (fun a0 : A => @lem4784261 A a0 fn)). Qed.
Lemma lem4784263 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4784264 {A : Type'} (fn : type1136 A) : (term27 A fn) = (term0 A fn).
Proof. exact (MK_COMB (@lem4784263 A) (@lem4784262 A fn)). Qed.
Lemma lem4784265 {A : Type'} (fn : type1136 A) : (term28 A fn) = (term28 A fn).
Proof. exact (eq_refl (term28 A fn)). Qed.
Lemma lem4784266 {A : Type'} (fn : type1136 A) : (term29 A fn) = (term6 A fn).
Proof. exact (MK_COMB (@lem4784265 A fn) (@lem4784264 A fn)). Qed.
Lemma lem4784267 {A : Type'} : (term30 A) = (term31 A).
Proof. exact (fun_ext (fun fn : type1136 A => @lem4784266 A fn)). Qed.
Lemma lem4784268 {A : Type'} : (@ex ((list A) -> A -> Prop)) = (@ex ((list A) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((list A) -> A -> Prop))). Qed.
Lemma lem4784269 {A : Type'} : (term12 A) = (term32 A).
Proof. exact (MK_COMB (@lem4784268 A) (@lem4784267 A)). Qed.
Lemma lem4784270 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem4784269 A) (@lem4784247 A)). Qed.
Lemma lem4784271 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : term6 A set_of_list'.
Proof. exact (h1). Qed.
Lemma lem4784272 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : term0 A set_of_list'.
Proof. exact (proj2 (@lem4784271 A set_of_list' h1)). Qed.
Lemma lem4784273 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : (set_of_list' (@nil A)) = (@EMPTY A).
Proof. exact (proj1 (@lem4784271 A set_of_list' h1)). Qed.
Lemma lem4784274 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : term6 A set_of_list'.
Proof. exact (conj (@lem4784273 A set_of_list' h1) (@lem4784272 A set_of_list' h1)). Qed.
Lemma lem4784275 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : term32 A.
Proof. exact (ex_intro (term31 A) set_of_list' (@lem4784274 A set_of_list' h1)). Qed.
Lemma lem4784276 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem4784277 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (ex_elim (@lem4784276 A h1) (fun set_of_list' : type1136 A => fun h0 : term31 A set_of_list' => @lem4784275 A set_of_list' h0)). Qed.
Lemma lem4784278 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (prop_ext (fun h1 : term32 A => @lem4784277 A h1) (fun h1 : term32 A => @lem4784270 A)). Qed.
Lemma lem4784279 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem4784278 A) (@lem4784270 A)). Qed.
Lemma lem4784280 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : term32 A.
Proof. exact (ex_intro (term31 A) set_of_list' (@lem4784239 A set_of_list' h1)). Qed.
Lemma lem4784281 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem4784282 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (ex_elim (@lem4784281 A h1) (fun set_of_list' : type1136 A => fun h0 : term31 A set_of_list' => @lem4784280 A set_of_list' h0)). Qed.
Lemma lem4784283 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (prop_ext (fun h1 : term32 A => @lem4784282 A h1) (fun h1 : term32 A => @lem4784279 A)). Qed.
Lemma lem4784284 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem4784283 A) (@lem4784279 A)). Qed.
Lemma lem4784287 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : term6 A set_of_list'.
Proof. exact (h1). Qed.
Lemma lem4784288 {A : Type'} (set_of_list' : type1136 A) (h1 : term6 A set_of_list') : term32 A.
Proof. exact (ex_intro (term31 A) set_of_list' (@lem4784287 A set_of_list' h1)). Qed.
Lemma lem4784289 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem4784290 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (ex_elim (@lem4784289 A h1) (fun set_of_list' : type1136 A => fun h0 : term31 A set_of_list' => @lem4784288 A set_of_list' h0)). Qed.
Lemma lem4784291 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (prop_ext (fun h1 : term32 A => @lem4784290 A h1) (fun h1 : term32 A => @lem4784284 A)). Qed.
Lemma lem4784292 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem4784291 A) (@lem4784284 A)). Qed.
Lemma lem4784293 {A : Type'} : term33 A.
Proof. exact (fun _59117 : type1667 => @lem4784292 A). Qed.
Lemma lem4784294 {A B : Type'} (P : type1413 A B) : term34 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem4784295 {A B : Type'} (P : type1413 A B) : (term34 A B P) = ((term35 A B P) = (term36 A B P)).
Proof. exact (eq_refl (term34 A B P)). Qed.
Lemma lem4784298 {A B : Type'} (P : type1413 A B) : (term35 A B P) = (term36 A B P).
Proof. exact (EQ_MP (@lem4784295 A B P) (@lem4784294 A B P)). Qed.
Lemma lem4784299 {A : Type'} (P : type1236 A) : (term37 A P) = (term38 A P).
Proof. exact (@lem4784298 type1667 (type1136 A) P). Qed.
Lemma lem4784300 {A : Type'} : (term39 A) = (term40 A).
Proof. exact (@lem4784299 A (term41 A)). Qed.
Lemma lem4784301 {A : Type'} (_59117 : type1667) : (term42 A _59117) = (term31 A).
Proof. exact (eq_refl (term42 A _59117)). Qed.
Lemma lem4784302 {A : Type'} (set_of_list' : type1136 A) : set_of_list' = set_of_list'.
Proof. exact (eq_refl set_of_list'). Qed.
Lemma lem4784303 {A : Type'} (_59117 : type1667) (set_of_list' : type1136 A) : (term43 A _59117 set_of_list') = (term44 A set_of_list').
Proof. exact (MK_COMB (@lem4784301 A _59117) (@lem4784302 A set_of_list')). Qed.
Lemma lem4784304 {A : Type'} (set_of_list' : type1136 A) : (term44 A set_of_list') = (term6 A set_of_list').
Proof. exact (eq_refl (term44 A set_of_list')). Qed.
Lemma lem4784305 {A : Type'} (_59117 : type1667) (set_of_list' : type1136 A) : (term43 A _59117 set_of_list') = (term6 A set_of_list').
Proof. exact (TRANS (@lem4784303 A _59117 set_of_list') (@lem4784304 A set_of_list')). Qed.
Lemma lem4784306 {A : Type'} (_59117 : type1667) : (term45 A _59117) = (term31 A).
Proof. exact (fun_ext (fun set_of_list' : type1136 A => @lem4784305 A _59117 set_of_list')). Qed.
Lemma lem4784307 {A : Type'} : (@ex ((list A) -> A -> Prop)) = (@ex ((list A) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((list A) -> A -> Prop))). Qed.
Lemma lem4784308 {A : Type'} (_59117 : type1667) : (term46 A _59117) = (term32 A).
Proof. exact (MK_COMB (@lem4784307 A) (@lem4784306 A _59117)). Qed.
Lemma lem4784309 {A : Type'} : (term47 A) = (term48 A).
Proof. exact (fun_ext (fun _59117 : type1667 => @lem4784308 A _59117)). Qed.
Lemma lem4784310 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))))). Qed.
Lemma lem4784311 {A : Type'} : (term39 A) = (term33 A).
Proof. exact (MK_COMB (@lem4784310) (@lem4784309 A)). Qed.
Lemma lem4784312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4784313 {A : Type'} : (term49 A) = (term50 A).
Proof. exact (MK_COMB (@lem4784312) (@lem4784311 A)). Qed.
Lemma lem4784314 {A : Type'} (_59117 : type1667) : (term42 A _59117) = (term31 A).
Proof. exact (eq_refl (term42 A _59117)). Qed.
Lemma lem4784315 {A : Type'} (set_of_list' : type1238 A) (_59117 : type1667) : (set_of_list' _59117) = (set_of_list' _59117).
Proof. exact (eq_refl (set_of_list' _59117)). Qed.
Lemma lem4784316 {A : Type'} (set_of_list' : type1238 A) (_59117 : type1667) : (term51 A set_of_list' _59117) = (term52 A set_of_list' _59117).
Proof. exact (MK_COMB (@lem4784314 A _59117) (@lem4784315 A set_of_list' _59117)). Qed.
Lemma lem4784317 {A : Type'} (set_of_list' : type1238 A) (_59117 : type1667) : (term52 A set_of_list' _59117) = (term53 A set_of_list' _59117).
Proof. exact (eq_refl (term52 A set_of_list' _59117)). Qed.
Lemma lem4784318 {A : Type'} (set_of_list' : type1238 A) (_59117 : type1667) : (term51 A set_of_list' _59117) = (term53 A set_of_list' _59117).
Proof. exact (TRANS (@lem4784316 A set_of_list' _59117) (@lem4784317 A set_of_list' _59117)). Qed.
Lemma lem4784319 {A : Type'} (set_of_list' : type1238 A) : (term54 A set_of_list') = (term55 A set_of_list').
Proof. exact (fun_ext (fun _59117 : type1667 => @lem4784318 A set_of_list' _59117)). Qed.
Lemma lem4784320 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))))). Qed.
Lemma lem4784321 {A : Type'} (set_of_list' : type1238 A) : (term56 A set_of_list') = (term57 A set_of_list').
Proof. exact (MK_COMB (@lem4784320) (@lem4784319 A set_of_list')). Qed.
Lemma lem4784322 {A : Type'} : (term58 A) = (term59 A).
Proof. exact (fun_ext (fun set_of_list' : type1238 A => @lem4784321 A set_of_list')). Qed.
Lemma lem4784323 {A : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list A) -> A -> Prop)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list A) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list A) -> A -> Prop))). Qed.
Lemma lem4784324 {A : Type'} : (term40 A) = (term60 A).
Proof. exact (MK_COMB (@lem4784323 A) (@lem4784322 A)). Qed.
Lemma lem4784325 {A : Type'} : ((term39 A) = (term40 A)) = ((term33 A) = (term60 A)).
Proof. exact (MK_COMB (@lem4784313 A) (@lem4784324 A)). Qed.
Lemma lem4784326 {A : Type'} : (term33 A) = (term60 A).
Proof. exact (EQ_MP (@lem4784325 A) (@lem4784300 A)). Qed.
Lemma lem4784327 {A : Type'} : term60 A.
Proof. exact (EQ_MP (@lem4784326 A) (@lem4784293 A)). Qed.
Lemma lem4784329 {A : Type'} : (@ex A) = (term61 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem4784330 {A : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list A) -> A -> Prop)) = (term62 A).
Proof. exact (@lem4784329 (type1238 A)). Qed.
Lemma lem4784331 {A : Type'} : (term59 A) = (term59 A).
Proof. exact (eq_refl (term59 A)). Qed.
Lemma lem4784332 {A : Type'} : (term60 A) = (term63 A).
Proof. exact (MK_COMB (@lem4784330 A) (@lem4784331 A)). Qed.
Lemma lem4784333 {A : Type'} : (term63 A) = (term64 A).
Proof. exact (eq_refl (term63 A)). Qed.
Lemma lem4784334 {A : Type'} : (term60 A) = (term64 A).
Proof. exact (TRANS (@lem4784332 A) (@lem4784333 A)). Qed.
Lemma lem4784335 {A : Type'} : term64 A.
Proof. exact (EQ_MP (@lem4784334 A) (@lem4784327 A)). Qed.
