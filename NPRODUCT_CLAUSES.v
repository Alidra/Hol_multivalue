Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NPRODUCT_CLAUSES_term_abbrevs.
Require Import ITERATE_CLAUSES_spec.
Require Import MONOIDAL_MUL_spec.
Require Import NEUTRAL_MUL_spec.
Require Import SWAP_FORALL_THM_spec.
Require Import thm0_spec.
Require Import thm6898569_spec.
Require Import thm6898583_spec.
Require Import thm7_spec.
Lemma lem6903158 : (@monoidal nat Nat.mul) = ((@monoidal nat Nat.mul) = True).
Proof. exact (@lem7 (@monoidal nat Nat.mul)). Qed.
Lemma lem6903160 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (h1). Qed.
Lemma lem6903161 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term1 _120477 _120519 _120521 op.
Proof. exact (@lem6903160 _120477 _120519 _120521 h1 op). Qed.
Lemma lem6903162 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term1 _120477 _120519 _120521 op) = (term2 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term1 _120477 _120519 _120521 op)). Qed.
Lemma lem6903163 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term2 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6903162 _120477 _120519 _120521 op) (@lem6903161 _120477 _120519 _120521 op h1)). Qed.
Lemma lem6903164 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem6903165 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) (h2 : @monoidal _120519 op) : term3 _120477 _120519 _120521 op.
Proof. exact (@lem6903163 _120477 _120519 _120521 op h1 (@lem6903164 _120519 op h2)). Qed.
Lemma lem6903166 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term4 _120477 _120519 _120521 op.
Proof. exact (fun h0 : term0 _120477 _120519 _120521 => @lem6903165 _120477 _120519 _120521 op h0 h1). Qed.
Lemma lem6903167 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (h1). Qed.
Lemma lem6903168 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) (h2 : @monoidal _120519 op) : term3 _120477 _120519 _120521 op.
Proof. exact (@lem6903166 _120477 _120519 _120521 op h2 (@lem6903167 _120477 _120519 _120521 h1)). Qed.
Lemma lem6903169 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term2 _120477 _120519 _120521 op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6903168 _120477 _120519 _120521 op h1 h0). Qed.
Lemma lem6903170 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (fun op : type1400 _120519 => @lem6903169 _120477 _120519 _120521 op h1). Qed.
Lemma lem6903171 {_120477 _120519 _120521 : Type'} : term5 _120477 _120519 _120521.
Proof. exact (fun h0 : term0 _120477 _120519 _120521 => @lem6903170 _120477 _120519 _120521 h0). Qed.
Lemma lem6903172 {_120477 _120519 _120521 : Type'} : term0 _120477 _120519 _120521.
Proof. exact (@lem6903171 _120477 _120519 _120521 (@lem5753565 _120477 _120519 _120521)). Qed.
Lemma lem6903173 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term1 _120477 _120519 _120521 op.
Proof. exact (@lem6903172 _120477 _120519 _120521 op). Qed.
Lemma lem6903174 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term1 _120477 _120519 _120521 op) = (term2 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term1 _120477 _120519 _120521 op)). Qed.
Lemma lem6903176 {A B : Type'} (P : type1413 A B) : term6 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem6903177 {A B : Type'} (P : type1413 A B) : (term6 A B P) = ((term7 A B P) = (term8 A B P)).
Proof. exact (eq_refl (term6 A B P)). Qed.
Lemma lem6903179 (h1 : (@neutral nat Nat.mul) = term9) : (@neutral nat Nat.mul) = term9.
Proof. exact (h1). Qed.
Lemma lem6903180 (h1 : (@neutral nat Nat.mul) = term9) : term9 = (@neutral nat Nat.mul).
Proof. exact (SYM (@lem6903179 h1)). Qed.
Lemma lem6903181 (h1 : term9 = (@neutral nat Nat.mul)) : term9 = (@neutral nat Nat.mul).
Proof. exact (h1). Qed.
Lemma lem6903182 (h1 : term9 = (@neutral nat Nat.mul)) : (@neutral nat Nat.mul) = term9.
Proof. exact (SYM (@lem6903181 h1)). Qed.
Lemma lem6903183 : ((@neutral nat Nat.mul) = term9) = (term9 = (@neutral nat Nat.mul)).
Proof. exact (prop_ext (fun h1 : (@neutral nat Nat.mul) = term9 => @lem6903180 h1) (fun h1 : term9 = (@neutral nat Nat.mul) => @lem6903182 h1)). Qed.
Lemma lem6903194 {_126105 : Type'} : (@nproduct _126105) = (@iterate nat _126105 Nat.mul).
Proof. exact (TRANS (@lem6898569 _126105) (@lem6898583 _126105)). Qed.
Lemma lem6903195 {_126132 : Type'} : (@nproduct _126132) = (@iterate nat _126132 Nat.mul).
Proof. exact (@lem6903194 _126132). Qed.
Lemma lem6903196 {_126132 : Type'} : (@EMPTY _126132) = (@EMPTY _126132).
Proof. exact (eq_refl (@EMPTY _126132)). Qed.
Lemma lem6903197 {_126132 : Type'} : (@nproduct _126132 (@EMPTY _126132)) = (@iterate nat _126132 Nat.mul (@EMPTY _126132)).
Proof. exact (MK_COMB (@lem6903195 _126132) (@lem6903196 _126132)). Qed.
Lemma lem6903198 {_126132 : Type'} (f : _126132 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6903199 {_126132 : Type'} (f : _126132 -> nat) : (@nproduct _126132 (@EMPTY _126132) f) = (@iterate nat _126132 Nat.mul (@EMPTY _126132) f).
Proof. exact (MK_COMB (@lem6903197 _126132) (@lem6903198 _126132 f)). Qed.
Lemma lem6903200 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6903201 {_126132 : Type'} (f : _126132 -> nat) : (term10 _126132 f) = (term11 _126132 f).
Proof. exact (MK_COMB (@lem6903200) (@lem6903199 _126132 f)). Qed.
Lemma lem6903203 : term9 = (@neutral nat Nat.mul).
Proof. exact (EQ_MP (@lem6903183) (@lem6901232)). Qed.
Lemma lem6903204 {_126132 : Type'} (f : _126132 -> nat) : ((@nproduct _126132 (@EMPTY _126132) f) = term9) = ((@iterate nat _126132 Nat.mul (@EMPTY _126132) f) = (@neutral nat Nat.mul)).
Proof. exact (MK_COMB (@lem6903201 _126132 f) (@lem6903203)). Qed.
Lemma lem6903207 {_126132 : Type'} : (term12 _126132) = (term13 _126132).
Proof. exact (fun_ext (fun f : _126132 -> nat => @lem6903204 _126132 f)). Qed.
Lemma lem6903208 {_126132 : Type'} : (@all (_126132 -> nat)) = (@all (_126132 -> nat)).
Proof. exact (eq_refl (@all (_126132 -> nat))). Qed.
Lemma lem6903209 {_126132 : Type'} : (term14 _126132) = (term15 _126132).
Proof. exact (MK_COMB (@lem6903208 _126132) (@lem6903207 _126132)). Qed.
Lemma lem6903214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6903215 {_126132 : Type'} : (term16 _126132) = (term17 _126132).
Proof. exact (MK_COMB (@lem6903214) (@lem6903209 _126132)). Qed.
Lemma lem6903233 {_126105 : Type'} : (@nproduct _126105) = (@iterate nat _126105 Nat.mul).
Proof. exact (TRANS (@lem6898569 _126105) (@lem6898583 _126105)). Qed.
Lemma lem6903234 {_126171 : Type'} : (@nproduct _126171) = (@iterate nat _126171 Nat.mul).
Proof. exact (@lem6903233 _126171). Qed.
Lemma lem6903235 {_126171 : Type'} (x : _126171) (s : _126171 -> Prop) : (@INSERT _126171 x s) = (@INSERT _126171 x s).
Proof. exact (eq_refl (@INSERT _126171 x s)). Qed.
Lemma lem6903236 {_126171 : Type'} (x : _126171) (s : _126171 -> Prop) : (term18 _126171 x s) = (term19 _126171 x s).
Proof. exact (MK_COMB (@lem6903234 _126171) (@lem6903235 _126171 x s)). Qed.
Lemma lem6903237 {_126171 : Type'} (f : _126171 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6903238 {_126171 : Type'} (x : _126171) (s : _126171 -> Prop) (f : _126171 -> nat) : (term20 _126171 x s f) = (term21 _126171 x s f).
Proof. exact (MK_COMB (@lem6903236 _126171 x s) (@lem6903237 _126171 f)). Qed.
Lemma lem6903239 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6903240 {_126171 : Type'} (x : _126171) (s : _126171 -> Prop) (f : _126171 -> nat) : (term22 _126171 x s f) = (term23 _126171 x s f).
Proof. exact (MK_COMB (@lem6903239) (@lem6903238 _126171 x s f)). Qed.
Lemma lem6903242 {_126105 : Type'} : (@nproduct _126105) = (@iterate nat _126105 Nat.mul).
Proof. exact (TRANS (@lem6898569 _126105) (@lem6898583 _126105)). Qed.
Lemma lem6903243 {_126171 : Type'} : (@nproduct _126171) = (@iterate nat _126171 Nat.mul).
Proof. exact (@lem6903242 _126171). Qed.
Lemma lem6903244 {_126171 : Type'} (s : _126171 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6903245 {_126171 : Type'} (s : _126171 -> Prop) : (@nproduct _126171 s) = (@iterate nat _126171 Nat.mul s).
Proof. exact (MK_COMB (@lem6903243 _126171) (@lem6903244 _126171 s)). Qed.
Lemma lem6903246 {_126171 : Type'} (f : _126171 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6903247 {_126171 : Type'} (s : _126171 -> Prop) (f : _126171 -> nat) : (@nproduct _126171 s f) = (@iterate nat _126171 Nat.mul s f).
Proof. exact (MK_COMB (@lem6903245 _126171 s) (@lem6903246 _126171 f)). Qed.
Lemma lem6903248 {_126171 : Type'} (x : _126171) (s : _126171 -> Prop) : (term24 _126171 x s) = (term24 _126171 x s).
Proof. exact (eq_refl (term24 _126171 x s)). Qed.
Lemma lem6903249 {_126171 : Type'} (x : _126171) (s : _126171 -> Prop) (f : _126171 -> nat) : (term25 _126171 x s f) = (term26 _126171 x s f).
Proof. exact (MK_COMB (@lem6903248 _126171 x s) (@lem6903247 _126171 s f)). Qed.
Lemma lem6903251 {_126105 : Type'} : (@nproduct _126105) = (@iterate nat _126105 Nat.mul).
Proof. exact (TRANS (@lem6898569 _126105) (@lem6898583 _126105)). Qed.
Lemma lem6903252 {_126171 : Type'} : (@nproduct _126171) = (@iterate nat _126171 Nat.mul).
Proof. exact (@lem6903251 _126171). Qed.
Lemma lem6903253 {_126171 : Type'} (s : _126171 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6903254 {_126171 : Type'} (s : _126171 -> Prop) : (@nproduct _126171 s) = (@iterate nat _126171 Nat.mul s).
Proof. exact (MK_COMB (@lem6903252 _126171) (@lem6903253 _126171 s)). Qed.
Lemma lem6903255 {_126171 : Type'} (f : _126171 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6903256 {_126171 : Type'} (s : _126171 -> Prop) (f : _126171 -> nat) : (@nproduct _126171 s f) = (@iterate nat _126171 Nat.mul s f).
Proof. exact (MK_COMB (@lem6903254 _126171 s) (@lem6903255 _126171 f)). Qed.
Lemma lem6903257 {_126171 : Type'} (f : _126171 -> nat) (x : _126171) : (term27 _126171 f x) = (term27 _126171 f x).
Proof. exact (eq_refl (term27 _126171 f x)). Qed.
Lemma lem6903258 {_126171 : Type'} (x : _126171) (s : _126171 -> Prop) (f : _126171 -> nat) : (term28 _126171 x s f) = (term29 _126171 x s f).
Proof. exact (MK_COMB (@lem6903257 _126171 f x) (@lem6903256 _126171 s f)). Qed.
Lemma lem6903259 {_126171 : Type'} (x : _126171) (s : _126171 -> Prop) (f : _126171 -> nat) : (term30 _126171 x s f) = (term31 _126171 x s f).
Proof. exact (MK_COMB (@lem6903249 _126171 x s f) (@lem6903258 _126171 x s f)). Qed.
Lemma lem6903260 {_126171 : Type'} (x : _126171) (s : _126171 -> Prop) (f : _126171 -> nat) : ((term20 _126171 x s f) = (term30 _126171 x s f)) = ((term21 _126171 x s f) = (term31 _126171 x s f)).
Proof. exact (MK_COMB (@lem6903240 _126171 x s f) (@lem6903259 _126171 x s f)). Qed.
Lemma lem6903263 {_126171 : Type'} (s : _126171 -> Prop) : (term32 _126171 s) = (term32 _126171 s).
Proof. exact (eq_refl (term32 _126171 s)). Qed.
Lemma lem6903264 {_126171 : Type'} (x : _126171) (s : _126171 -> Prop) (f : _126171 -> nat) : (term33 _126171 x s f) = (term34 _126171 x s f).
Proof. exact (MK_COMB (@lem6903263 _126171 s) (@lem6903260 _126171 x s f)). Qed.
Lemma lem6903267 {_126171 : Type'} (x : _126171) (f : _126171 -> nat) : (term35 _126171 x f) = (term36 _126171 x f).
Proof. exact (fun_ext (fun s : _126171 -> Prop => @lem6903264 _126171 x s f)). Qed.
Lemma lem6903268 {_126171 : Type'} : (@all (_126171 -> Prop)) = (@all (_126171 -> Prop)).
Proof. exact (eq_refl (@all (_126171 -> Prop))). Qed.
Lemma lem6903269 {_126171 : Type'} (x : _126171) (f : _126171 -> nat) : (term37 _126171 x f) = (term38 _126171 x f).
Proof. exact (MK_COMB (@lem6903268 _126171) (@lem6903267 _126171 x f)). Qed.
Lemma lem6903274 {_126171 : Type'} (x : _126171) : (term39 _126171 x) = (term40 _126171 x).
Proof. exact (fun_ext (fun f : _126171 -> nat => @lem6903269 _126171 x f)). Qed.
Lemma lem6903275 {_126171 : Type'} : (@all (_126171 -> nat)) = (@all (_126171 -> nat)).
Proof. exact (eq_refl (@all (_126171 -> nat))). Qed.
Lemma lem6903276 {_126171 : Type'} (x : _126171) : (term41 _126171 x) = (term42 _126171 x).
Proof. exact (MK_COMB (@lem6903275 _126171) (@lem6903274 _126171 x)). Qed.
Lemma lem6903281 {_126171 : Type'} : (term43 _126171) = (term44 _126171).
Proof. exact (fun_ext (fun x : _126171 => @lem6903276 _126171 x)). Qed.
Lemma lem6903282 {_126171 : Type'} : (@all _126171) = (@all _126171).
Proof. exact (eq_refl (@all _126171)). Qed.
Lemma lem6903283 {_126171 : Type'} : (term45 _126171) = (term46 _126171).
Proof. exact (MK_COMB (@lem6903282 _126171) (@lem6903281 _126171)). Qed.
Lemma lem6903288 {_126132 _126171 : Type'} : (term47 _126132 _126171) = (term48 _126132 _126171).
Proof. exact (MK_COMB (@lem6903215 _126132) (@lem6903283 _126171)). Qed.
Lemma lem6903291 {_126132 _126171 : Type'} : (term48 _126132 _126171) = (term47 _126132 _126171).
Proof. exact (SYM (@lem6903288 _126132 _126171)). Qed.
Lemma lem6903301 {A B : Type'} (P : type1413 A B) : (term7 A B P) = (term8 A B P).
Proof. exact (EQ_MP (@lem6903177 A B P) (@lem6903176 A B P)). Qed.
Lemma lem6903302 {_126171 : Type'} (P : type1366 _126171) : (term49 _126171 P) = (term50 _126171 P).
Proof. exact (@lem6903301 _126171 (_126171 -> nat) P). Qed.
Lemma lem6903303 {_126171 : Type'} : (term51 _126171) = (term52 _126171).
Proof. exact (@lem6903302 _126171 (term53 _126171)). Qed.
Lemma lem6903304 {_126171 : Type'} (x : _126171) : (term54 _126171 x) = (term40 _126171 x).
Proof. exact (eq_refl (term54 _126171 x)). Qed.
Lemma lem6903305 {_126171 : Type'} (f : _126171 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6903306 {_126171 : Type'} (x : _126171) (f : _126171 -> nat) : (term55 _126171 x f) = (term56 _126171 x f).
Proof. exact (MK_COMB (@lem6903304 _126171 x) (@lem6903305 _126171 f)). Qed.
Lemma lem6903307 {_126171 : Type'} (x : _126171) (f : _126171 -> nat) : (term56 _126171 x f) = (term38 _126171 x f).
Proof. exact (eq_refl (term56 _126171 x f)). Qed.
Lemma lem6903308 {_126171 : Type'} (x : _126171) (f : _126171 -> nat) : (term55 _126171 x f) = (term38 _126171 x f).
Proof. exact (TRANS (@lem6903306 _126171 x f) (@lem6903307 _126171 x f)). Qed.
Lemma lem6903309 {_126171 : Type'} (x : _126171) : (term57 _126171 x) = (term40 _126171 x).
Proof. exact (fun_ext (fun f : _126171 -> nat => @lem6903308 _126171 x f)). Qed.
Lemma lem6903310 {_126171 : Type'} : (@all (_126171 -> nat)) = (@all (_126171 -> nat)).
Proof. exact (eq_refl (@all (_126171 -> nat))). Qed.
Lemma lem6903311 {_126171 : Type'} (x : _126171) : (term58 _126171 x) = (term42 _126171 x).
Proof. exact (MK_COMB (@lem6903310 _126171) (@lem6903309 _126171 x)). Qed.
Lemma lem6903312 {_126171 : Type'} : (term59 _126171) = (term44 _126171).
Proof. exact (fun_ext (fun x : _126171 => @lem6903311 _126171 x)). Qed.
Lemma lem6903313 {_126171 : Type'} : (@all _126171) = (@all _126171).
Proof. exact (eq_refl (@all _126171)). Qed.
Lemma lem6903314 {_126171 : Type'} : (term51 _126171) = (term46 _126171).
Proof. exact (MK_COMB (@lem6903313 _126171) (@lem6903312 _126171)). Qed.
Lemma lem6903315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6903316 {_126171 : Type'} : (term60 _126171) = (term61 _126171).
Proof. exact (MK_COMB (@lem6903315) (@lem6903314 _126171)). Qed.
Lemma lem6903317 {_126171 : Type'} (x : _126171) : (term54 _126171 x) = (term40 _126171 x).
Proof. exact (eq_refl (term54 _126171 x)). Qed.
Lemma lem6903318 {_126171 : Type'} (f : _126171 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6903319 {_126171 : Type'} (x : _126171) (f : _126171 -> nat) : (term55 _126171 x f) = (term56 _126171 x f).
Proof. exact (MK_COMB (@lem6903317 _126171 x) (@lem6903318 _126171 f)). Qed.
Lemma lem6903320 {_126171 : Type'} (x : _126171) (f : _126171 -> nat) : (term56 _126171 x f) = (term38 _126171 x f).
Proof. exact (eq_refl (term56 _126171 x f)). Qed.
Lemma lem6903321 {_126171 : Type'} (x : _126171) (f : _126171 -> nat) : (term55 _126171 x f) = (term38 _126171 x f).
Proof. exact (TRANS (@lem6903319 _126171 x f) (@lem6903320 _126171 x f)). Qed.
Lemma lem6903322 {_126171 : Type'} (f : _126171 -> nat) : (term62 _126171 f) = (term63 _126171 f).
Proof. exact (fun_ext (fun x : _126171 => @lem6903321 _126171 x f)). Qed.
Lemma lem6903323 {_126171 : Type'} : (@all _126171) = (@all _126171).
Proof. exact (eq_refl (@all _126171)). Qed.
Lemma lem6903324 {_126171 : Type'} (f : _126171 -> nat) : (term64 _126171 f) = (term65 _126171 f).
Proof. exact (MK_COMB (@lem6903323 _126171) (@lem6903322 _126171 f)). Qed.
Lemma lem6903325 {_126171 : Type'} : (term66 _126171) = (term67 _126171).
Proof. exact (fun_ext (fun f : _126171 -> nat => @lem6903324 _126171 f)). Qed.
Lemma lem6903326 {_126171 : Type'} : (@all (_126171 -> nat)) = (@all (_126171 -> nat)).
Proof. exact (eq_refl (@all (_126171 -> nat))). Qed.
Lemma lem6903327 {_126171 : Type'} : (term52 _126171) = (term68 _126171).
Proof. exact (MK_COMB (@lem6903326 _126171) (@lem6903325 _126171)). Qed.
Lemma lem6903328 {_126171 : Type'} : ((term51 _126171) = (term52 _126171)) = ((term46 _126171) = (term68 _126171)).
Proof. exact (MK_COMB (@lem6903316 _126171) (@lem6903327 _126171)). Qed.
Lemma lem6903329 {_126171 : Type'} : (term46 _126171) = (term68 _126171).
Proof. exact (EQ_MP (@lem6903328 _126171) (@lem6903303 _126171)). Qed.
Lemma lem6903330 {_126132 : Type'} : (term17 _126132) = (term17 _126132).
Proof. exact (eq_refl (term17 _126132)). Qed.
Lemma lem6903331 {_126132 _126171 : Type'} : (term48 _126132 _126171) = (term69 _126132 _126171).
Proof. exact (MK_COMB (@lem6903330 _126132) (@lem6903329 _126171)). Qed.
Lemma lem6903332 {_126132 _126171 : Type'} : (term69 _126132 _126171) = (term48 _126132 _126171).
Proof. exact (SYM (@lem6903331 _126132 _126171)). Qed.
Lemma lem6903334 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term2 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6903174 _120477 _120519 _120521 op) (@lem6903173 _120477 _120519 _120521 op)). Qed.
Lemma lem6903335 {_126132 _126171 : Type'} (op : type1606) : term70 _126132 _126171 op.
Proof. exact (@lem6903334 _126132 nat _126171 op). Qed.
Lemma lem6903336 {_126132 _126171 : Type'} : term71 _126132 _126171.
Proof. exact (@lem6903335 _126132 _126171 Nat.mul). Qed.
Lemma lem6903338 : (@monoidal nat Nat.mul) = True.
Proof. exact (EQ_MP (@lem6903158) (@lem6903157)). Qed.
Lemma lem6903339 : True = (@monoidal nat Nat.mul).
Proof. exact (SYM (@lem6903338)). Qed.
Lemma lem6903340 : @monoidal nat Nat.mul.
Proof. exact (EQ_MP (@lem6903339) (@lem0)). Qed.
Lemma lem6903341 {_126132 _126171 : Type'} : term69 _126132 _126171.
Proof. exact (@lem6903336 _126132 _126171 (@lem6903340)). Qed.
Lemma lem6903342 {_126132 _126171 : Type'} : term48 _126132 _126171.
Proof. exact (EQ_MP (@lem6903332 _126132 _126171) (@lem6903341 _126132 _126171)). Qed.
Lemma lem6903343 {_126132 _126171 : Type'} : term47 _126132 _126171.
Proof. exact (EQ_MP (@lem6903291 _126132 _126171) (@lem6903342 _126132 _126171)). Qed.
