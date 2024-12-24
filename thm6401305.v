Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6401305_term_abbrevs.
Require Import thm6399998_spec.
Require Import thm6401229_spec.
Lemma lem6401230 {A K : Type'} : (term0 A K) = (term1 A K).
Proof. exact (eq_refl (term0 A K)). Qed.
Lemma lem6401231 {A K : Type'} : term1 A K.
Proof. exact (EQ_MP (@lem6401230 A K) (@lem6399998 A K)). Qed.
Lemma lem6401232 {A K : Type'} : term2 A K.
Proof. exact (@lem6401231 A K term3). Qed.
Lemma lem6401233 {A K : Type'} : (term2 A K) = (term4 A K).
Proof. exact (eq_refl (term2 A K)). Qed.
Lemma lem6401234 {A K : Type'} : term4 A K.
Proof. exact (EQ_MP (@lem6401233 A K) (@lem6401232 A K)). Qed.
Lemma lem6401235 {A K : Type'} (h1 : (@iterato A K) = (term5 A K)) : (@iterato A K) = (term5 A K).
Proof. exact (h1). Qed.
Lemma lem6401236 {A K : Type'} (h1 : (@iterato A K) = (term5 A K)) : (term5 A K) = (@iterato A K).
Proof. exact (SYM (@lem6401235 A K h1)). Qed.
Lemma lem6401237 {A K : Type'} (h1 : (term5 A K) = (@iterato A K)) : (term5 A K) = (@iterato A K).
Proof. exact (h1). Qed.
Lemma lem6401238 {A K : Type'} (h1 : (term5 A K) = (@iterato A K)) : (@iterato A K) = (term5 A K).
Proof. exact (SYM (@lem6401237 A K h1)). Qed.
Lemma lem6401239 {A K : Type'} : ((@iterato A K) = (term5 A K)) = ((term5 A K) = (@iterato A K)).
Proof. exact (prop_ext (fun h1 : (@iterato A K) = (term5 A K) => @lem6401236 A K h1) (fun h1 : (term5 A K) = (@iterato A K) => @lem6401238 A K h1)). Qed.
Lemma lem6401242 {A K : Type'} : (term5 A K) = (@iterato A K).
Proof. exact (EQ_MP (@lem6401239 A K) (@lem6401229 A K)). Qed.
Lemma lem6401243 {A K : Type'} : (term5 A K) = (@iterato A K).
Proof. exact (@lem6401242 A K). Qed.
Lemma lem6401244 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6401245 {A K : Type'} (dom : A -> Prop) : (term6 A K dom) = (@iterato A K dom).
Proof. exact (MK_COMB (@lem6401243 A K) (@lem6401244 A dom)). Qed.
Lemma lem6401246 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6401247 {A K : Type'} (dom : A -> Prop) (neut : A) : (term7 A K dom neut) = (@iterato A K dom neut).
Proof. exact (MK_COMB (@lem6401245 A K dom) (@lem6401246 A neut)). Qed.
Lemma lem6401248 {A : Type'} (op : type1400 A) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6401249 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : (term8 A K dom neut op) = (@iterato A K dom neut op).
Proof. exact (MK_COMB (@lem6401247 A K dom neut) (@lem6401248 A op)). Qed.
Lemma lem6401250 {K : Type'} (ltle : type1402 K) : ltle = ltle.
Proof. exact (eq_refl ltle). Qed.
Lemma lem6401251 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : (term9 A K dom neut op ltle) = (@iterato A K dom neut op ltle).
Proof. exact (MK_COMB (@lem6401249 A K dom neut op) (@lem6401250 K ltle)). Qed.
Lemma lem6401252 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem6401253 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) : (term10 A K dom neut op ltle k) = (@iterato A K dom neut op ltle k).
Proof. exact (MK_COMB (@lem6401251 A K dom neut op ltle) (@lem6401252 K k)). Qed.
Lemma lem6401254 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6401255 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term11 A K dom neut op ltle k f) = (@iterato A K dom neut op ltle k f).
Proof. exact (MK_COMB (@lem6401253 A K dom neut op ltle k) (@lem6401254 A K f)). Qed.
Lemma lem6401256 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6401257 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term12 A K dom neut op ltle k f) = (term13 A K dom neut op ltle k f).
Proof. exact (MK_COMB (@lem6401256 A) (@lem6401255 A K dom neut op ltle k f)). Qed.
Lemma lem6401259 {A K : Type'} : (term5 A K) = (@iterato A K).
Proof. exact (EQ_MP (@lem6401239 A K) (@lem6401229 A K)). Qed.
Lemma lem6401260 {A K : Type'} : (term5 A K) = (@iterato A K).
Proof. exact (@lem6401259 A K). Qed.
Lemma lem6401261 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6401262 {A K : Type'} (dom : A -> Prop) : (term6 A K dom) = (@iterato A K dom).
Proof. exact (MK_COMB (@lem6401260 A K) (@lem6401261 A dom)). Qed.
Lemma lem6401263 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6401264 {A K : Type'} (dom : A -> Prop) (neut : A) : (term7 A K dom neut) = (@iterato A K dom neut).
Proof. exact (MK_COMB (@lem6401262 A K dom) (@lem6401263 A neut)). Qed.
Lemma lem6401265 {A : Type'} (op : type1400 A) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6401266 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : (term8 A K dom neut op) = (@iterato A K dom neut op).
Proof. exact (MK_COMB (@lem6401264 A K dom neut) (@lem6401265 A op)). Qed.
Lemma lem6401267 {K : Type'} (ltle : type1402 K) : ltle = ltle.
Proof. exact (eq_refl ltle). Qed.
Lemma lem6401268 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : (term9 A K dom neut op ltle) = (@iterato A K dom neut op ltle).
Proof. exact (MK_COMB (@lem6401266 A K dom neut op) (@lem6401267 K ltle)). Qed.
Lemma lem6401269 {A K : Type'} (k : K -> Prop) (i : K) (f : K -> A) (dom : A -> Prop) (neut : A) : (term14 A K k i f dom neut) = (term14 A K k i f dom neut).
Proof. exact (eq_refl (term14 A K k i f dom neut)). Qed.
Lemma lem6401270 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) (dom : A -> Prop) (neut : A) : (term15 A K op ltle k i f dom neut) = (term16 A K op ltle k i f dom neut).
Proof. exact (MK_COMB (@lem6401268 A K dom neut op ltle) (@lem6401269 A K k i f dom neut)). Qed.
Lemma lem6401271 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6401272 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term17 A K op ltle k i dom neut f) = (term18 A K op ltle k i dom neut f).
Proof. exact (MK_COMB (@lem6401270 A K op ltle k i f dom neut) (@lem6401271 A K f)). Qed.
Lemma lem6401273 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) : (term19 A K op f i) = (term19 A K op f i).
Proof. exact (eq_refl (term19 A K op f i)). Qed.
Lemma lem6401274 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term20 A K op ltle k i dom neut f) = (term21 A K op ltle k i dom neut f).
Proof. exact (MK_COMB (@lem6401273 A K op f i) (@lem6401272 A K op ltle k i dom neut f)). Qed.
Lemma lem6401275 {A : Type'} : (@LET_END A) = (@LET_END A).
Proof. exact (eq_refl (@LET_END A)). Qed.
Lemma lem6401276 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term22 A K op ltle k i dom neut f) = (term23 A K op ltle k i dom neut f).
Proof. exact (MK_COMB (@lem6401275 A) (@lem6401274 A K op ltle k i dom neut f)). Qed.
Lemma lem6401277 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (term24 A K op ltle k dom neut f) = (term25 A K op ltle k dom neut f).
Proof. exact (fun_ext (fun i : K => @lem6401276 A K op ltle k i dom neut f)). Qed.
Lemma lem6401278 {A K : Type'} : (@LET K A) = (@LET K A).
Proof. exact (eq_refl (@LET K A)). Qed.
Lemma lem6401279 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (term26 A K op ltle k dom neut f) = (term27 A K op ltle k dom neut f).
Proof. exact (MK_COMB (@lem6401278 A K) (@lem6401277 A K op ltle k dom neut f)). Qed.
Lemma lem6401280 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term28 A K ltle k f dom neut) = (term28 A K ltle k f dom neut).
Proof. exact (eq_refl (term28 A K ltle k f dom neut)). Qed.
Lemma lem6401281 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term29 A K op ltle k f dom neut) = (term30 A K op ltle k f dom neut).
Proof. exact (MK_COMB (@lem6401279 A K op ltle k dom neut f) (@lem6401280 A K ltle k f dom neut)). Qed.
Lemma lem6401282 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term31 A K k f dom neut) = (term31 A K k f dom neut).
Proof. exact (eq_refl (term31 A K k f dom neut)). Qed.
Lemma lem6401283 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term32 A K op ltle k f dom neut) = (term33 A K op ltle k f dom neut).
Proof. exact (MK_COMB (@lem6401282 A K k f dom neut) (@lem6401281 A K op ltle k f dom neut)). Qed.
Lemma lem6401284 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6401285 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term34 A K op ltle k f dom neut) = (term35 A K op ltle k f dom neut).
Proof. exact (MK_COMB (@lem6401283 A K op ltle k f dom neut) (@lem6401284 A neut)). Qed.
Lemma lem6401286 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((term11 A K dom neut op ltle k f) = (term34 A K op ltle k f dom neut)) = ((@iterato A K dom neut op ltle k f) = (term35 A K op ltle k f dom neut)).
Proof. exact (MK_COMB (@lem6401257 A K dom neut op ltle k f) (@lem6401285 A K op ltle k f dom neut)). Qed.
Lemma lem6401287 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : (term36 A K op ltle k dom neut) = (term37 A K op ltle k dom neut).
Proof. exact (fun_ext (fun f : K -> A => @lem6401286 A K op ltle k f dom neut)). Qed.
Lemma lem6401288 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6401289 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : (term38 A K op ltle k dom neut) = (term39 A K op ltle k dom neut).
Proof. exact (MK_COMB (@lem6401288 A K) (@lem6401287 A K op ltle k dom neut)). Qed.
Lemma lem6401290 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : (term40 A K op ltle dom neut) = (term41 A K op ltle dom neut).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6401289 A K op ltle k dom neut)). Qed.
Lemma lem6401291 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6401292 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : (term42 A K op ltle dom neut) = (term43 A K op ltle dom neut).
Proof. exact (MK_COMB (@lem6401291 K) (@lem6401290 A K op ltle dom neut)). Qed.
Lemma lem6401293 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : (term44 A K op dom neut) = (term45 A K op dom neut).
Proof. exact (fun_ext (fun ltle : type1402 K => @lem6401292 A K op ltle dom neut)). Qed.
Lemma lem6401294 {K : Type'} : (@all (K -> K -> Prop)) = (@all (K -> K -> Prop)).
Proof. exact (eq_refl (@all (K -> K -> Prop))). Qed.
Lemma lem6401295 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : (term46 A K op dom neut) = (term47 A K op dom neut).
Proof. exact (MK_COMB (@lem6401294 K) (@lem6401293 A K op dom neut)). Qed.
Lemma lem6401296 {A K : Type'} (dom : A -> Prop) (neut : A) : (term48 A K dom neut) = (term49 A K dom neut).
Proof. exact (fun_ext (fun op : type1400 A => @lem6401295 A K op dom neut)). Qed.
Lemma lem6401297 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem6401298 {A K : Type'} (dom : A -> Prop) (neut : A) : (term50 A K dom neut) = (term51 A K dom neut).
Proof. exact (MK_COMB (@lem6401297 A) (@lem6401296 A K dom neut)). Qed.
Lemma lem6401299 {A K : Type'} (dom : A -> Prop) : (term52 A K dom) = (term53 A K dom).
Proof. exact (fun_ext (fun neut : A => @lem6401298 A K dom neut)). Qed.
Lemma lem6401300 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6401301 {A K : Type'} (dom : A -> Prop) : (term54 A K dom) = (term55 A K dom).
Proof. exact (MK_COMB (@lem6401300 A) (@lem6401299 A K dom)). Qed.
Lemma lem6401302 {A K : Type'} : (term56 A K) = (term57 A K).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6401301 A K dom)). Qed.
Lemma lem6401303 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6401304 {A K : Type'} : (term4 A K) = (term58 A K).
Proof. exact (MK_COMB (@lem6401303 A) (@lem6401302 A K)). Qed.
Lemma lem6401305 {A K : Type'} : term58 A K.
Proof. exact (EQ_MP (@lem6401304 A K) (@lem6401234 A K)). Qed.
