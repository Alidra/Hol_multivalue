Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERS_IN_CHAIN_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_INDUCT_spec.
Require Import FORALL_AND_THM_spec.
Require Import FORALL_IN_INSERT_spec.
Require Import INTER_UNIV_spec.
Require Import IN_INSERT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_INSERT_EMPTY_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3354637_spec.
Require Import thm3354697_spec.
Require Import thm3356591_spec.
Require Import thm3358011_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem3769000 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3769001 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : (term1 _98313 s t f) = (term2 _98313 s t f).
Proof. exact (@lem3769000 (term1 _98313 s t f)). Qed.
Lemma lem3769002 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : (term2 _98313 s t f) = (term1 _98313 s t f).
Proof. exact (SYM (@lem3769001 _98313 s t f)). Qed.
Lemma lem3769003 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term3 _98313 s t f) : term3 _98313 s t f.
Proof. exact (h1). Qed.
Lemma lem3769006 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term2 _98313 s t f) : term2 _98313 s t f.
Proof. exact (h1). Qed.
Lemma lem3769007 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : term4 _98313 s t f.
Proof. exact (fun h0 : term2 _98313 s t f => @lem3769006 _98313 s t f h0). Qed.
Lemma lem3769008 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term4 _98313 s t f) : term4 _98313 s t f.
Proof. exact (h1). Qed.
Lemma lem3769009 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term2 _98313 s t f) : term2 _98313 s t f.
Proof. exact (h1). Qed.
Lemma lem3769010 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term2 _98313 s t f) (h2 : term4 _98313 s t f) : term2 _98313 s t f.
Proof. exact (@lem3769008 _98313 s t f h2 (@lem3769009 _98313 s t f h1)). Qed.
Lemma lem3769011 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term2 _98313 s t f) : term5 _98313 s t f.
Proof. exact (fun h0 : term4 _98313 s t f => @lem3769010 _98313 s t f h1 h0). Qed.
Lemma lem3769012 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term4 _98313 s t f) : term4 _98313 s t f.
Proof. exact (h1). Qed.
Lemma lem3769013 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term2 _98313 s t f) (h2 : term4 _98313 s t f) : term2 _98313 s t f.
Proof. exact (@lem3769011 _98313 s t f h1 (@lem3769012 _98313 s t f h2)). Qed.
Lemma lem3769014 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term4 _98313 s t f) : term4 _98313 s t f.
Proof. exact (fun h0 : term2 _98313 s t f => @lem3769013 _98313 s t f h0 h1). Qed.
Lemma lem3769015 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : term6 _98313 s t f.
Proof. exact (fun h0 : term4 _98313 s t f => @lem3769014 _98313 s t f h0). Qed.
Lemma lem3769018 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : term4 _98313 s t f.
Proof. exact (@lem3769015 _98313 s t f (@lem3769007 _98313 s t f)). Qed.
Lemma lem3769019 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : term4 _98313 s t f.
Proof. exact (@lem3769018 _98313 s t f). Qed.
Lemma lem3769033 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3769034 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : (term2 _98313 s t f) = (term7 _98313 s t f).
Proof. exact (@lem3769033 (term3 _98313 s t f)). Qed.
Lemma lem3769036 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3769037 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : (term7 _98313 s t f) = (term1 _98313 s t f).
Proof. exact (@lem3769036 (term1 _98313 s t f)). Qed.
Lemma lem3769040 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : (term2 _98313 s t f) = (term1 _98313 s t f).
Proof. exact (TRANS (@lem3769034 _98313 s t f) (@lem3769037 _98313 s t f)). Qed.
Lemma lem3769047 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) : (term9 _98313 t f) = (term10 _98313 t f).
Proof. exact (fun_ext (fun s : _98313 -> Prop => @lem3769040 _98313 s t f)). Qed.
Lemma lem3769048 {_98313 : Type'} : (@all (_98313 -> Prop)) = (@all (_98313 -> Prop)).
Proof. exact (eq_refl (@all (_98313 -> Prop))). Qed.
Lemma lem3769049 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) : (term11 _98313 t f) = (term12 _98313 t f).
Proof. exact (MK_COMB (@lem3769048 _98313) (@lem3769047 _98313 t f)). Qed.
Lemma lem3769054 {_98313 : Type'} (f : type686 _98313) : (term13 _98313 f) = (term14 _98313 f).
Proof. exact (fun_ext (fun t : _98313 -> Prop => @lem3769049 _98313 t f)). Qed.
Lemma lem3769055 {_98313 : Type'} : (@all (_98313 -> Prop)) = (@all (_98313 -> Prop)).
Proof. exact (eq_refl (@all (_98313 -> Prop))). Qed.
Lemma lem3769056 {_98313 : Type'} (f : type686 _98313) : (term15 _98313 f) = (term16 _98313 f).
Proof. exact (MK_COMB (@lem3769055 _98313) (@lem3769054 _98313 f)). Qed.
Lemma lem3769061 {_98313 : Type'} : (term17 _98313) = (term18 _98313).
Proof. exact (fun_ext (fun f : type686 _98313 => @lem3769056 _98313 f)). Qed.
Lemma lem3769062 {_98313 : Type'} : (@all ((_98313 -> Prop) -> Prop)) = (@all ((_98313 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_98313 -> Prop) -> Prop))). Qed.
Lemma lem3769071 {_98313 : Type'} : (term19 _98313) = (term20 _98313).
Proof. exact (MK_COMB (@lem3769062 _98313) (@lem3769061 _98313)). Qed.
Lemma lem3769088 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : (term1 _98313 s t f) = (term1 _98313 s t f).
Proof. exact (eq_refl (term1 _98313 s t f)). Qed.
Lemma lem3769089 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) : (term10 _98313 t f) = (term10 _98313 t f).
Proof. exact (fun_ext (fun s : _98313 -> Prop => @lem3769088 _98313 s t f)). Qed.
Lemma lem3769090 {_98313 : Type'} : (@all (_98313 -> Prop)) = (@all (_98313 -> Prop)).
Proof. exact (eq_refl (@all (_98313 -> Prop))). Qed.
Lemma lem3769091 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) : (term12 _98313 t f) = (term12 _98313 t f).
Proof. exact (MK_COMB (@lem3769090 _98313) (@lem3769089 _98313 t f)). Qed.
Lemma lem3769092 {_98313 : Type'} (f : type686 _98313) : (term14 _98313 f) = (term14 _98313 f).
Proof. exact (fun_ext (fun t : _98313 -> Prop => @lem3769091 _98313 t f)). Qed.
Lemma lem3769093 {_98313 : Type'} : (@all (_98313 -> Prop)) = (@all (_98313 -> Prop)).
Proof. exact (eq_refl (@all (_98313 -> Prop))). Qed.
Lemma lem3769094 {_98313 : Type'} (f : type686 _98313) : (term16 _98313 f) = (term16 _98313 f).
Proof. exact (MK_COMB (@lem3769093 _98313) (@lem3769092 _98313 f)). Qed.
Lemma lem3769095 {_98313 : Type'} : (term18 _98313) = (term18 _98313).
Proof. exact (fun_ext (fun f : type686 _98313 => @lem3769094 _98313 f)). Qed.
Lemma lem3769096 {_98313 : Type'} : (@all ((_98313 -> Prop) -> Prop)) = (@all ((_98313 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_98313 -> Prop) -> Prop))). Qed.
Lemma lem3769097 {_98313 : Type'} : (term20 _98313) = (term20 _98313).
Proof. exact (MK_COMB (@lem3769096 _98313) (@lem3769095 _98313)). Qed.
Lemma lem3769126 {_98313 : Type'} : (term19 _98313) = (term20 _98313).
Proof. exact (TRANS (@lem3769071 _98313) (@lem3769097 _98313)). Qed.
Lemma lem3769127 {_98313 : Type'} : (term20 _98313) = (term19 _98313).
Proof. exact (SYM (@lem3769126 _98313)). Qed.
Lemma lem3769131 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3769132 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : (term21 _98313 s t f) = (term22 _98313 s t f).
Proof. exact (@lem3769131 (term21 _98313 s t f)). Qed.
Lemma lem3769133 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : (term22 _98313 s t f) = (term21 _98313 s t f).
Proof. exact (SYM (@lem3769132 _98313 s t f)). Qed.
Lemma lem3769134 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) : term23 _98313 s t f.
Proof. exact (h1). Qed.
Lemma lem3769144 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term24 _98313 s t) : term24 _98313 s t.
Proof. exact (h1). Qed.
Lemma lem3769150 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) (h1 : @IN (_98313 -> Prop) t f) : @IN (_98313 -> Prop) t f.
Proof. exact (h1). Qed.
Lemma lem3769161 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : (term23 _98313 s t f) = (term25 _98313 s t f).
Proof. exact (@lem17160 ((@INTER _98313 s t) = s) (term26 _98313 s t f)). Qed.
Lemma lem3769184 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term24 _98313 s t) : term24 _98313 s t.
Proof. exact (h1). Qed.
Lemma lem3769190 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) (h1 : @IN (_98313 -> Prop) t f) : @IN (_98313 -> Prop) t f.
Proof. exact (h1). Qed.
Lemma lem3769216 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) : term25 _98313 s t f.
Proof. exact (EQ_MP (@lem3769161 _98313 s t f) (@lem3769134 _98313 s t f h1)). Qed.
Lemma lem3769236 {_98313 : Type'} (t : _98313 -> Prop) (s : _98313 -> Prop) (h1 : (@INTER _98313 s t) = s) : (@INTER _98313 s t) = s.
Proof. exact (h1). Qed.
Lemma lem3769240 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) (h1 : @IN (_98313 -> Prop) t f) : @IN (_98313 -> Prop) t f.
Proof. exact (h1). Qed.
Lemma lem3769252 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : (@INTER _98313 s t) = t) : (@INTER _98313 s t) = t.
Proof. exact (h1). Qed.
Lemma lem3769256 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) : term27 _98313 t s.
Proof. exact (proj1 (@lem3769216 _98313 s t f h1)). Qed.
Lemma lem3769260 {_98313 : Type'} (t : _98313 -> Prop) (s : _98313 -> Prop) (h1 : (@INTER _98313 s t) = s) : (@INTER _98313 s t) = s.
Proof. exact (h1). Qed.
Lemma lem3769262 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) (h1 : @IN (_98313 -> Prop) t f) : @IN (_98313 -> Prop) t f.
Proof. exact (h1). Qed.
Lemma lem3769266 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) : term28 _98313 s t f.
Proof. exact (proj2 (@lem3769216 _98313 s t f h1)). Qed.
Lemma lem3769268 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : (@INTER _98313 s t) = t) : (@INTER _98313 s t) = t.
Proof. exact (h1). Qed.
Lemma lem3769308 {_98313 : Type'} (t : _98313 -> Prop) (s : _98313 -> Prop) (h1 : (@INTER _98313 s t) = s) : (@INTER _98313 s t) = s.
Proof. exact (h1). Qed.
Lemma lem3769309 {_98313 : Type'} (t : _98313 -> Prop) (s : _98313 -> Prop) (h1 : (@INTER _98313 s t) = s) : term29 _98313 t s.
Proof. exact (fun h0 : term27 _98313 t s => @lem3769308 _98313 t s h1). Qed.
Lemma lem3769311 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3769312 {_98313 : Type'} (t : _98313 -> Prop) (s : _98313 -> Prop) : (term29 _98313 t s) = ((@INTER _98313 s t) = s).
Proof. exact (@lem3769311 ((@INTER _98313 s t) = s)). Qed.
Lemma lem3769313 {_98313 : Type'} (t : _98313 -> Prop) (s : _98313 -> Prop) (h1 : (@INTER _98313 s t) = s) : (@INTER _98313 s t) = s.
Proof. exact (EQ_MP (@lem3769312 _98313 t s) (@lem3769309 _98313 t s h1)). Qed.
Lemma lem3769316 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3769318 {_98313 : Type'} (t : _98313 -> Prop) (s : _98313 -> Prop) : (term27 _98313 t s) = (term31 _98313 t s).
Proof. exact (@lem3769316 ((@INTER _98313 s t) = s)). Qed.
Lemma lem3769321 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) : term31 _98313 t s.
Proof. exact (EQ_MP (@lem3769318 _98313 t s) (@lem3769256 _98313 s t f h1)). Qed.
Lemma lem3769324 {_98313 : Type'} (f : type686 _98313) (t : _98313 -> Prop) (s : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = s) : False.
Proof. exact (@lem3769321 _98313 s t f h1 (@lem3769313 _98313 t s h2)). Qed.
Lemma lem3769325 {_98313 : Type'} (f : type686 _98313) (t : _98313 -> Prop) (s : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = s) : term32.
Proof. exact (fun h0 : ~ False => @lem3769324 _98313 f t s h1 h2). Qed.
Lemma lem3769327 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3769328 : term32 = False.
Proof. exact (@lem3769327 False). Qed.
Lemma lem3769329 {_98313 : Type'} (f : type686 _98313) (t : _98313 -> Prop) (s : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = s) : False.
Proof. exact (EQ_MP (@lem3769328) (@lem3769325 _98313 f t s h1 h2)). Qed.
Lemma lem3769330 {_98313 : Type'} : (@IN (_98313 -> Prop)) = (@IN (_98313 -> Prop)).
Proof. exact (eq_refl (@IN (_98313 -> Prop))). Qed.
Lemma lem3769331 {_98313 : Type'} (_43333 : _98313 -> Prop) (_43335 : _98313 -> Prop) (h1 : _43333 = _43335) : _43333 = _43335.
Proof. exact (h1). Qed.
Lemma lem3769332 {_98313 : Type'} (_43334 : type686 _98313) (_43336 : type686 _98313) (h1 : _43334 = _43336) : _43334 = _43336.
Proof. exact (h1). Qed.
Lemma lem3769333 {_98313 : Type'} (_43333 : _98313 -> Prop) (_43335 : _98313 -> Prop) (h1 : _43333 = _43335) : (@IN (_98313 -> Prop) _43333) = (@IN (_98313 -> Prop) _43335).
Proof. exact (MK_COMB (@lem3769330 _98313) (@lem3769331 _98313 _43333 _43335 h1)). Qed.
Lemma lem3769334 {_98313 : Type'} (_43333 : _98313 -> Prop) (_43335 : _98313 -> Prop) (_43334 : type686 _98313) (_43336 : type686 _98313) (h1 : _43333 = _43335) (h2 : _43334 = _43336) : (@IN (_98313 -> Prop) _43333 _43334) = (@IN (_98313 -> Prop) _43335 _43336).
Proof. exact (MK_COMB (@lem3769333 _98313 _43333 _43335 h1) (@lem3769332 _98313 _43334 _43336 h2)). Qed.
Lemma lem3769336 (b : Prop) (a : Prop) : term33 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3769337 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : term34 _98313 _43335 _43336 _43333 _43334.
Proof. exact (@lem3769336 (@IN (_98313 -> Prop) _43335 _43336) (@IN (_98313 -> Prop) _43333 _43334)). Qed.
Lemma lem3769338 {_98313 : Type'} (_43333 : _98313 -> Prop) (_43335 : _98313 -> Prop) (_43334 : type686 _98313) (_43336 : type686 _98313) (h1 : _43333 = _43335) (h2 : _43334 = _43336) : term35 _98313 _43335 _43336 _43333 _43334.
Proof. exact (@lem3769337 _98313 _43335 _43336 _43333 _43334 (@lem3769334 _98313 _43333 _43335 _43334 _43336 h1 h2)). Qed.
Lemma lem3769339 {_98313 : Type'} (_43336 : type686 _98313) (_43334 : type686 _98313) (_43333 : _98313 -> Prop) (_43335 : _98313 -> Prop) (h1 : _43333 = _43335) : term36 _98313 _43335 _43336 _43333 _43334.
Proof. exact (fun h0 : _43334 = _43336 => @lem3769338 _98313 _43333 _43335 _43334 _43336 h1 h0). Qed.
Lemma lem3769341 (a : Prop) (b : Prop) : (a -> b) = (term37 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3769342 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term36 _98313 _43335 _43336 _43333 _43334) = (term38 _98313 _43335 _43336 _43333 _43334).
Proof. exact (@lem3769341 (_43334 = _43336) (term35 _98313 _43335 _43336 _43333 _43334)). Qed.
Lemma lem3769343 {_98313 : Type'} (_43336 : type686 _98313) (_43334 : type686 _98313) (_43333 : _98313 -> Prop) (_43335 : _98313 -> Prop) (h1 : _43333 = _43335) : term38 _98313 _43335 _43336 _43333 _43334.
Proof. exact (EQ_MP (@lem3769342 _98313 _43335 _43336 _43333 _43334) (@lem3769339 _98313 _43336 _43334 _43333 _43335 h1)). Qed.
Lemma lem3769344 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : term39 _98313 _43335 _43336 _43333 _43334.
Proof. exact (fun h0 : _43333 = _43335 => @lem3769343 _98313 _43336 _43334 _43333 _43335 h0). Qed.
Lemma lem3769346 (a : Prop) (b : Prop) : (a -> b) = (term37 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3769347 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term39 _98313 _43335 _43336 _43333 _43334) = (term40 _98313 _43335 _43336 _43333 _43334).
Proof. exact (@lem3769346 (_43333 = _43335) (term38 _98313 _43335 _43336 _43333 _43334)). Qed.
Lemma lem3769348 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : term40 _98313 _43335 _43336 _43333 _43334.
Proof. exact (EQ_MP (@lem3769347 _98313 _43335 _43336 _43333 _43334) (@lem3769344 _98313 _43335 _43336 _43333 _43334)). Qed.
Lemma lem3769365 {_98313 : Type'} (x : _98313 -> Prop) (y : _98313 -> Prop) (z : _98313 -> Prop) : term41 _98313 x y z.
Proof. exact (@lem21385 (_98313 -> Prop) x y z). Qed.
Lemma lem3769369 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : (@INTER _98313 s t) = t) : (@INTER _98313 s t) = t.
Proof. exact (h1). Qed.
Lemma lem3769370 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : (@INTER _98313 s t) = t) : term42 _98313 s t.
Proof. exact (fun h0 : term43 _98313 s t => @lem3769369 _98313 s t h1). Qed.
Lemma lem3769372 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3769373 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) : (term42 _98313 s t) = ((@INTER _98313 s t) = t).
Proof. exact (@lem3769372 ((@INTER _98313 s t) = t)). Qed.
Lemma lem3769374 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : (@INTER _98313 s t) = t) : (@INTER _98313 s t) = t.
Proof. exact (EQ_MP (@lem3769373 _98313 s t) (@lem3769370 _98313 s t h1)). Qed.
Lemma lem3769376 {_98313 : Type'} (x : _98313 -> Prop) : x = x.
Proof. exact (@lem21386 (_98313 -> Prop) x). Qed.
Lemma lem3769377 {_98313 : Type'} (x : _98313 -> Prop) : x = x.
Proof. exact (@lem3769376 _98313 x). Qed.
Lemma lem3769378 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) : (@INTER _98313 s t) = (@INTER _98313 s t).
Proof. exact (@lem3769377 _98313 (@INTER _98313 s t)). Qed.
Lemma lem3769379 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) : term44 _98313 s t.
Proof. exact (fun h0 : term45 _98313 s t => @lem3769378 _98313 s t). Qed.
Lemma lem3769381 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3769382 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) : (term44 _98313 s t) = ((@INTER _98313 s t) = (@INTER _98313 s t)).
Proof. exact (@lem3769381 ((@INTER _98313 s t) = (@INTER _98313 s t))). Qed.
Lemma lem3769383 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) : (@INTER _98313 s t) = (@INTER _98313 s t).
Proof. exact (EQ_MP (@lem3769382 _98313 s t) (@lem3769379 _98313 s t)). Qed.
Lemma lem3769401 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3769402 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : (term46 _98313 x y z) = (term47 _98313 y x z).
Proof. exact (@lem3769401 (y = z) (term48 _98313 x z)). Qed.
Lemma lem3769412 {_98313 : Type'} (x : _98313 -> Prop) (y : _98313 -> Prop) : (term49 _98313 x y) = (term49 _98313 x y).
Proof. exact (eq_refl (term49 _98313 x y)). Qed.
Lemma lem3769413 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : (term41 _98313 x y z) = (term50 _98313 y x z).
Proof. exact (MK_COMB (@lem3769412 _98313 x y) (@lem3769402 _98313 y x z)). Qed.
Lemma lem3769417 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3769418 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : (term50 _98313 y x z) = (term52 _98313 y x z).
Proof. exact (@lem3769417 (y = z) (term48 _98313 x y) (term48 _98313 x z)). Qed.
Lemma lem3769440 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : (term41 _98313 x y z) = (term52 _98313 y x z).
Proof. exact (TRANS (@lem3769413 _98313 y x z) (@lem3769418 _98313 y x z)). Qed.
Lemma lem3769441 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3769442 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : (term53 _98313 x y z) = (term54 _98313 y x z).
Proof. exact (MK_COMB (@lem3769441) (@lem3769440 _98313 y x z)). Qed.
Lemma lem3769464 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : (term52 _98313 y x z) = (term52 _98313 y x z).
Proof. exact (eq_refl (term52 _98313 y x z)). Qed.
Lemma lem3769465 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : ((term41 _98313 x y z) = (term52 _98313 y x z)) = ((term52 _98313 y x z) = (term52 _98313 y x z)).
Proof. exact (MK_COMB (@lem3769442 _98313 y x z) (@lem3769464 _98313 y x z)). Qed.
Lemma lem3769467 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3769468 (x : Prop) : (x = x) = True.
Proof. exact (@lem3769467 Prop x). Qed.
Lemma lem3769469 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : ((term52 _98313 y x z) = (term52 _98313 y x z)) = True.
Proof. exact (@lem3769468 (term52 _98313 y x z)). Qed.
Lemma lem3769470 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : ((term41 _98313 x y z) = (term52 _98313 y x z)) = True.
Proof. exact (TRANS (@lem3769465 _98313 y x z) (@lem3769469 _98313 y x z)). Qed.
Lemma lem3769471 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : True = ((term41 _98313 x y z) = (term52 _98313 y x z)).
Proof. exact (SYM (@lem3769470 _98313 y x z)). Qed.
Lemma lem3769472 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : (term41 _98313 x y z) = (term52 _98313 y x z).
Proof. exact (EQ_MP (@lem3769471 _98313 y x z) (@lem0)). Qed.
Lemma lem3769473 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : term52 _98313 y x z.
Proof. exact (EQ_MP (@lem3769472 _98313 y x z) (@lem3769365 _98313 x y z)). Qed.
Lemma lem3769475 (b : Prop) (a : Prop) : (a \/ b) = (term55 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3769476 {_98313 : Type'} (x : _98313 -> Prop) (y : _98313 -> Prop) (z : _98313 -> Prop) : (term52 _98313 y x z) = (term56 _98313 x y z).
Proof. exact (@lem3769475 (term57 _98313 y x z) (y = z)). Qed.
Lemma lem3769478 (a : Prop) (b : Prop) : (term58 a b) = (term59 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3769479 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : (term60 _98313 y x z) = (term61 _98313 y x z).
Proof. exact (@lem3769478 (term48 _98313 x y) (term48 _98313 x z)). Qed.
Lemma lem3769481 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3769482 {_98313 : Type'} (x : _98313 -> Prop) (y : _98313 -> Prop) : (term62 _98313 x y) = (x = y).
Proof. exact (@lem3769481 (x = y)). Qed.
Lemma lem3769483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3769484 {_98313 : Type'} (x : _98313 -> Prop) (y : _98313 -> Prop) : (term63 _98313 x y) = (term64 _98313 x y).
Proof. exact (MK_COMB (@lem3769483) (@lem3769482 _98313 x y)). Qed.
Lemma lem3769486 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3769487 {_98313 : Type'} (x : _98313 -> Prop) (z : _98313 -> Prop) : (term62 _98313 x z) = (x = z).
Proof. exact (@lem3769486 (x = z)). Qed.
Lemma lem3769488 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : (term61 _98313 y x z) = (term65 _98313 y x z).
Proof. exact (MK_COMB (@lem3769484 _98313 x y) (@lem3769487 _98313 x z)). Qed.
Lemma lem3769489 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : (term60 _98313 y x z) = (term65 _98313 y x z).
Proof. exact (TRANS (@lem3769479 _98313 y x z) (@lem3769488 _98313 y x z)). Qed.
Lemma lem3769490 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3769491 {_98313 : Type'} (y : _98313 -> Prop) (x : _98313 -> Prop) (z : _98313 -> Prop) : (term66 _98313 y x z) = (term67 _98313 y x z).
Proof. exact (MK_COMB (@lem3769490) (@lem3769489 _98313 y x z)). Qed.
Lemma lem3769492 {_98313 : Type'} (y : _98313 -> Prop) (z : _98313 -> Prop) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3769493 {_98313 : Type'} (x : _98313 -> Prop) (y : _98313 -> Prop) (z : _98313 -> Prop) : (term56 _98313 x y z) = (term68 _98313 x y z).
Proof. exact (MK_COMB (@lem3769491 _98313 y x z) (@lem3769492 _98313 y z)). Qed.
Lemma lem3769494 {_98313 : Type'} (x : _98313 -> Prop) (y : _98313 -> Prop) (z : _98313 -> Prop) : (term52 _98313 y x z) = (term68 _98313 x y z).
Proof. exact (TRANS (@lem3769476 _98313 x y z) (@lem3769493 _98313 x y z)). Qed.
Lemma lem3769496 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : (@INTER _98313 s t) = t) : term69 _98313 s t.
Proof. exact (conj (@lem3769374 _98313 s t h1) (@lem3769383 _98313 s t)). Qed.
Lemma lem3769498 {_98313 : Type'} (x : _98313 -> Prop) (y : _98313 -> Prop) (z : _98313 -> Prop) : term68 _98313 x y z.
Proof. exact (EQ_MP (@lem3769494 _98313 x y z) (@lem3769473 _98313 y x z)). Qed.
Lemma lem3769499 {_98313 : Type'} (x : _98313 -> Prop) (y : _98313 -> Prop) (z : _98313 -> Prop) : term68 _98313 x y z.
Proof. exact (@lem3769498 _98313 x y z). Qed.
Lemma lem3769500 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) : term70 _98313 s t.
Proof. exact (@lem3769499 _98313 (@INTER _98313 s t) t (@INTER _98313 s t)). Qed.
Lemma lem3769503 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : (@INTER _98313 s t) = t) : t = (@INTER _98313 s t).
Proof. exact (@lem3769500 _98313 s t (@lem3769496 _98313 s t h1)). Qed.
Lemma lem3769504 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : (@INTER _98313 s t) = t) : term71 _98313 s t.
Proof. exact (fun h0 : term72 _98313 s t => @lem3769503 _98313 s t h1). Qed.
Lemma lem3769506 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3769507 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) : (term71 _98313 s t) = (t = (@INTER _98313 s t)).
Proof. exact (@lem3769506 (t = (@INTER _98313 s t))). Qed.
Lemma lem3769508 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : (@INTER _98313 s t) = t) : t = (@INTER _98313 s t).
Proof. exact (EQ_MP (@lem3769507 _98313 s t) (@lem3769504 _98313 s t h1)). Qed.
Lemma lem3769510 {_98313 : Type'} (x : type686 _98313) : x = x.
Proof. exact (@lem21386 (type686 _98313) x). Qed.
Lemma lem3769511 {_98313 : Type'} (x : type686 _98313) : x = x.
Proof. exact (@lem3769510 _98313 x). Qed.
Lemma lem3769512 {_98313 : Type'} (f : type686 _98313) : f = f.
Proof. exact (@lem3769511 _98313 f). Qed.
Lemma lem3769513 {_98313 : Type'} (f : type686 _98313) : term73 _98313 f.
Proof. exact (fun h0 : term74 _98313 f => @lem3769512 _98313 f). Qed.
Lemma lem3769515 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3769516 {_98313 : Type'} (f : type686 _98313) : (term73 _98313 f) = (f = f).
Proof. exact (@lem3769515 (f = f)). Qed.
Lemma lem3769517 {_98313 : Type'} (f : type686 _98313) : f = f.
Proof. exact (EQ_MP (@lem3769516 _98313 f) (@lem3769513 _98313 f)). Qed.
Lemma lem3769519 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) (h1 : @IN (_98313 -> Prop) t f) : @IN (_98313 -> Prop) t f.
Proof. exact (h1). Qed.
Lemma lem3769520 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) (h1 : @IN (_98313 -> Prop) t f) : term75 _98313 t f.
Proof. exact (fun h0 : term76 _98313 t f => @lem3769519 _98313 t f h1). Qed.
Lemma lem3769522 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3769523 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) : (term75 _98313 t f) = (@IN (_98313 -> Prop) t f).
Proof. exact (@lem3769522 (@IN (_98313 -> Prop) t f)). Qed.
Lemma lem3769524 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) (h1 : @IN (_98313 -> Prop) t f) : @IN (_98313 -> Prop) t f.
Proof. exact (EQ_MP (@lem3769523 _98313 t f) (@lem3769520 _98313 t f h1)). Qed.
Lemma lem3769542 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3769543 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term38 _98313 _43335 _43336 _43333 _43334) = (term77 _98313 _43335 _43336 _43333 _43334).
Proof. exact (@lem3769542 (@IN (_98313 -> Prop) _43335 _43336) (term78 _98313 _43334 _43336) (term76 _98313 _43333 _43334)). Qed.
Lemma lem3769561 {_98313 : Type'} (_43333 : _98313 -> Prop) (_43335 : _98313 -> Prop) : (term49 _98313 _43333 _43335) = (term49 _98313 _43333 _43335).
Proof. exact (eq_refl (term49 _98313 _43333 _43335)). Qed.
Lemma lem3769562 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term40 _98313 _43335 _43336 _43333 _43334) = (term79 _98313 _43335 _43336 _43333 _43334).
Proof. exact (MK_COMB (@lem3769561 _98313 _43333 _43335) (@lem3769543 _98313 _43335 _43336 _43333 _43334)). Qed.
Lemma lem3769566 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3769567 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term79 _98313 _43335 _43336 _43333 _43334) = (term80 _98313 _43335 _43336 _43333 _43334).
Proof. exact (@lem3769566 (@IN (_98313 -> Prop) _43335 _43336) (term48 _98313 _43333 _43335) (term81 _98313 _43336 _43333 _43334)). Qed.
Lemma lem3769597 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term40 _98313 _43335 _43336 _43333 _43334) = (term80 _98313 _43335 _43336 _43333 _43334).
Proof. exact (TRANS (@lem3769562 _98313 _43335 _43336 _43333 _43334) (@lem3769567 _98313 _43335 _43336 _43333 _43334)). Qed.
Lemma lem3769598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3769599 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term82 _98313 _43335 _43336 _43333 _43334) = (term83 _98313 _43335 _43336 _43333 _43334).
Proof. exact (MK_COMB (@lem3769598) (@lem3769597 _98313 _43335 _43336 _43333 _43334)). Qed.
Lemma lem3769629 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term80 _98313 _43335 _43336 _43333 _43334) = (term80 _98313 _43335 _43336 _43333 _43334).
Proof. exact (eq_refl (term80 _98313 _43335 _43336 _43333 _43334)). Qed.
Lemma lem3769630 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : ((term40 _98313 _43335 _43336 _43333 _43334) = (term80 _98313 _43335 _43336 _43333 _43334)) = ((term80 _98313 _43335 _43336 _43333 _43334) = (term80 _98313 _43335 _43336 _43333 _43334)).
Proof. exact (MK_COMB (@lem3769599 _98313 _43335 _43336 _43333 _43334) (@lem3769629 _98313 _43335 _43336 _43333 _43334)). Qed.
Lemma lem3769632 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3769633 (x : Prop) : (x = x) = True.
Proof. exact (@lem3769632 Prop x). Qed.
Lemma lem3769634 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : ((term80 _98313 _43335 _43336 _43333 _43334) = (term80 _98313 _43335 _43336 _43333 _43334)) = True.
Proof. exact (@lem3769633 (term80 _98313 _43335 _43336 _43333 _43334)). Qed.
Lemma lem3769635 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : ((term40 _98313 _43335 _43336 _43333 _43334) = (term80 _98313 _43335 _43336 _43333 _43334)) = True.
Proof. exact (TRANS (@lem3769630 _98313 _43335 _43336 _43333 _43334) (@lem3769634 _98313 _43335 _43336 _43333 _43334)). Qed.
Lemma lem3769636 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : True = ((term40 _98313 _43335 _43336 _43333 _43334) = (term80 _98313 _43335 _43336 _43333 _43334)).
Proof. exact (SYM (@lem3769635 _98313 _43335 _43336 _43333 _43334)). Qed.
Lemma lem3769637 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term40 _98313 _43335 _43336 _43333 _43334) = (term80 _98313 _43335 _43336 _43333 _43334).
Proof. exact (EQ_MP (@lem3769636 _98313 _43335 _43336 _43333 _43334) (@lem0)). Qed.
Lemma lem3769638 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : term80 _98313 _43335 _43336 _43333 _43334.
Proof. exact (EQ_MP (@lem3769637 _98313 _43335 _43336 _43333 _43334) (@lem3769348 _98313 _43335 _43336 _43333 _43334)). Qed.
Lemma lem3769640 (b : Prop) (a : Prop) : (a \/ b) = (term55 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3769641 {_98313 : Type'} (_43333 : _98313 -> Prop) (_43334 : type686 _98313) (_43335 : _98313 -> Prop) (_43336 : type686 _98313) : (term80 _98313 _43335 _43336 _43333 _43334) = (term84 _98313 _43333 _43334 _43335 _43336).
Proof. exact (@lem3769640 (term85 _98313 _43335 _43336 _43333 _43334) (@IN (_98313 -> Prop) _43335 _43336)). Qed.
Lemma lem3769643 (a : Prop) (b : Prop) : (term58 a b) = (term59 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3769644 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term86 _98313 _43335 _43336 _43333 _43334) = (term87 _98313 _43335 _43336 _43333 _43334).
Proof. exact (@lem3769643 (term48 _98313 _43333 _43335) (term81 _98313 _43336 _43333 _43334)). Qed.
Lemma lem3769646 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3769647 {_98313 : Type'} (_43333 : _98313 -> Prop) (_43335 : _98313 -> Prop) : (term62 _98313 _43333 _43335) = (_43333 = _43335).
Proof. exact (@lem3769646 (_43333 = _43335)). Qed.
Lemma lem3769648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3769649 {_98313 : Type'} (_43333 : _98313 -> Prop) (_43335 : _98313 -> Prop) : (term63 _98313 _43333 _43335) = (term64 _98313 _43333 _43335).
Proof. exact (MK_COMB (@lem3769648) (@lem3769647 _98313 _43333 _43335)). Qed.
Lemma lem3769651 (a : Prop) (b : Prop) : (term58 a b) = (term59 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3769652 {_98313 : Type'} (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term88 _98313 _43336 _43333 _43334) = (term89 _98313 _43336 _43333 _43334).
Proof. exact (@lem3769651 (term78 _98313 _43334 _43336) (term76 _98313 _43333 _43334)). Qed.
Lemma lem3769654 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3769655 {_98313 : Type'} (_43334 : type686 _98313) (_43336 : type686 _98313) : (term90 _98313 _43334 _43336) = (_43334 = _43336).
Proof. exact (@lem3769654 (_43334 = _43336)). Qed.
Lemma lem3769656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3769657 {_98313 : Type'} (_43334 : type686 _98313) (_43336 : type686 _98313) : (term91 _98313 _43334 _43336) = (term92 _98313 _43334 _43336).
Proof. exact (MK_COMB (@lem3769656) (@lem3769655 _98313 _43334 _43336)). Qed.
Lemma lem3769659 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3769660 {_98313 : Type'} (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term93 _98313 _43333 _43334) = (@IN (_98313 -> Prop) _43333 _43334).
Proof. exact (@lem3769659 (@IN (_98313 -> Prop) _43333 _43334)). Qed.
Lemma lem3769661 {_98313 : Type'} (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term89 _98313 _43336 _43333 _43334) = (term94 _98313 _43336 _43333 _43334).
Proof. exact (MK_COMB (@lem3769657 _98313 _43334 _43336) (@lem3769660 _98313 _43333 _43334)). Qed.
Lemma lem3769662 {_98313 : Type'} (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term88 _98313 _43336 _43333 _43334) = (term94 _98313 _43336 _43333 _43334).
Proof. exact (TRANS (@lem3769652 _98313 _43336 _43333 _43334) (@lem3769661 _98313 _43336 _43333 _43334)). Qed.
Lemma lem3769663 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term87 _98313 _43335 _43336 _43333 _43334) = (term95 _98313 _43335 _43336 _43333 _43334).
Proof. exact (MK_COMB (@lem3769649 _98313 _43333 _43335) (@lem3769662 _98313 _43336 _43333 _43334)). Qed.
Lemma lem3769664 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term86 _98313 _43335 _43336 _43333 _43334) = (term95 _98313 _43335 _43336 _43333 _43334).
Proof. exact (TRANS (@lem3769644 _98313 _43335 _43336 _43333 _43334) (@lem3769663 _98313 _43335 _43336 _43333 _43334)). Qed.
Lemma lem3769665 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3769666 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) (_43333 : _98313 -> Prop) (_43334 : type686 _98313) : (term96 _98313 _43335 _43336 _43333 _43334) = (term97 _98313 _43335 _43336 _43333 _43334).
Proof. exact (MK_COMB (@lem3769665) (@lem3769664 _98313 _43335 _43336 _43333 _43334)). Qed.
Lemma lem3769667 {_98313 : Type'} (_43335 : _98313 -> Prop) (_43336 : type686 _98313) : (@IN (_98313 -> Prop) _43335 _43336) = (@IN (_98313 -> Prop) _43335 _43336).
Proof. exact (eq_refl (@IN (_98313 -> Prop) _43335 _43336)). Qed.
Lemma lem3769668 {_98313 : Type'} (_43333 : _98313 -> Prop) (_43334 : type686 _98313) (_43335 : _98313 -> Prop) (_43336 : type686 _98313) : (term84 _98313 _43333 _43334 _43335 _43336) = (term98 _98313 _43333 _43334 _43335 _43336).
Proof. exact (MK_COMB (@lem3769666 _98313 _43335 _43336 _43333 _43334) (@lem3769667 _98313 _43335 _43336)). Qed.
Lemma lem3769669 {_98313 : Type'} (_43333 : _98313 -> Prop) (_43334 : type686 _98313) (_43335 : _98313 -> Prop) (_43336 : type686 _98313) : (term80 _98313 _43335 _43336 _43333 _43334) = (term98 _98313 _43333 _43334 _43335 _43336).
Proof. exact (TRANS (@lem3769641 _98313 _43333 _43334 _43335 _43336) (@lem3769668 _98313 _43333 _43334 _43335 _43336)). Qed.
Lemma lem3769671 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) (h1 : @IN (_98313 -> Prop) t f) : term99 _98313 t f.
Proof. exact (conj (@lem3769517 _98313 f) (@lem3769524 _98313 t f h1)). Qed.
Lemma lem3769672 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : (@INTER _98313 s t) = t) (h2 : @IN (_98313 -> Prop) t f) : term100 _98313 s t f.
Proof. exact (conj (@lem3769508 _98313 s t h1) (@lem3769671 _98313 t f h2)). Qed.
Lemma lem3769674 {_98313 : Type'} (_43333 : _98313 -> Prop) (_43334 : type686 _98313) (_43335 : _98313 -> Prop) (_43336 : type686 _98313) : term98 _98313 _43333 _43334 _43335 _43336.
Proof. exact (EQ_MP (@lem3769669 _98313 _43333 _43334 _43335 _43336) (@lem3769638 _98313 _43335 _43336 _43333 _43334)). Qed.
Lemma lem3769675 {_98313 : Type'} (_43333 : _98313 -> Prop) (_43334 : type686 _98313) (_43335 : _98313 -> Prop) (_43336 : type686 _98313) : term98 _98313 _43333 _43334 _43335 _43336.
Proof. exact (@lem3769674 _98313 _43333 _43334 _43335 _43336). Qed.
Lemma lem3769676 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : term101 _98313 s t f.
Proof. exact (@lem3769675 _98313 t f (@INTER _98313 s t) f). Qed.
Lemma lem3769679 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : (@INTER _98313 s t) = t) (h2 : @IN (_98313 -> Prop) t f) : term26 _98313 s t f.
Proof. exact (@lem3769676 _98313 s t f (@lem3769672 _98313 s t f h1 h2)). Qed.
Lemma lem3769680 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : (@INTER _98313 s t) = t) (h2 : @IN (_98313 -> Prop) t f) : term102 _98313 s t f.
Proof. exact (fun h0 : term28 _98313 s t f => @lem3769679 _98313 s t f h1 h2). Qed.
Lemma lem3769682 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3769683 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : (term102 _98313 s t f) = (term26 _98313 s t f).
Proof. exact (@lem3769682 (term26 _98313 s t f)). Qed.
Lemma lem3769684 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : (@INTER _98313 s t) = t) (h2 : @IN (_98313 -> Prop) t f) : term26 _98313 s t f.
Proof. exact (EQ_MP (@lem3769683 _98313 s t f) (@lem3769680 _98313 s t f h1 h2)). Qed.
Lemma lem3769687 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3769689 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : (term28 _98313 s t f) = (term103 _98313 s t f).
Proof. exact (@lem3769687 (term26 _98313 s t f)). Qed.
Lemma lem3769692 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) : term103 _98313 s t f.
Proof. exact (EQ_MP (@lem3769689 _98313 s t f) (@lem3769266 _98313 s t f h1)). Qed.
Lemma lem3769695 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = t) (h3 : @IN (_98313 -> Prop) t f) : False.
Proof. exact (@lem3769692 _98313 s t f h1 (@lem3769684 _98313 s t f h2 h3)). Qed.
Lemma lem3769696 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = t) (h3 : @IN (_98313 -> Prop) t f) : term32.
Proof. exact (fun h0 : ~ False => @lem3769695 _98313 s t f h1 h2 h3). Qed.
Lemma lem3769698 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3769699 : term32 = False.
Proof. exact (@lem3769698 False). Qed.
Lemma lem3769700 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = t) (h3 : @IN (_98313 -> Prop) t f) : False.
Proof. exact (EQ_MP (@lem3769699) (@lem3769696 _98313 s t f h1 h2 h3)). Qed.
Lemma lem3769701 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = t) (h3 : @IN (_98313 -> Prop) t f) : ((@INTER _98313 s t) = t) = False.
Proof. exact (prop_ext (fun h4 : (@INTER _98313 s t) = t => @lem3769700 _98313 s t f h1 h2 h3) (fun h4 : False => @lem3769268 _98313 s t h2)). Qed.
Lemma lem3769702 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = t) (h3 : @IN (_98313 -> Prop) t f) : False.
Proof. exact (EQ_MP (@lem3769701 _98313 s t f h1 h2 h3) (@lem3769268 _98313 s t h2)). Qed.
Lemma lem3769703 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = t) (h3 : @IN (_98313 -> Prop) t f) : (@IN (_98313 -> Prop) t f) = False.
Proof. exact (prop_ext (fun h4 : @IN (_98313 -> Prop) t f => @lem3769702 _98313 s t f h1 h2 h3) (fun h4 : False => @lem3769262 _98313 t f h3)). Qed.
Lemma lem3769704 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = t) (h3 : @IN (_98313 -> Prop) t f) : False.
Proof. exact (EQ_MP (@lem3769703 _98313 s t f h1 h2 h3) (@lem3769262 _98313 t f h3)). Qed.
Lemma lem3769705 {_98313 : Type'} (f : type686 _98313) (t : _98313 -> Prop) (s : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = s) : ((@INTER _98313 s t) = s) = False.
Proof. exact (prop_ext (fun h3 : (@INTER _98313 s t) = s => @lem3769329 _98313 f t s h1 h2) (fun h3 : False => @lem3769260 _98313 t s h2)). Qed.
Lemma lem3769706 {_98313 : Type'} (f : type686 _98313) (t : _98313 -> Prop) (s : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = s) : False.
Proof. exact (EQ_MP (@lem3769705 _98313 f t s h1 h2) (@lem3769260 _98313 t s h2)). Qed.
Lemma lem3769707 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = t) (h3 : @IN (_98313 -> Prop) t f) : ((@INTER _98313 s t) = t) = False.
Proof. exact (prop_ext (fun h4 : (@INTER _98313 s t) = t => @lem3769704 _98313 s t f h1 h2 h3) (fun h4 : False => @lem3769252 _98313 s t h2)). Qed.
Lemma lem3769708 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = t) (h3 : @IN (_98313 -> Prop) t f) : False.
Proof. exact (EQ_MP (@lem3769707 _98313 s t f h1 h2 h3) (@lem3769252 _98313 s t h2)). Qed.
Lemma lem3769709 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = t) (h3 : @IN (_98313 -> Prop) t f) : (@IN (_98313 -> Prop) t f) = False.
Proof. exact (prop_ext (fun h4 : @IN (_98313 -> Prop) t f => @lem3769708 _98313 s t f h1 h2 h3) (fun h4 : False => @lem3769240 _98313 t f h3)). Qed.
Lemma lem3769710 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = t) (h3 : @IN (_98313 -> Prop) t f) : False.
Proof. exact (EQ_MP (@lem3769709 _98313 s t f h1 h2 h3) (@lem3769240 _98313 t f h3)). Qed.
Lemma lem3769711 {_98313 : Type'} (f : type686 _98313) (t : _98313 -> Prop) (s : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = s) : ((@INTER _98313 s t) = s) = False.
Proof. exact (prop_ext (fun h3 : (@INTER _98313 s t) = s => @lem3769706 _98313 f t s h1 h2) (fun h3 : False => @lem3769236 _98313 t s h2)). Qed.
Lemma lem3769712 {_98313 : Type'} (f : type686 _98313) (t : _98313 -> Prop) (s : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = s) : False.
Proof. exact (EQ_MP (@lem3769711 _98313 f t s h1 h2) (@lem3769236 _98313 t s h2)). Qed.
Lemma lem3769713 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = t) (h3 : @IN (_98313 -> Prop) t f) : ((@INTER _98313 s t) = t) = False.
Proof. exact (prop_ext (fun h4 : (@INTER _98313 s t) = t => @lem3769710 _98313 s t f h1 h2 h3) (fun h4 : False => @lem3769252 _98313 s t h2)). Qed.
Lemma lem3769714 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = t) (h3 : @IN (_98313 -> Prop) t f) : False.
Proof. exact (EQ_MP (@lem3769713 _98313 s t f h1 h2 h3) (@lem3769252 _98313 s t h2)). Qed.
Lemma lem3769715 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = t) (h3 : @IN (_98313 -> Prop) t f) : (@IN (_98313 -> Prop) t f) = False.
Proof. exact (prop_ext (fun h4 : @IN (_98313 -> Prop) t f => @lem3769714 _98313 s t f h1 h2 h3) (fun h4 : False => @lem3769240 _98313 t f h3)). Qed.
Lemma lem3769716 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = t) (h3 : @IN (_98313 -> Prop) t f) : False.
Proof. exact (EQ_MP (@lem3769715 _98313 s t f h1 h2 h3) (@lem3769240 _98313 t f h3)). Qed.
Lemma lem3769717 {_98313 : Type'} (f : type686 _98313) (t : _98313 -> Prop) (s : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = s) : ((@INTER _98313 s t) = s) = False.
Proof. exact (prop_ext (fun h3 : (@INTER _98313 s t) = s => @lem3769712 _98313 f t s h1 h2) (fun h3 : False => @lem3769236 _98313 t s h2)). Qed.
Lemma lem3769718 {_98313 : Type'} (f : type686 _98313) (t : _98313 -> Prop) (s : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : (@INTER _98313 s t) = s) : False.
Proof. exact (EQ_MP (@lem3769717 _98313 f t s h1 h2) (@lem3769236 _98313 t s h2)). Qed.
Lemma lem3769719 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : @IN (_98313 -> Prop) t f) (h3 : term24 _98313 s t) : False.
Proof. exact (or_elim (@lem3769184 _98313 s t h3) (fun h0 : (@INTER _98313 s t) = s => @lem3769718 _98313 f t s h1 h0) (fun h0 : (@INTER _98313 s t) = t => @lem3769716 _98313 s t f h1 h0 h2)). Qed.
Lemma lem3769720 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : @IN (_98313 -> Prop) t f) (h3 : term24 _98313 s t) : (@IN (_98313 -> Prop) t f) = False.
Proof. exact (prop_ext (fun h4 : @IN (_98313 -> Prop) t f => @lem3769719 _98313 f s t h1 h2 h3) (fun h4 : False => @lem3769190 _98313 t f h2)). Qed.
Lemma lem3769721 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : @IN (_98313 -> Prop) t f) (h3 : term24 _98313 s t) : False.
Proof. exact (EQ_MP (@lem3769720 _98313 f s t h1 h2 h3) (@lem3769190 _98313 t f h2)). Qed.
Lemma lem3769722 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : @IN (_98313 -> Prop) t f) (h3 : term24 _98313 s t) : (term24 _98313 s t) = False.
Proof. exact (prop_ext (fun h4 : term24 _98313 s t => @lem3769721 _98313 f s t h1 h2 h3) (fun h4 : False => @lem3769184 _98313 s t h3)). Qed.
Lemma lem3769723 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : @IN (_98313 -> Prop) t f) (h3 : term24 _98313 s t) : False.
Proof. exact (EQ_MP (@lem3769722 _98313 f s t h1 h2 h3) (@lem3769184 _98313 s t h3)). Qed.
Lemma lem3769724 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : @IN (_98313 -> Prop) t f) (h3 : term24 _98313 s t) : (@IN (_98313 -> Prop) t f) = False.
Proof. exact (prop_ext (fun h4 : @IN (_98313 -> Prop) t f => @lem3769723 _98313 f s t h1 h2 h3) (fun h4 : False => @lem3769150 _98313 t f h2)). Qed.
Lemma lem3769725 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : @IN (_98313 -> Prop) t f) (h3 : term24 _98313 s t) : False.
Proof. exact (EQ_MP (@lem3769724 _98313 f s t h1 h2 h3) (@lem3769150 _98313 t f h2)). Qed.
Lemma lem3769726 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : @IN (_98313 -> Prop) t f) (h3 : term24 _98313 s t) : (term24 _98313 s t) = False.
Proof. exact (prop_ext (fun h4 : term24 _98313 s t => @lem3769725 _98313 f s t h1 h2 h3) (fun h4 : False => @lem3769144 _98313 s t h3)). Qed.
Lemma lem3769727 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : @IN (_98313 -> Prop) t f) (h3 : term24 _98313 s t) : False.
Proof. exact (EQ_MP (@lem3769726 _98313 f s t h1 h2 h3) (@lem3769144 _98313 s t h3)). Qed.
Lemma lem3769728 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : @IN (_98313 -> Prop) t f) (h3 : term24 _98313 s t) : (term23 _98313 s t f) = False.
Proof. exact (prop_ext (fun h4 : term23 _98313 s t f => @lem3769727 _98313 f s t h1 h2 h3) (fun h4 : False => @lem3769134 _98313 s t f h1)). Qed.
Lemma lem3769729 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term23 _98313 s t f) (h2 : @IN (_98313 -> Prop) t f) (h3 : term24 _98313 s t) : False.
Proof. exact (EQ_MP (@lem3769728 _98313 f s t h1 h2 h3) (@lem3769134 _98313 s t f h1)). Qed.
Lemma lem3769730 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : @IN (_98313 -> Prop) t f) (h2 : term24 _98313 s t) : term22 _98313 s t f.
Proof. exact (fun h0 : term23 _98313 s t f => @lem3769729 _98313 f s t h0 h1 h2). Qed.
Lemma lem3769731 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : @IN (_98313 -> Prop) t f) (h2 : term24 _98313 s t) : term21 _98313 s t f.
Proof. exact (EQ_MP (@lem3769133 _98313 s t f) (@lem3769730 _98313 f s t h1 h2)). Qed.
Lemma lem3769732 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term24 _98313 s t) : term104 _98313 s t f.
Proof. exact (fun h0 : @IN (_98313 -> Prop) t f => @lem3769731 _98313 f s t h0 h1). Qed.
Lemma lem3769733 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : term1 _98313 s t f.
Proof. exact (fun h0 : term24 _98313 s t => @lem3769732 _98313 f s t h0). Qed.
Lemma lem3769738 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) : term12 _98313 t f.
Proof. exact (fun s : _98313 -> Prop => @lem3769733 _98313 s t f). Qed.
Lemma lem3769743 {_98313 : Type'} (f : type686 _98313) : term16 _98313 f.
Proof. exact (fun t : _98313 -> Prop => @lem3769738 _98313 t f). Qed.
Lemma lem3769748 {_98313 : Type'} : term20 _98313.
Proof. exact (fun f : type686 _98313 => @lem3769743 _98313 f). Qed.
Lemma lem3769749 {_98313 : Type'} : term19 _98313.
Proof. exact (EQ_MP (@lem3769127 _98313) (@lem3769748 _98313)). Qed.
Lemma lem3769750 {_98313 : Type'} (f : type686 _98313) : term105 _98313 f.
Proof. exact (@lem3769749 _98313 f). Qed.
Lemma lem3769751 {_98313 : Type'} (f : type686 _98313) : (term105 _98313 f) = (term15 _98313 f).
Proof. exact (eq_refl (term105 _98313 f)). Qed.
Lemma lem3769752 {_98313 : Type'} (f : type686 _98313) : term15 _98313 f.
Proof. exact (EQ_MP (@lem3769751 _98313 f) (@lem3769750 _98313 f)). Qed.
Lemma lem3769753 {_98313 : Type'} (f : type686 _98313) (t : _98313 -> Prop) : term106 _98313 f t.
Proof. exact (@lem3769752 _98313 f t). Qed.
Lemma lem3769754 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) : (term106 _98313 f t) = (term11 _98313 t f).
Proof. exact (eq_refl (term106 _98313 f t)). Qed.
Lemma lem3769755 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) : term11 _98313 t f.
Proof. exact (EQ_MP (@lem3769754 _98313 t f) (@lem3769753 _98313 f t)). Qed.
Lemma lem3769756 {_98313 : Type'} (t : _98313 -> Prop) (f : type686 _98313) (s : _98313 -> Prop) : term107 _98313 t f s.
Proof. exact (@lem3769755 _98313 t f s). Qed.
Lemma lem3769757 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : (term107 _98313 t f s) = (term2 _98313 s t f).
Proof. exact (eq_refl (term107 _98313 t f s)). Qed.
Lemma lem3769758 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : term2 _98313 s t f.
Proof. exact (EQ_MP (@lem3769757 _98313 s t f) (@lem3769756 _98313 t f s)). Qed.
Lemma lem3769760 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : term2 _98313 s t f.
Proof. exact (@lem3769019 _98313 s t f (@lem3769758 _98313 s t f)). Qed.
Lemma lem3769761 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term3 _98313 s t f) : False.
Proof. exact (@lem3769760 _98313 s t f (@lem3769003 _98313 s t f h1)). Qed.
Lemma lem3769762 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term3 _98313 s t f) : (term3 _98313 s t f) = False.
Proof. exact (prop_ext (fun h2 : term3 _98313 s t f => @lem3769761 _98313 s t f h1) (fun h2 : False => @lem3769003 _98313 s t f h1)). Qed.
Lemma lem3769763 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term3 _98313 s t f) : False.
Proof. exact (EQ_MP (@lem3769762 _98313 s t f h1) (@lem3769003 _98313 s t f h1)). Qed.
Lemma lem3769764 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : term2 _98313 s t f.
Proof. exact (fun h0 : term3 _98313 s t f => @lem3769763 _98313 s t f h0). Qed.
Lemma lem3769765 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : term1 _98313 s t f.
Proof. exact (EQ_MP (@lem3769002 _98313 s t f) (@lem3769764 _98313 s t f)). Qed.
Lemma lem3769766 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term1 _98313 s t f) : term1 _98313 s t f.
Proof. exact (h1). Qed.
Lemma lem3769767 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term24 _98313 s t) : term24 _98313 s t.
Proof. exact (h1). Qed.
Lemma lem3769768 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term1 _98313 s t f) (h2 : term24 _98313 s t) : term104 _98313 s t f.
Proof. exact (@lem3769766 _98313 s t f h1 (@lem3769767 _98313 s t h2)). Qed.
Lemma lem3769769 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term24 _98313 s t) : term108 _98313 s t f.
Proof. exact (fun h0 : term1 _98313 s t f => @lem3769768 _98313 f s t h0 h1). Qed.
Lemma lem3769770 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term1 _98313 s t f) : term1 _98313 s t f.
Proof. exact (h1). Qed.
Lemma lem3769771 {_98313 : Type'} (f : type686 _98313) (s : _98313 -> Prop) (t : _98313 -> Prop) (h1 : term1 _98313 s t f) (h2 : term24 _98313 s t) : term104 _98313 s t f.
Proof. exact (@lem3769769 _98313 f s t h2 (@lem3769770 _98313 s t f h1)). Qed.
Lemma lem3769772 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) (h1 : term1 _98313 s t f) : term1 _98313 s t f.
Proof. exact (fun h0 : term24 _98313 s t => @lem3769771 _98313 f s t h1 h0). Qed.
Lemma lem3769773 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : term109 _98313 s t f.
Proof. exact (fun h0 : term1 _98313 s t f => @lem3769772 _98313 s t f h0). Qed.
Lemma lem3769775 {A : Type'} (f : type686 A) : term110 A f.
Proof. exact (@lem9784 (f = (@EMPTY (A -> Prop)))). Qed.
Lemma lem3769776 {A : Type'} (f : type686 A) : (term110 A f) = (term111 A f).
Proof. exact (eq_refl (term110 A f)). Qed.
Lemma lem3769777 {A : Type'} (f : type686 A) : term111 A f.
Proof. exact (EQ_MP (@lem3769776 A f) (@lem3769775 A f)). Qed.
Lemma lem3769779 {A : Type'} (f : type686 A) (h1 : term112 A f) : term112 A f.
Proof. exact (h1). Qed.
Lemma lem3769794 (p : Prop) : term113 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem3769795 (p : Prop) : (term113 p) = (term114 p).
Proof. exact (eq_refl (term113 p)). Qed.
Lemma lem3769796 (p : Prop) : term114 p.
Proof. exact (EQ_MP (@lem3769795 p) (@lem3769794 p)). Qed.
Lemma lem3769797 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem3769798 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem3769813 (q : Prop) (r : Prop) : (term115 q r) = (term115 q r).
Proof. exact (eq_refl (term115 q r)). Qed.
Lemma lem3769814 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : (term116 q r p) = (term117 q r).
Proof. exact (MK_COMB (@lem3769813 q r) (@lem3769797 p h1)). Qed.
Lemma lem3769815 (q : Prop) (r : Prop) : (term117 q r) = ((term118 q r) = (term119 q r)).
Proof. exact (eq_refl (term117 q r)). Qed.
Lemma lem3769816 (q : Prop) (r : Prop) (p : Prop) : (term120 q r p) = (term120 q r p).
Proof. exact (eq_refl (term120 q r p)). Qed.
Lemma lem3769817 (p : Prop) (q : Prop) (r : Prop) : ((term116 q r p) = (term117 q r)) = ((term116 q r p) = ((term118 q r) = (term119 q r))).
Proof. exact (MK_COMB (@lem3769816 q r p) (@lem3769815 q r)). Qed.
Lemma lem3769818 (q : Prop) (p : Prop) (r : Prop) : (term116 q r p) = ((term121 p q r) = (term122 q p r)).
Proof. exact (eq_refl (term116 q r p)). Qed.
Lemma lem3769819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3769820 (q : Prop) (p : Prop) (r : Prop) : (term120 q r p) = (term123 q p r).
Proof. exact (MK_COMB (@lem3769819) (@lem3769818 q p r)). Qed.
Lemma lem3769821 (q : Prop) (r : Prop) : ((term118 q r) = (term119 q r)) = ((term118 q r) = (term119 q r)).
Proof. exact (eq_refl ((term118 q r) = (term119 q r))). Qed.
Lemma lem3769822 (p : Prop) (q : Prop) (r : Prop) : ((term116 q r p) = ((term118 q r) = (term119 q r))) = (((term121 p q r) = (term122 q p r)) = ((term118 q r) = (term119 q r))).
Proof. exact (MK_COMB (@lem3769820 q p r) (@lem3769821 q r)). Qed.
Lemma lem3769823 (p : Prop) (q : Prop) (r : Prop) : ((term116 q r p) = (term117 q r)) = (((term121 p q r) = (term122 q p r)) = ((term118 q r) = (term119 q r))).
Proof. exact (TRANS (@lem3769817 p q r) (@lem3769822 p q r)). Qed.
Lemma lem3769824 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : ((term121 p q r) = (term122 q p r)) = ((term118 q r) = (term119 q r)).
Proof. exact (EQ_MP (@lem3769823 p q r) (@lem3769814 q r p h1)). Qed.
Lemma lem3769825 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : ((term118 q r) = (term119 q r)) = ((term121 p q r) = (term122 q p r)).
Proof. exact (SYM (@lem3769824 q r p h1)). Qed.
Lemma lem3769826 (q : Prop) (r : Prop) : (term115 q r) = (term115 q r).
Proof. exact (eq_refl (term115 q r)). Qed.
Lemma lem3769827 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : (term116 q r p) = (term124 q r).
Proof. exact (MK_COMB (@lem3769826 q r) (@lem3769798 p h1)). Qed.
Lemma lem3769828 (q : Prop) (r : Prop) : (term124 q r) = ((term125 q r) = (term126 q r)).
Proof. exact (eq_refl (term124 q r)). Qed.
Lemma lem3769829 (q : Prop) (r : Prop) (p : Prop) : (term120 q r p) = (term120 q r p).
Proof. exact (eq_refl (term120 q r p)). Qed.
Lemma lem3769830 (p : Prop) (q : Prop) (r : Prop) : ((term116 q r p) = (term124 q r)) = ((term116 q r p) = ((term125 q r) = (term126 q r))).
Proof. exact (MK_COMB (@lem3769829 q r p) (@lem3769828 q r)). Qed.
Lemma lem3769831 (q : Prop) (p : Prop) (r : Prop) : (term116 q r p) = ((term121 p q r) = (term122 q p r)).
Proof. exact (eq_refl (term116 q r p)). Qed.
Lemma lem3769832 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3769833 (q : Prop) (p : Prop) (r : Prop) : (term120 q r p) = (term123 q p r).
Proof. exact (MK_COMB (@lem3769832) (@lem3769831 q p r)). Qed.
Lemma lem3769834 (q : Prop) (r : Prop) : ((term125 q r) = (term126 q r)) = ((term125 q r) = (term126 q r)).
Proof. exact (eq_refl ((term125 q r) = (term126 q r))). Qed.
Lemma lem3769835 (p : Prop) (q : Prop) (r : Prop) : ((term116 q r p) = ((term125 q r) = (term126 q r))) = (((term121 p q r) = (term122 q p r)) = ((term125 q r) = (term126 q r))).
Proof. exact (MK_COMB (@lem3769833 q p r) (@lem3769834 q r)). Qed.
Lemma lem3769836 (p : Prop) (q : Prop) (r : Prop) : ((term116 q r p) = (term124 q r)) = (((term121 p q r) = (term122 q p r)) = ((term125 q r) = (term126 q r))).
Proof. exact (TRANS (@lem3769830 p q r) (@lem3769835 p q r)). Qed.
Lemma lem3769837 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : ((term121 p q r) = (term122 q p r)) = ((term125 q r) = (term126 q r)).
Proof. exact (EQ_MP (@lem3769836 p q r) (@lem3769827 q r p h1)). Qed.
Lemma lem3769838 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : ((term125 q r) = (term126 q r)) = ((term121 p q r) = (term122 q p r)).
Proof. exact (SYM (@lem3769837 q r p h1)). Qed.
Lemma lem3769842 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3769843 (q : Prop) (r : Prop) : (term118 q r) = (q /\ r).
Proof. exact (@lem3769842 (q /\ r)). Qed.
Lemma lem3769846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3769847 (q : Prop) (r : Prop) : (term127 q r) = (term128 q r).
Proof. exact (MK_COMB (@lem3769846) (@lem3769843 q r)). Qed.
Lemma lem3769851 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3769852 (q : Prop) : (True -> q) = q.
Proof. exact (@lem3769851 q). Qed.
Lemma lem3769853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3769854 (q : Prop) : (term129 q) = (and q).
Proof. exact (MK_COMB (@lem3769853) (@lem3769852 q)). Qed.
Lemma lem3769856 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3769857 (r : Prop) : (True -> r) = r.
Proof. exact (@lem3769856 r). Qed.
Lemma lem3769858 (q : Prop) (r : Prop) : (term119 q r) = (q /\ r).
Proof. exact (MK_COMB (@lem3769854 q) (@lem3769857 r)). Qed.
Lemma lem3769861 (q : Prop) (r : Prop) : ((term118 q r) = (term119 q r)) = ((q /\ r) = (q /\ r)).
Proof. exact (MK_COMB (@lem3769847 q r) (@lem3769858 q r)). Qed.
Lemma lem3769863 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3769864 (x : Prop) : (x = x) = True.
Proof. exact (@lem3769863 Prop x). Qed.
Lemma lem3769865 (q : Prop) (r : Prop) : ((q /\ r) = (q /\ r)) = True.
Proof. exact (@lem3769864 (q /\ r)). Qed.
Lemma lem3769866 (q : Prop) (r : Prop) : ((term118 q r) = (term119 q r)) = True.
Proof. exact (TRANS (@lem3769861 q r) (@lem3769865 q r)). Qed.
Lemma lem3769867 (q : Prop) (r : Prop) : True = ((term118 q r) = (term119 q r)).
Proof. exact (SYM (@lem3769866 q r)). Qed.
Lemma lem3769868 (q : Prop) (r : Prop) : (term118 q r) = (term119 q r).
Proof. exact (EQ_MP (@lem3769867 q r) (@lem0)). Qed.
Lemma lem3769872 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3769873 (q : Prop) (r : Prop) : (term125 q r) = True.
Proof. exact (@lem3769872 (q /\ r)). Qed.
Lemma lem3769874 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3769875 (q : Prop) (r : Prop) : (term130 q r) = (@eq Prop True).
Proof. exact (MK_COMB (@lem3769874) (@lem3769873 q r)). Qed.
Lemma lem3769879 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3769880 (q : Prop) : (False -> q) = True.
Proof. exact (@lem3769879 q). Qed.
Lemma lem3769881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3769882 (q : Prop) : (term131 q) = (and True).
Proof. exact (MK_COMB (@lem3769881) (@lem3769880 q)). Qed.
Lemma lem3769884 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3769885 (r : Prop) : (False -> r) = True.
Proof. exact (@lem3769884 r). Qed.
Lemma lem3769886 (q : Prop) (r : Prop) : (term126 q r) = (True /\ True).
Proof. exact (MK_COMB (@lem3769882 q) (@lem3769885 r)). Qed.
Lemma lem3769888 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3769889 : (True /\ True) = True.
Proof. exact (@lem3769888 True). Qed.
Lemma lem3769890 (q : Prop) (r : Prop) : (term126 q r) = True.
Proof. exact (TRANS (@lem3769886 q r) (@lem3769889)). Qed.
Lemma lem3769891 (q : Prop) (r : Prop) : ((term125 q r) = (term126 q r)) = (True = True).
Proof. exact (MK_COMB (@lem3769875 q r) (@lem3769890 q r)). Qed.
Lemma lem3769893 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3769894 : (True = True) = True.
Proof. exact (@lem3769893 True). Qed.
Lemma lem3769895 (q : Prop) (r : Prop) : ((term125 q r) = (term126 q r)) = True.
Proof. exact (TRANS (@lem3769891 q r) (@lem3769894)). Qed.
Lemma lem3769896 (q : Prop) (r : Prop) : True = ((term125 q r) = (term126 q r)).
Proof. exact (SYM (@lem3769895 q r)). Qed.
Lemma lem3769897 (q : Prop) (r : Prop) : (term125 q r) = (term126 q r).
Proof. exact (EQ_MP (@lem3769896 q r) (@lem0)). Qed.
Lemma lem3769898 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : (term121 p q r) = (term122 q p r).
Proof. exact (EQ_MP (@lem3769838 q r p h1) (@lem3769897 q r)). Qed.
Lemma lem3769899 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : (term121 p q r) = (term122 q p r).
Proof. exact (EQ_MP (@lem3769825 q r p h1) (@lem3769868 q r)). Qed.
Lemma lem3769903 {A : Type'} (x : A) : term132 A x.
Proof. exact (@lem3278799 A x). Qed.
Lemma lem3769904 {A : Type'} (x : A) : (term132 A x) = (term133 A x).
Proof. exact (eq_refl (term132 A x)). Qed.
Lemma lem3769905 {A : Type'} (x : A) : term133 A x.
Proof. exact (EQ_MP (@lem3769904 A x) (@lem3769903 A x)). Qed.
Lemma lem3769906 {A : Type'} (x : A) (s : A -> Prop) : term134 A x s.
Proof. exact (@lem3769905 A x s). Qed.
Lemma lem3769907 {A : Type'} (x : A) (s : A -> Prop) : (term134 A x s) = (term135 A x s).
Proof. exact (eq_refl (term134 A x s)). Qed.
Lemma lem3769908 {A : Type'} (x : A) (s : A -> Prop) : term135 A x s.
Proof. exact (EQ_MP (@lem3769907 A x s) (@lem3769906 A x s)). Qed.
Lemma lem3769909 {A : Type'} (x : A) (s : A -> Prop) : term136 A x s.
Proof. exact (@lem82 ((@INSERT A x s) = (@EMPTY A))). Qed.
Lemma lem3769922 {A : Type'} (P : A -> Prop) : term137 A P.
Proof. exact (@lem4997 A P). Qed.
Lemma lem3769923 {A : Type'} (P : A -> Prop) : (term137 A P) = (term138 A P).
Proof. exact (eq_refl (term137 A P)). Qed.
Lemma lem3769924 {A : Type'} (P : A -> Prop) : term138 A P.
Proof. exact (EQ_MP (@lem3769923 A P) (@lem3769922 A P)). Qed.
Lemma lem3769925 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term139 A P Q.
Proof. exact (@lem3769924 A P Q). Qed.
Lemma lem3769926 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term139 A P Q) = ((term140 A P Q) = (term141 A P Q)).
Proof. exact (eq_refl (term139 A P Q)). Qed.
Lemma lem3769928 {_83983 : Type'} (P : _83983 -> Prop) : term142 _83983 P.
Proof. exact (@lem3207453 _83983 P). Qed.
Lemma lem3769929 {_83983 : Type'} (P : _83983 -> Prop) : (term142 _83983 P) = (term143 _83983 P).
Proof. exact (eq_refl (term142 _83983 P)). Qed.
Lemma lem3769930 {_83983 : Type'} (P : _83983 -> Prop) : term143 _83983 P.
Proof. exact (EQ_MP (@lem3769929 _83983 P) (@lem3769928 _83983 P)). Qed.
Lemma lem3769931 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : term144 _83983 P a.
Proof. exact (@lem3769930 _83983 P a). Qed.
Lemma lem3769932 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term144 _83983 P a) = (term145 _83983 a P).
Proof. exact (eq_refl (term144 _83983 P a)). Qed.
Lemma lem3769933 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term145 _83983 a P.
Proof. exact (EQ_MP (@lem3769932 _83983 a P) (@lem3769931 _83983 P a)). Qed.
Lemma lem3769934 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (s : _83983 -> Prop) : term146 _83983 a P s.
Proof. exact (@lem3769933 _83983 a P s). Qed.
Lemma lem3769935 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term146 _83983 a P s) = ((term147 _83983 a s P) = (term148 _83983 a s P)).
Proof. exact (eq_refl (term146 _83983 a P s)). Qed.
Lemma lem3769937 {A : Type'} (P : Prop) : term149 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem3769938 {A : Type'} (P : Prop) : (term149 A P) = (term150 A P).
Proof. exact (eq_refl (term149 A P)). Qed.
Lemma lem3769939 {A : Type'} (P : Prop) : term150 A P.
Proof. exact (EQ_MP (@lem3769938 A P) (@lem3769937 A P)). Qed.
Lemma lem3769940 {A : Type'} (P : Prop) (Q : A -> Prop) : term151 A P Q.
Proof. exact (@lem3769939 A P Q). Qed.
Lemma lem3769941 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = ((term152 A P Q) = (term153 A P Q)).
Proof. exact (eq_refl (term151 A P Q)). Qed.
Lemma lem3769943 {A : Type'} (h1 : term154 A) : term154 A.
Proof. exact (h1). Qed.
Lemma lem3769944 {A : Type'} (FINITE' : type686 A) (h1 : term154 A) : term155 A FINITE'.
Proof. exact (@lem3769943 A h1 FINITE'). Qed.
Lemma lem3769945 {A : Type'} (FINITE' : type686 A) : (term155 A FINITE') = (term156 A FINITE').
Proof. exact (eq_refl (term155 A FINITE')). Qed.
Lemma lem3769946 {A : Type'} (FINITE' : type686 A) (h1 : term154 A) : term156 A FINITE'.
Proof. exact (EQ_MP (@lem3769945 A FINITE') (@lem3769944 A FINITE' h1)). Qed.
Lemma lem3769947 {A : Type'} (FINITE' : type686 A) (h1 : term157 A FINITE') : term157 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3769948 {A : Type'} (FINITE' : type686 A) (h1 : term154 A) (h2 : term157 A FINITE') : term158 A FINITE'.
Proof. exact (@lem3769946 A FINITE' h1 (@lem3769947 A FINITE' h2)). Qed.
Lemma lem3769949 {A : Type'} (FINITE' : type686 A) (h1 : term157 A FINITE') : term159 A FINITE'.
Proof. exact (fun h0 : term154 A => @lem3769948 A FINITE' h0 h1). Qed.
Lemma lem3769950 {A : Type'} (h1 : term154 A) : term154 A.
Proof. exact (h1). Qed.
Lemma lem3769951 {A : Type'} (FINITE' : type686 A) (h1 : term154 A) (h2 : term157 A FINITE') : term158 A FINITE'.
Proof. exact (@lem3769949 A FINITE' h2 (@lem3769950 A h1)). Qed.
Lemma lem3769952 {A : Type'} (FINITE' : type686 A) (h1 : term154 A) : term156 A FINITE'.
Proof. exact (fun h0 : term157 A FINITE' => @lem3769951 A FINITE' h1 h0). Qed.
Lemma lem3769953 {A : Type'} (h1 : term154 A) : term154 A.
Proof. exact (fun FINITE' : type686 A => @lem3769952 A FINITE' h1). Qed.
Lemma lem3769954 {A : Type'} : term160 A.
Proof. exact (fun h0 : term154 A => @lem3769953 A h0). Qed.
Lemma lem3769955 {A : Type'} : term154 A.
Proof. exact (@lem3769954 A (@lem3197567 A)). Qed.
Lemma lem3769956 {A : Type'} (FINITE' : type686 A) : term155 A FINITE'.
Proof. exact (@lem3769955 A FINITE'). Qed.
Lemma lem3769957 {A : Type'} (FINITE' : type686 A) : (term155 A FINITE') = (term156 A FINITE').
Proof. exact (eq_refl (term155 A FINITE')). Qed.
Lemma lem3769964 (p : Prop) (q : Prop) (r : Prop) : (term161 p q r) = (term162 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem3769965 {A : Type'} (f : type686 A) : (term163 A f) = (term164 A f).
Proof. exact (@lem3769964 (@FINITE (A -> Prop) f) (term165 A f) (term166 A f)). Qed.
Lemma lem3769969 (p : Prop) (q : Prop) (r : Prop) : (term161 p q r) = (term162 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem3769970 {A : Type'} (f : type686 A) : (term167 A f) = (term168 A f).
Proof. exact (@lem3769969 (term112 A f) (term169 A f) (term166 A f)). Qed.
Lemma lem3769986 (p : Prop) (q : Prop) (r : Prop) : (term161 p q r) = (term162 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem3769987 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term170 A f t s) = (term171 A f t s).
Proof. exact (@lem3769986 (@IN (A -> Prop) s f) (@IN (A -> Prop) t f) (term172 A t s)). Qed.
Lemma lem3769994 {A : Type'} (f : type686 A) (s : A -> Prop) : (term173 A f s) = (term174 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3769987 A f t s)). Qed.
Lemma lem3769995 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3769996 {A : Type'} (f : type686 A) (s : A -> Prop) : (term175 A f s) = (term176 A f s).
Proof. exact (MK_COMB (@lem3769995 A) (@lem3769994 A f s)). Qed.
Lemma lem3770001 {A : Type'} (f : type686 A) : (term177 A f) = (term178 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3769996 A f s)). Qed.
Lemma lem3770002 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770003 {A : Type'} (f : type686 A) : (term169 A f) = (term179 A f).
Proof. exact (MK_COMB (@lem3770002 A) (@lem3770001 A f)). Qed.
Lemma lem3770008 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3770009 {A : Type'} (f : type686 A) : (term180 A f) = (term181 A f).
Proof. exact (MK_COMB (@lem3770008) (@lem3770003 A f)). Qed.
Lemma lem3770010 {A : Type'} (f : type686 A) : (term166 A f) = (term166 A f).
Proof. exact (eq_refl (term166 A f)). Qed.
Lemma lem3770011 {A : Type'} (f : type686 A) : (term182 A f) = (term183 A f).
Proof. exact (MK_COMB (@lem3770009 A f) (@lem3770010 A f)). Qed.
Lemma lem3770014 {A : Type'} (f : type686 A) : (term184 A f) = (term184 A f).
Proof. exact (eq_refl (term184 A f)). Qed.
Lemma lem3770015 {A : Type'} (f : type686 A) : (term168 A f) = (term185 A f).
Proof. exact (MK_COMB (@lem3770014 A f) (@lem3770011 A f)). Qed.
Lemma lem3770018 {A : Type'} (f : type686 A) : (term167 A f) = (term185 A f).
Proof. exact (TRANS (@lem3769970 A f) (@lem3770015 A f)). Qed.
Lemma lem3770019 {A : Type'} (f : type686 A) : (term186 A f) = (term186 A f).
Proof. exact (eq_refl (term186 A f)). Qed.
Lemma lem3770020 {A : Type'} (f : type686 A) : (term164 A f) = (term187 A f).
Proof. exact (MK_COMB (@lem3770019 A f) (@lem3770018 A f)). Qed.
Lemma lem3770023 {A : Type'} (f : type686 A) : (term163 A f) = (term187 A f).
Proof. exact (TRANS (@lem3769965 A f) (@lem3770020 A f)). Qed.
Lemma lem3770024 {A : Type'} : (term188 A) = (term189 A).
Proof. exact (fun_ext (fun f : type686 A => @lem3770023 A f)). Qed.
Lemma lem3770025 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3770026 {A : Type'} : (term190 A) = (term191 A).
Proof. exact (MK_COMB (@lem3770025 A) (@lem3770024 A)). Qed.
Lemma lem3770031 {A : Type'} : (term191 A) = (term190 A).
Proof. exact (SYM (@lem3770026 A)). Qed.
Lemma lem3770033 {A : Type'} (FINITE' : type686 A) : term156 A FINITE'.
Proof. exact (EQ_MP (@lem3769957 A FINITE') (@lem3769956 A FINITE')). Qed.
Lemma lem3770034 {A : Type'} (FINITE' : type180 A) : term192 A FINITE'.
Proof. exact (@lem3770033 (A -> Prop) FINITE'). Qed.
Lemma lem3770035 {A : Type'} : term193 A.
Proof. exact (@lem3770034 A (term194 A)). Qed.
Lemma lem3770036 {A : Type'} : (term195 A) = (term196 A).
Proof. exact (eq_refl (term195 A)). Qed.
Lemma lem3770037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3770038 {A : Type'} : (term197 A) = (term198 A).
Proof. exact (MK_COMB (@lem3770037) (@lem3770036 A)). Qed.
Lemma lem3770039 {A : Type'} (s : type686 A) : (term199 A s) = (term185 A s).
Proof. exact (eq_refl (term199 A s)). Qed.
Lemma lem3770040 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3770041 {A : Type'} (s : type686 A) : (term200 A s) = (term201 A s).
Proof. exact (MK_COMB (@lem3770040) (@lem3770039 A s)). Qed.
Lemma lem3770042 {A : Type'} (x : A -> Prop) (s : type686 A) : (term202 A x s) = (term203 A x s).
Proof. exact (eq_refl (term202 A x s)). Qed.
Lemma lem3770043 {A : Type'} (x : A -> Prop) (s : type686 A) : (term204 A x s) = (term205 A x s).
Proof. exact (MK_COMB (@lem3770041 A s) (@lem3770042 A x s)). Qed.
Lemma lem3770044 {A : Type'} (x : A -> Prop) : (term206 A x) = (term207 A x).
Proof. exact (fun_ext (fun s : type686 A => @lem3770043 A x s)). Qed.
Lemma lem3770045 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3770046 {A : Type'} (x : A -> Prop) : (term208 A x) = (term209 A x).
Proof. exact (MK_COMB (@lem3770045 A) (@lem3770044 A x)). Qed.
Lemma lem3770047 {A : Type'} : (term210 A) = (term211 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3770046 A x)). Qed.
Lemma lem3770048 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770049 {A : Type'} : (term212 A) = (term213 A).
Proof. exact (MK_COMB (@lem3770048 A) (@lem3770047 A)). Qed.
Lemma lem3770050 {A : Type'} : (term214 A) = (term215 A).
Proof. exact (MK_COMB (@lem3770038 A) (@lem3770049 A)). Qed.
Lemma lem3770051 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3770052 {A : Type'} : (term216 A) = (term217 A).
Proof. exact (MK_COMB (@lem3770051) (@lem3770050 A)). Qed.
Lemma lem3770053 {A : Type'} (f : type686 A) : (term199 A f) = (term185 A f).
Proof. exact (eq_refl (term199 A f)). Qed.
Lemma lem3770054 {A : Type'} (f : type686 A) : (term186 A f) = (term186 A f).
Proof. exact (eq_refl (term186 A f)). Qed.
Lemma lem3770055 {A : Type'} (f : type686 A) : (term218 A f) = (term187 A f).
Proof. exact (MK_COMB (@lem3770054 A f) (@lem3770053 A f)). Qed.
Lemma lem3770056 {A : Type'} : (term219 A) = (term189 A).
Proof. exact (fun_ext (fun f : type686 A => @lem3770055 A f)). Qed.
Lemma lem3770057 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3770058 {A : Type'} : (term220 A) = (term191 A).
Proof. exact (MK_COMB (@lem3770057 A) (@lem3770056 A)). Qed.
Lemma lem3770059 {A : Type'} : (term193 A) = (term221 A).
Proof. exact (MK_COMB (@lem3770052 A) (@lem3770058 A)). Qed.
Lemma lem3770060 {A : Type'} : term221 A.
Proof. exact (EQ_MP (@lem3770059 A) (@lem3770035 A)). Qed.
Lemma lem3770066 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3770067 {A : Type'} (x : type686 A) : (x = x) = True.
Proof. exact (@lem3770066 (type686 A) x). Qed.
Lemma lem3770068 {A : Type'} : ((@EMPTY (A -> Prop)) = (@EMPTY (A -> Prop))) = True.
Proof. exact (@lem3770067 A (@EMPTY (A -> Prop))). Qed.
Lemma lem3770069 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3770070 {A : Type'} : (term222 A) = (~ True).
Proof. exact (MK_COMB (@lem3770069) (@lem3770068 A)). Qed.
Lemma lem3770072 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3770073 {A : Type'} : (term222 A) = False.
Proof. exact (TRANS (@lem3770070 A) (@lem3770072)). Qed.
Lemma lem3770074 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3770075 {A : Type'} : (term223 A) = (imp False).
Proof. exact (MK_COMB (@lem3770074) (@lem3770073 A)). Qed.
Lemma lem3770083 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem3769941 A P Q) (@lem3769940 A P Q)). Qed.
Lemma lem3770084 {A : Type'} (P : Prop) (Q : type686 A) : (term224 A P Q) = (term225 A P Q).
Proof. exact (@lem3770083 (A -> Prop) P Q). Qed.
Lemma lem3770085 {A : Type'} (s : A -> Prop) : (term226 A s) = (term227 A s).
Proof. exact (@lem3770084 A (@IN (A -> Prop) s (@EMPTY (A -> Prop))) (term228 A s)). Qed.
Lemma lem3770086 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term229 A s t) = (term230 A t s).
Proof. exact (eq_refl (term229 A s t)). Qed.
Lemma lem3770087 {A : Type'} (s : A -> Prop) : (term231 A s) = (term231 A s).
Proof. exact (eq_refl (term231 A s)). Qed.
Lemma lem3770088 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term232 A s t) = (term233 A t s).
Proof. exact (MK_COMB (@lem3770087 A s) (@lem3770086 A t s)). Qed.
Lemma lem3770089 {A : Type'} (s : A -> Prop) : (term234 A s) = (term235 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3770088 A t s)). Qed.
Lemma lem3770090 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770091 {A : Type'} (s : A -> Prop) : (term226 A s) = (term236 A s).
Proof. exact (MK_COMB (@lem3770090 A) (@lem3770089 A s)). Qed.
Lemma lem3770092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3770093 {A : Type'} (s : A -> Prop) : (term237 A s) = (term238 A s).
Proof. exact (MK_COMB (@lem3770092) (@lem3770091 A s)). Qed.
Lemma lem3770094 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term229 A s t) = (term230 A t s).
Proof. exact (eq_refl (term229 A s t)). Qed.
Lemma lem3770095 {A : Type'} (s : A -> Prop) : (term239 A s) = (term228 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3770094 A t s)). Qed.
Lemma lem3770096 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770097 {A : Type'} (s : A -> Prop) : (term240 A s) = (term241 A s).
Proof. exact (MK_COMB (@lem3770096 A) (@lem3770095 A s)). Qed.
Lemma lem3770098 {A : Type'} (s : A -> Prop) : (term231 A s) = (term231 A s).
Proof. exact (eq_refl (term231 A s)). Qed.
Lemma lem3770099 {A : Type'} (s : A -> Prop) : (term227 A s) = (term242 A s).
Proof. exact (MK_COMB (@lem3770098 A s) (@lem3770097 A s)). Qed.
Lemma lem3770100 {A : Type'} (s : A -> Prop) : ((term226 A s) = (term227 A s)) = ((term236 A s) = (term242 A s)).
Proof. exact (MK_COMB (@lem3770093 A s) (@lem3770099 A s)). Qed.
Lemma lem3770101 {A : Type'} (s : A -> Prop) : (term236 A s) = (term242 A s).
Proof. exact (EQ_MP (@lem3770100 A s) (@lem3770085 A s)). Qed.
Lemma lem3770132 {A : Type'} : (term243 A) = (term244 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3770101 A s)). Qed.
Lemma lem3770133 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770134 {A : Type'} : (term245 A) = (term246 A).
Proof. exact (MK_COMB (@lem3770133 A) (@lem3770132 A)). Qed.
Lemma lem3770159 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3770160 {A : Type'} : (term247 A) = (term248 A).
Proof. exact (MK_COMB (@lem3770159) (@lem3770134 A)). Qed.
Lemma lem3770161 {A : Type'} : (term249 A) = (term249 A).
Proof. exact (eq_refl (term249 A)). Qed.
Lemma lem3770162 {A : Type'} : (term250 A) = (term251 A).
Proof. exact (MK_COMB (@lem3770160 A) (@lem3770161 A)). Qed.
Lemma lem3770165 {A : Type'} : (term196 A) = (term252 A).
Proof. exact (MK_COMB (@lem3770075 A) (@lem3770162 A)). Qed.
Lemma lem3770167 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3770168 {A : Type'} : (term252 A) = True.
Proof. exact (@lem3770167 (term251 A)). Qed.
Lemma lem3770169 {A : Type'} : (term196 A) = True.
Proof. exact (TRANS (@lem3770165 A) (@lem3770168 A)). Qed.
Lemma lem3770170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3770171 {A : Type'} : (term198 A) = (and True).
Proof. exact (MK_COMB (@lem3770170) (@lem3770169 A)). Qed.
Lemma lem3770213 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem3769941 A P Q) (@lem3769940 A P Q)). Qed.
Lemma lem3770214 {A : Type'} (P : Prop) (Q : type686 A) : (term224 A P Q) = (term225 A P Q).
Proof. exact (@lem3770213 (A -> Prop) P Q). Qed.
Lemma lem3770215 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term253 A s s') = (term254 A s s').
Proof. exact (@lem3770214 A (@IN (A -> Prop) s' s) (term255 A s s')). Qed.
Lemma lem3770216 {A : Type'} (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term256 A s s' t) = (term257 A s t s').
Proof. exact (eq_refl (term256 A s s' t)). Qed.
Lemma lem3770217 {A : Type'} (s : A -> Prop) (s' : type686 A) : (term258 A s s') = (term258 A s s').
Proof. exact (eq_refl (term258 A s s')). Qed.
Lemma lem3770218 {A : Type'} (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term259 A s s' t) = (term171 A s t s').
Proof. exact (MK_COMB (@lem3770217 A s' s) (@lem3770216 A s t s')). Qed.
Lemma lem3770219 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term260 A s s') = (term174 A s s').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3770218 A s t s')). Qed.
Lemma lem3770220 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770221 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term253 A s s') = (term176 A s s').
Proof. exact (MK_COMB (@lem3770220 A) (@lem3770219 A s s')). Qed.
Lemma lem3770222 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3770223 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term261 A s s') = (term262 A s s').
Proof. exact (MK_COMB (@lem3770222) (@lem3770221 A s s')). Qed.
Lemma lem3770224 {A : Type'} (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term256 A s s' t) = (term257 A s t s').
Proof. exact (eq_refl (term256 A s s' t)). Qed.
Lemma lem3770225 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term263 A s s') = (term255 A s s').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3770224 A s t s')). Qed.
Lemma lem3770226 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770227 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term264 A s s') = (term265 A s s').
Proof. exact (MK_COMB (@lem3770226 A) (@lem3770225 A s s')). Qed.
Lemma lem3770228 {A : Type'} (s : A -> Prop) (s' : type686 A) : (term258 A s s') = (term258 A s s').
Proof. exact (eq_refl (term258 A s s')). Qed.
Lemma lem3770229 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term254 A s s') = (term266 A s s').
Proof. exact (MK_COMB (@lem3770228 A s' s) (@lem3770227 A s s')). Qed.
Lemma lem3770230 {A : Type'} (s : type686 A) (s' : A -> Prop) : ((term253 A s s') = (term254 A s s')) = ((term176 A s s') = (term266 A s s')).
Proof. exact (MK_COMB (@lem3770223 A s s') (@lem3770229 A s s')). Qed.
Lemma lem3770231 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term176 A s s') = (term266 A s s').
Proof. exact (EQ_MP (@lem3770230 A s s') (@lem3770215 A s s')). Qed.
Lemma lem3770262 {A : Type'} (s : type686 A) : (term178 A s) = (term267 A s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3770231 A s s')). Qed.
Lemma lem3770263 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770264 {A : Type'} (s : type686 A) : (term179 A s) = (term268 A s).
Proof. exact (MK_COMB (@lem3770263 A) (@lem3770262 A s)). Qed.
Lemma lem3770289 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3770290 {A : Type'} (s : type686 A) : (term181 A s) = (term269 A s).
Proof. exact (MK_COMB (@lem3770289) (@lem3770264 A s)). Qed.
Lemma lem3770291 {A : Type'} (s : type686 A) : (term166 A s) = (term166 A s).
Proof. exact (eq_refl (term166 A s)). Qed.
Lemma lem3770292 {A : Type'} (s : type686 A) : (term183 A s) = (term270 A s).
Proof. exact (MK_COMB (@lem3770290 A s) (@lem3770291 A s)). Qed.
Lemma lem3770295 {A : Type'} (s : type686 A) : (term184 A s) = (term184 A s).
Proof. exact (eq_refl (term184 A s)). Qed.
Lemma lem3770296 {A : Type'} (s : type686 A) : (term185 A s) = (term271 A s).
Proof. exact (MK_COMB (@lem3770295 A s) (@lem3770292 A s)). Qed.
Lemma lem3770299 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3770300 {A : Type'} (s : type686 A) : (term201 A s) = (term272 A s).
Proof. exact (MK_COMB (@lem3770299) (@lem3770296 A s)). Qed.
Lemma lem3770314 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem3769941 A P Q) (@lem3769940 A P Q)). Qed.
Lemma lem3770315 {A : Type'} (P : Prop) (Q : type686 A) : (term224 A P Q) = (term225 A P Q).
Proof. exact (@lem3770314 (A -> Prop) P Q). Qed.
Lemma lem3770316 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term273 A x s s') = (term274 A x s s').
Proof. exact (@lem3770315 A (term275 A s' x s) (term276 A x s s')). Qed.
Lemma lem3770317 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term277 A x s s' t) = (term278 A x s t s').
Proof. exact (eq_refl (term277 A x s s' t)). Qed.
Lemma lem3770318 {A : Type'} (s : A -> Prop) (x : A -> Prop) (s' : type686 A) : (term279 A s x s') = (term279 A s x s').
Proof. exact (eq_refl (term279 A s x s')). Qed.
Lemma lem3770319 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term280 A x s s' t) = (term281 A x s t s').
Proof. exact (MK_COMB (@lem3770318 A s' x s) (@lem3770317 A x s t s')). Qed.
Lemma lem3770320 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term282 A x s s') = (term283 A x s s').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3770319 A x s t s')). Qed.
Lemma lem3770321 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770322 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term273 A x s s') = (term284 A x s s').
Proof. exact (MK_COMB (@lem3770321 A) (@lem3770320 A x s s')). Qed.
Lemma lem3770323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3770324 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term285 A x s s') = (term286 A x s s').
Proof. exact (MK_COMB (@lem3770323) (@lem3770322 A x s s')). Qed.
Lemma lem3770325 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term277 A x s s' t) = (term278 A x s t s').
Proof. exact (eq_refl (term277 A x s s' t)). Qed.
Lemma lem3770326 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term287 A x s s') = (term276 A x s s').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3770325 A x s t s')). Qed.
Lemma lem3770327 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770328 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term288 A x s s') = (term289 A x s s').
Proof. exact (MK_COMB (@lem3770327 A) (@lem3770326 A x s s')). Qed.
Lemma lem3770329 {A : Type'} (s : A -> Prop) (x : A -> Prop) (s' : type686 A) : (term279 A s x s') = (term279 A s x s').
Proof. exact (eq_refl (term279 A s x s')). Qed.
Lemma lem3770330 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term274 A x s s') = (term290 A x s s').
Proof. exact (MK_COMB (@lem3770329 A s' x s) (@lem3770328 A x s s')). Qed.
Lemma lem3770331 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : ((term273 A x s s') = (term274 A x s s')) = ((term284 A x s s') = (term290 A x s s')).
Proof. exact (MK_COMB (@lem3770324 A x s s') (@lem3770330 A x s s')). Qed.
Lemma lem3770332 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term284 A x s s') = (term290 A x s s').
Proof. exact (EQ_MP (@lem3770331 A x s s') (@lem3770316 A x s s')). Qed.
Lemma lem3770336 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term147 _83983 a s P) = (term148 _83983 a s P).
Proof. exact (EQ_MP (@lem3769935 _83983 a s P) (@lem3769934 _83983 a P s)). Qed.
Lemma lem3770337 {A : Type'} (a : A -> Prop) (s : type686 A) (P : type686 A) : (term291 A a s P) = (term292 A a s P).
Proof. exact (@lem3770336 (A -> Prop) a s P). Qed.
Lemma lem3770338 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term293 A x s s') = (term294 A x s s').
Proof. exact (@lem3770337 A x s (term295 A s')). Qed.
Lemma lem3770339 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term296 A s t) = (term172 A t s).
Proof. exact (eq_refl (term296 A s t)). Qed.
Lemma lem3770340 {A : Type'} (t : A -> Prop) (x : A -> Prop) (s : type686 A) : (term279 A t x s) = (term279 A t x s).
Proof. exact (eq_refl (term279 A t x s)). Qed.
Lemma lem3770341 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term297 A x s s' t) = (term278 A x s t s').
Proof. exact (MK_COMB (@lem3770340 A t x s) (@lem3770339 A t s')). Qed.
Lemma lem3770342 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term298 A x s s') = (term276 A x s s').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3770341 A x s t s')). Qed.
Lemma lem3770343 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770344 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term293 A x s s') = (term289 A x s s').
Proof. exact (MK_COMB (@lem3770343 A) (@lem3770342 A x s s')). Qed.
Lemma lem3770345 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3770346 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term299 A x s s') = (term300 A x s s').
Proof. exact (MK_COMB (@lem3770345) (@lem3770344 A x s s')). Qed.
Lemma lem3770347 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term296 A s x) = (term172 A x s).
Proof. exact (eq_refl (term296 A s x)). Qed.
Lemma lem3770348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3770349 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term301 A s x) = (term302 A x s).
Proof. exact (MK_COMB (@lem3770348) (@lem3770347 A x s)). Qed.
Lemma lem3770350 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term296 A s t) = (term172 A t s).
Proof. exact (eq_refl (term296 A s t)). Qed.
Lemma lem3770351 {A : Type'} (t : A -> Prop) (s : type686 A) : (term258 A t s) = (term258 A t s).
Proof. exact (eq_refl (term258 A t s)). Qed.
Lemma lem3770352 {A : Type'} (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term303 A s s' t) = (term257 A s t s').
Proof. exact (MK_COMB (@lem3770351 A t s) (@lem3770350 A t s')). Qed.
Lemma lem3770353 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term304 A s s') = (term255 A s s').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3770352 A s t s')). Qed.
Lemma lem3770354 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770355 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term305 A s s') = (term265 A s s').
Proof. exact (MK_COMB (@lem3770354 A) (@lem3770353 A s s')). Qed.
Lemma lem3770356 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term294 A x s s') = (term306 A x s s').
Proof. exact (MK_COMB (@lem3770349 A x s') (@lem3770355 A s s')). Qed.
Lemma lem3770357 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : ((term293 A x s s') = (term294 A x s s')) = ((term289 A x s s') = (term306 A x s s')).
Proof. exact (MK_COMB (@lem3770346 A x s s') (@lem3770356 A x s s')). Qed.
Lemma lem3770358 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term289 A x s s') = (term306 A x s s').
Proof. exact (EQ_MP (@lem3770357 A x s s') (@lem3770338 A x s s')). Qed.
Lemma lem3770391 {A : Type'} (s : A -> Prop) (x : A -> Prop) (s' : type686 A) : (term279 A s x s') = (term279 A s x s').
Proof. exact (eq_refl (term279 A s x s')). Qed.
Lemma lem3770392 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term290 A x s s') = (term307 A x s s').
Proof. exact (MK_COMB (@lem3770391 A s' x s) (@lem3770358 A x s s')). Qed.
Lemma lem3770395 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term284 A x s s') = (term307 A x s s').
Proof. exact (TRANS (@lem3770332 A x s s') (@lem3770392 A x s s')). Qed.
Lemma lem3770396 {A : Type'} (x : A -> Prop) (s : type686 A) : (term308 A x s) = (term309 A x s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3770395 A x s s')). Qed.
Lemma lem3770397 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770398 {A : Type'} (x : A -> Prop) (s : type686 A) : (term310 A x s) = (term311 A x s).
Proof. exact (MK_COMB (@lem3770397 A) (@lem3770396 A x s)). Qed.
Lemma lem3770400 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term147 _83983 a s P) = (term148 _83983 a s P).
Proof. exact (EQ_MP (@lem3769935 _83983 a s P) (@lem3769934 _83983 a P s)). Qed.
Lemma lem3770401 {A : Type'} (a : A -> Prop) (s : type686 A) (P : type686 A) : (term291 A a s P) = (term292 A a s P).
Proof. exact (@lem3770400 (A -> Prop) a s P). Qed.
Lemma lem3770402 {A : Type'} (x : A -> Prop) (s : type686 A) : (term312 A x s) = (term313 A x s).
Proof. exact (@lem3770401 A x s (term314 A x s)). Qed.
Lemma lem3770403 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term315 A x s s') = (term306 A x s s').
Proof. exact (eq_refl (term315 A x s s')). Qed.
Lemma lem3770404 {A : Type'} (s : A -> Prop) (x : A -> Prop) (s' : type686 A) : (term279 A s x s') = (term279 A s x s').
Proof. exact (eq_refl (term279 A s x s')). Qed.
Lemma lem3770405 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term316 A x s s') = (term307 A x s s').
Proof. exact (MK_COMB (@lem3770404 A s' x s) (@lem3770403 A x s s')). Qed.
Lemma lem3770406 {A : Type'} (x : A -> Prop) (s : type686 A) : (term317 A x s) = (term309 A x s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3770405 A x s s')). Qed.
Lemma lem3770407 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770408 {A : Type'} (x : A -> Prop) (s : type686 A) : (term312 A x s) = (term311 A x s).
Proof. exact (MK_COMB (@lem3770407 A) (@lem3770406 A x s)). Qed.
Lemma lem3770409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3770410 {A : Type'} (x : A -> Prop) (s : type686 A) : (term318 A x s) = (term319 A x s).
Proof. exact (MK_COMB (@lem3770409) (@lem3770408 A x s)). Qed.
Lemma lem3770411 {A : Type'} (s : type686 A) (x : A -> Prop) : (term320 A s x) = (term321 A s x).
Proof. exact (eq_refl (term320 A s x)). Qed.
Lemma lem3770412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3770413 {A : Type'} (s : type686 A) (x : A -> Prop) : (term322 A s x) = (term323 A s x).
Proof. exact (MK_COMB (@lem3770412) (@lem3770411 A s x)). Qed.
Lemma lem3770414 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term315 A x s s') = (term306 A x s s').
Proof. exact (eq_refl (term315 A x s s')). Qed.
Lemma lem3770415 {A : Type'} (s : A -> Prop) (s' : type686 A) : (term258 A s s') = (term258 A s s').
Proof. exact (eq_refl (term258 A s s')). Qed.
Lemma lem3770416 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term324 A x s s') = (term325 A x s s').
Proof. exact (MK_COMB (@lem3770415 A s' s) (@lem3770414 A x s s')). Qed.
Lemma lem3770417 {A : Type'} (x : A -> Prop) (s : type686 A) : (term326 A x s) = (term327 A x s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3770416 A x s s')). Qed.
Lemma lem3770418 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770419 {A : Type'} (x : A -> Prop) (s : type686 A) : (term328 A x s) = (term329 A x s).
Proof. exact (MK_COMB (@lem3770418 A) (@lem3770417 A x s)). Qed.
Lemma lem3770420 {A : Type'} (x : A -> Prop) (s : type686 A) : (term313 A x s) = (term330 A x s).
Proof. exact (MK_COMB (@lem3770413 A s x) (@lem3770419 A x s)). Qed.
Lemma lem3770421 {A : Type'} (x : A -> Prop) (s : type686 A) : ((term312 A x s) = (term313 A x s)) = ((term311 A x s) = (term330 A x s)).
Proof. exact (MK_COMB (@lem3770410 A x s) (@lem3770420 A x s)). Qed.
Lemma lem3770422 {A : Type'} (x : A -> Prop) (s : type686 A) : (term311 A x s) = (term330 A x s).
Proof. exact (EQ_MP (@lem3770421 A x s) (@lem3770402 A x s)). Qed.
Lemma lem3770428 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem1834 t)). Qed.
Lemma lem3770429 {A : Type'} (x : A -> Prop) : (term331 A x) = (@SUBSET A x x).
Proof. exact (@lem3770428 (@SUBSET A x x)). Qed.
Lemma lem3770430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3770431 {A : Type'} (x : A -> Prop) : (term332 A x) = (term333 A x).
Proof. exact (MK_COMB (@lem3770430) (@lem3770429 A x)). Qed.
Lemma lem3770460 {A : Type'} (s : type686 A) (x : A -> Prop) : (term265 A s x) = (term265 A s x).
Proof. exact (eq_refl (term265 A s x)). Qed.
Lemma lem3770461 {A : Type'} (s : type686 A) (x : A -> Prop) : (term321 A s x) = (term334 A s x).
Proof. exact (MK_COMB (@lem3770431 A x) (@lem3770460 A s x)). Qed.
Lemma lem3770464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3770465 {A : Type'} (s : type686 A) (x : A -> Prop) : (term323 A s x) = (term335 A s x).
Proof. exact (MK_COMB (@lem3770464) (@lem3770461 A s x)). Qed.
Lemma lem3770524 {A : Type'} (x : A -> Prop) (s : type686 A) : (term329 A x s) = (term329 A x s).
Proof. exact (eq_refl (term329 A x s)). Qed.
Lemma lem3770525 {A : Type'} (x : A -> Prop) (s : type686 A) : (term330 A x s) = (term336 A x s).
Proof. exact (MK_COMB (@lem3770465 A s x) (@lem3770524 A x s)). Qed.
Lemma lem3770528 {A : Type'} (x : A -> Prop) (s : type686 A) : (term311 A x s) = (term336 A x s).
Proof. exact (TRANS (@lem3770422 A x s) (@lem3770525 A x s)). Qed.
Lemma lem3770529 {A : Type'} (x : A -> Prop) (s : type686 A) : (term310 A x s) = (term336 A x s).
Proof. exact (TRANS (@lem3770398 A x s) (@lem3770528 A x s)). Qed.
Lemma lem3770530 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3770531 {A : Type'} (x : A -> Prop) (s : type686 A) : (term337 A x s) = (term338 A x s).
Proof. exact (MK_COMB (@lem3770530) (@lem3770529 A x s)). Qed.
Lemma lem3770533 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : (term339 _87274 s u) = (term340 _87274 s u).
Proof. exact (EQ_MP (@lem3356591 _87274 s u) (@lem3358011 _87274 s u)). Qed.
Lemma lem3770534 {A : Type'} (s : A -> Prop) (u : type686 A) : (term339 A s u) = (term340 A s u).
Proof. exact (@lem3770533 A s u). Qed.
Lemma lem3770535 {A : Type'} (x : A -> Prop) (s : type686 A) : (term339 A x s) = (term340 A x s).
Proof. exact (@lem3770534 A x s). Qed.
Lemma lem3770536 {A : Type'} : (@IN (A -> Prop)) = (@IN (A -> Prop)).
Proof. exact (eq_refl (@IN (A -> Prop))). Qed.
Lemma lem3770537 {A : Type'} (x : A -> Prop) (s : type686 A) : (term341 A x s) = (term342 A x s).
Proof. exact (MK_COMB (@lem3770536 A) (@lem3770535 A x s)). Qed.
Lemma lem3770538 {A : Type'} (x : A -> Prop) (s : type686 A) : (@INSERT (A -> Prop) x s) = (@INSERT (A -> Prop) x s).
Proof. exact (eq_refl (@INSERT (A -> Prop) x s)). Qed.
Lemma lem3770539 {A : Type'} (x : A -> Prop) (s : type686 A) : (term343 A x s) = (term344 A x s).
Proof. exact (MK_COMB (@lem3770537 A x s) (@lem3770538 A x s)). Qed.
Lemma lem3770540 {A : Type'} (x : A -> Prop) (s : type686 A) : (term345 A x s) = (term346 A x s).
Proof. exact (MK_COMB (@lem3770531 A x s) (@lem3770539 A x s)). Qed.
Lemma lem3770543 {A : Type'} (x : A -> Prop) (s : type686 A) : (term347 A x s) = (term347 A x s).
Proof. exact (eq_refl (term347 A x s)). Qed.
Lemma lem3770544 {A : Type'} (x : A -> Prop) (s : type686 A) : (term203 A x s) = (term348 A x s).
Proof. exact (MK_COMB (@lem3770543 A x s) (@lem3770540 A x s)). Qed.
Lemma lem3770547 {A : Type'} (x : A -> Prop) (s : type686 A) : (term205 A x s) = (term349 A x s).
Proof. exact (MK_COMB (@lem3770300 A s) (@lem3770544 A x s)). Qed.
Lemma lem3770550 {A : Type'} (x : A -> Prop) : (term207 A x) = (term350 A x).
Proof. exact (fun_ext (fun s : type686 A => @lem3770547 A x s)). Qed.
Lemma lem3770551 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3770552 {A : Type'} (x : A -> Prop) : (term209 A x) = (term351 A x).
Proof. exact (MK_COMB (@lem3770551 A) (@lem3770550 A x)). Qed.
Lemma lem3770577 {A : Type'} : (term211 A) = (term352 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3770552 A x)). Qed.
Lemma lem3770578 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770579 {A : Type'} : (term213 A) = (term353 A).
Proof. exact (MK_COMB (@lem3770578 A) (@lem3770577 A)). Qed.
Lemma lem3770584 {A : Type'} : (term215 A) = (term354 A).
Proof. exact (MK_COMB (@lem3770171 A) (@lem3770579 A)). Qed.
Lemma lem3770586 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3770587 {A : Type'} : (term354 A) = (term353 A).
Proof. exact (@lem3770586 (term353 A)). Qed.
Lemma lem3770774 {A : Type'} : (term215 A) = (term353 A).
Proof. exact (TRANS (@lem3770584 A) (@lem3770587 A)). Qed.
Lemma lem3770775 {A : Type'} : (term353 A) = (term215 A).
Proof. exact (SYM (@lem3770774 A)). Qed.
Lemma lem3770809 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem3769909 A x s (@lem3769908 A x s)). Qed.
Lemma lem3770810 {A : Type'} (x : A -> Prop) (s : type686 A) : ((@INSERT (A -> Prop) x s) = (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3770809 (A -> Prop) x s). Qed.
Lemma lem3770811 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3770812 {A : Type'} (x : A -> Prop) (s : type686 A) : (term355 A x s) = (~ False).
Proof. exact (MK_COMB (@lem3770811) (@lem3770810 A x s)). Qed.
Lemma lem3770814 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3770815 {A : Type'} (x : A -> Prop) (s : type686 A) : (term355 A x s) = True.
Proof. exact (TRANS (@lem3770812 A x s) (@lem3770814)). Qed.
Lemma lem3770816 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3770817 {A : Type'} (x : A -> Prop) (s : type686 A) : (term347 A x s) = (imp True).
Proof. exact (MK_COMB (@lem3770816) (@lem3770815 A x s)). Qed.
Lemma lem3770837 (q : Prop) (p : Prop) (r : Prop) : (term121 p q r) = (term122 q p r).
Proof. exact (or_elim (@lem3769796 p) (fun h0 : p = True => @lem3769899 q r p h0) (fun h0 : p = False => @lem3769898 q r p h0)). Qed.
Lemma lem3770838 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term325 A x s s') = (term356 A x s s').
Proof. exact (@lem3770837 (term172 A x s') (@IN (A -> Prop) s' s) (term265 A s s')). Qed.
Lemma lem3770855 {A : Type'} (x : A -> Prop) (s : type686 A) : (term327 A x s) = (term357 A x s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3770838 A x s s')). Qed.
Lemma lem3770856 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770857 {A : Type'} (x : A -> Prop) (s : type686 A) : (term329 A x s) = (term358 A x s).
Proof. exact (MK_COMB (@lem3770856 A) (@lem3770855 A x s)). Qed.
Lemma lem3770859 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem3769926 A P Q) (@lem3769925 A P Q)). Qed.
Lemma lem3770860 {A : Type'} (P : type686 A) (Q : type686 A) : (term359 A P Q) = (term360 A P Q).
Proof. exact (@lem3770859 (A -> Prop) P Q). Qed.
Lemma lem3770861 {A : Type'} (x : A -> Prop) (s : type686 A) : (term361 A x s) = (term362 A x s).
Proof. exact (@lem3770860 A (term363 A s x) (term267 A s)). Qed.
Lemma lem3770862 {A : Type'} (s : type686 A) (x : A -> Prop) (s' : A -> Prop) : (term364 A s x s') = (term365 A s x s').
Proof. exact (eq_refl (term364 A s x s')). Qed.
Lemma lem3770863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3770864 {A : Type'} (s : type686 A) (x : A -> Prop) (s' : A -> Prop) : (term366 A s x s') = (term367 A s x s').
Proof. exact (MK_COMB (@lem3770863) (@lem3770862 A s x s')). Qed.
Lemma lem3770865 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term368 A s s') = (term266 A s s').
Proof. exact (eq_refl (term368 A s s')). Qed.
Lemma lem3770866 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term369 A x s s') = (term356 A x s s').
Proof. exact (MK_COMB (@lem3770864 A s x s') (@lem3770865 A s s')). Qed.
Lemma lem3770867 {A : Type'} (x : A -> Prop) (s : type686 A) : (term370 A x s) = (term357 A x s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3770866 A x s s')). Qed.
Lemma lem3770868 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770869 {A : Type'} (x : A -> Prop) (s : type686 A) : (term361 A x s) = (term358 A x s).
Proof. exact (MK_COMB (@lem3770868 A) (@lem3770867 A x s)). Qed.
Lemma lem3770870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3770871 {A : Type'} (x : A -> Prop) (s : type686 A) : (term371 A x s) = (term372 A x s).
Proof. exact (MK_COMB (@lem3770870) (@lem3770869 A x s)). Qed.
Lemma lem3770872 {A : Type'} (s : type686 A) (x : A -> Prop) (s' : A -> Prop) : (term364 A s x s') = (term365 A s x s').
Proof. exact (eq_refl (term364 A s x s')). Qed.
Lemma lem3770873 {A : Type'} (s : type686 A) (x : A -> Prop) : (term373 A s x) = (term363 A s x).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3770872 A s x s')). Qed.
Lemma lem3770874 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770875 {A : Type'} (s : type686 A) (x : A -> Prop) : (term374 A s x) = (term375 A s x).
Proof. exact (MK_COMB (@lem3770874 A) (@lem3770873 A s x)). Qed.
Lemma lem3770876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3770877 {A : Type'} (s : type686 A) (x : A -> Prop) : (term376 A s x) = (term377 A s x).
Proof. exact (MK_COMB (@lem3770876) (@lem3770875 A s x)). Qed.
Lemma lem3770878 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term368 A s s') = (term266 A s s').
Proof. exact (eq_refl (term368 A s s')). Qed.
Lemma lem3770879 {A : Type'} (s : type686 A) : (term378 A s) = (term267 A s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3770878 A s s')). Qed.
Lemma lem3770880 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770881 {A : Type'} (s : type686 A) : (term379 A s) = (term268 A s).
Proof. exact (MK_COMB (@lem3770880 A) (@lem3770879 A s)). Qed.
Lemma lem3770882 {A : Type'} (x : A -> Prop) (s : type686 A) : (term362 A x s) = (term380 A x s).
Proof. exact (MK_COMB (@lem3770877 A s x) (@lem3770881 A s)). Qed.
Lemma lem3770883 {A : Type'} (x : A -> Prop) (s : type686 A) : ((term361 A x s) = (term362 A x s)) = ((term358 A x s) = (term380 A x s)).
Proof. exact (MK_COMB (@lem3770871 A x s) (@lem3770882 A x s)). Qed.
Lemma lem3770884 {A : Type'} (x : A -> Prop) (s : type686 A) : (term358 A x s) = (term380 A x s).
Proof. exact (EQ_MP (@lem3770883 A x s) (@lem3770861 A x s)). Qed.
Lemma lem3770909 {A : Type'} (x : A -> Prop) (s : type686 A) : (term329 A x s) = (term380 A x s).
Proof. exact (TRANS (@lem3770857 A x s) (@lem3770884 A x s)). Qed.
Lemma lem3770910 {A : Type'} (s : type686 A) (x : A -> Prop) : (term335 A s x) = (term335 A s x).
Proof. exact (eq_refl (term335 A s x)). Qed.
Lemma lem3770911 {A : Type'} (x : A -> Prop) (s : type686 A) : (term336 A x s) = (term381 A x s).
Proof. exact (MK_COMB (@lem3770910 A s x) (@lem3770909 A x s)). Qed.
Lemma lem3770914 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3770915 {A : Type'} (x : A -> Prop) (s : type686 A) : (term338 A x s) = (term382 A x s).
Proof. exact (MK_COMB (@lem3770914) (@lem3770911 A x s)). Qed.
Lemma lem3770916 {A : Type'} (x : A -> Prop) (s : type686 A) : (term344 A x s) = (term344 A x s).
Proof. exact (eq_refl (term344 A x s)). Qed.
Lemma lem3770917 {A : Type'} (x : A -> Prop) (s : type686 A) : (term346 A x s) = (term383 A x s).
Proof. exact (MK_COMB (@lem3770915 A x s) (@lem3770916 A x s)). Qed.
Lemma lem3770920 {A : Type'} (x : A -> Prop) (s : type686 A) : (term348 A x s) = (term384 A x s).
Proof. exact (MK_COMB (@lem3770817 A x s) (@lem3770917 A x s)). Qed.
Lemma lem3770922 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3770923 {A : Type'} (x : A -> Prop) (s : type686 A) : (term384 A x s) = (term383 A x s).
Proof. exact (@lem3770922 (term383 A x s)). Qed.
Lemma lem3770962 {A : Type'} (x : A -> Prop) (s : type686 A) : (term348 A x s) = (term383 A x s).
Proof. exact (TRANS (@lem3770920 A x s) (@lem3770923 A x s)). Qed.
Lemma lem3770963 {A : Type'} (s : type686 A) : (term272 A s) = (term272 A s).
Proof. exact (eq_refl (term272 A s)). Qed.
Lemma lem3770964 {A : Type'} (x : A -> Prop) (s : type686 A) : (term349 A x s) = (term385 A x s).
Proof. exact (MK_COMB (@lem3770963 A s) (@lem3770962 A x s)). Qed.
Lemma lem3770967 {A : Type'} (x : A -> Prop) : (term350 A x) = (term386 A x).
Proof. exact (fun_ext (fun s : type686 A => @lem3770964 A x s)). Qed.
Lemma lem3770968 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3770969 {A : Type'} (x : A -> Prop) : (term351 A x) = (term387 A x).
Proof. exact (MK_COMB (@lem3770968 A) (@lem3770967 A x)). Qed.
Lemma lem3770974 {A : Type'} : (term352 A) = (term388 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3770969 A x)). Qed.
Lemma lem3770975 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3770976 {A : Type'} : (term353 A) = (term389 A).
Proof. exact (MK_COMB (@lem3770975 A) (@lem3770974 A)). Qed.
Lemma lem3770981 {A : Type'} : (term389 A) = (term353 A).
Proof. exact (SYM (@lem3770976 A)). Qed.
Lemma lem3770982 {A : Type'} : term390 A.
Proof. exact (proj2 (@lem3258568 A)). Qed.
Lemma lem3770983 {A : Type'} (s : A -> Prop) : term391 A s.
Proof. exact (@lem3770982 A s). Qed.
Lemma lem3770984 {A : Type'} (s : A -> Prop) : (term391 A s) = ((@INTER A s (@UNIV A)) = s).
Proof. exact (eq_refl (term391 A s)). Qed.
Lemma lem3770990 {A : Type'} (x : A) : term392 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3770991 {A : Type'} (x : A) : (term392 A x) = (term393 A x).
Proof. exact (eq_refl (term392 A x)). Qed.
Lemma lem3770992 {A : Type'} (x : A) : term393 A x.
Proof. exact (EQ_MP (@lem3770991 A x) (@lem3770990 A x)). Qed.
Lemma lem3770993 {A : Type'} (x : A) (y : A) : term394 A x y.
Proof. exact (@lem3770992 A x y). Qed.
Lemma lem3770994 {A : Type'} (y : A) (x : A) : (term394 A x y) = (term395 A y x).
Proof. exact (eq_refl (term394 A x y)). Qed.
Lemma lem3770995 {A : Type'} (y : A) (x : A) : term395 A y x.
Proof. exact (EQ_MP (@lem3770994 A y x) (@lem3770993 A x y)). Qed.
Lemma lem3770996 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term396 A y x s.
Proof. exact (@lem3770995 A y x s). Qed.
Lemma lem3770997 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term396 A y x s) = ((term397 A x y s) = (term398 A y x s)).
Proof. exact (eq_refl (term396 A y x s)). Qed.
Lemma lem3771006 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3771007 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem3771008 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@eq ((A -> Prop) -> Prop) f) = (@eq ((A -> Prop) -> Prop) (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3771007 A) (@lem3771006 A f h1)). Qed.
Lemma lem3771009 {A : Type'} : (@EMPTY (A -> Prop)) = (@EMPTY (A -> Prop)).
Proof. exact (eq_refl (@EMPTY (A -> Prop))). Qed.
Lemma lem3771010 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (f = (@EMPTY (A -> Prop))) = ((@EMPTY (A -> Prop)) = (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3771008 A f h1) (@lem3771009 A)). Qed.
Lemma lem3771012 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3771013 {A : Type'} (x : type686 A) : (x = x) = True.
Proof. exact (@lem3771012 (type686 A) x). Qed.
Lemma lem3771014 {A : Type'} : ((@EMPTY (A -> Prop)) = (@EMPTY (A -> Prop))) = True.
Proof. exact (@lem3771013 A (@EMPTY (A -> Prop))). Qed.
Lemma lem3771015 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (f = (@EMPTY (A -> Prop))) = True.
Proof. exact (TRANS (@lem3771010 A f h1) (@lem3771014 A)). Qed.
Lemma lem3771016 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3771017 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term112 A f) = (~ True).
Proof. exact (MK_COMB (@lem3771016) (@lem3771015 A f h1)). Qed.
Lemma lem3771019 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3771020 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term112 A f) = False.
Proof. exact (TRANS (@lem3771017 A f h1) (@lem3771019)). Qed.
Lemma lem3771021 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771022 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term184 A f) = (imp False).
Proof. exact (MK_COMB (@lem3771021) (@lem3771020 A f h1)). Qed.
Lemma lem3771032 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3771033 {A : Type'} (s : A -> Prop) : (@IN (A -> Prop) s) = (@IN (A -> Prop) s).
Proof. exact (eq_refl (@IN (A -> Prop) s)). Qed.
Lemma lem3771034 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@IN (A -> Prop) s f) = (@IN (A -> Prop) s (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3771033 A s) (@lem3771032 A f h1)). Qed.
Lemma lem3771035 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771036 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term258 A s f) = (term231 A s).
Proof. exact (MK_COMB (@lem3771035) (@lem3771034 A s f h1)). Qed.
Lemma lem3771044 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3771045 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t) = (@IN (A -> Prop) t).
Proof. exact (eq_refl (@IN (A -> Prop) t)). Qed.
Lemma lem3771046 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@IN (A -> Prop) t f) = (@IN (A -> Prop) t (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3771045 A t) (@lem3771044 A f h1)). Qed.
Lemma lem3771047 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771048 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term258 A t f) = (term231 A t).
Proof. exact (MK_COMB (@lem3771047) (@lem3771046 A t f h1)). Qed.
Lemma lem3771051 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term172 A t s) = (term172 A t s).
Proof. exact (eq_refl (term172 A t s)). Qed.
Lemma lem3771052 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term257 A f t s) = (term230 A t s).
Proof. exact (MK_COMB (@lem3771048 A t f h1) (@lem3771051 A t s)). Qed.
Lemma lem3771055 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term255 A f s) = (term228 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3771052 A t s f h1)). Qed.
Lemma lem3771056 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3771057 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term265 A f s) = (term241 A s).
Proof. exact (MK_COMB (@lem3771056 A) (@lem3771055 A s f h1)). Qed.
Lemma lem3771062 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term266 A f s) = (term242 A s).
Proof. exact (MK_COMB (@lem3771036 A s f h1) (@lem3771057 A s f h1)). Qed.
Lemma lem3771065 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term267 A f) = (term244 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3771062 A s f h1)). Qed.
Lemma lem3771066 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3771067 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term268 A f) = (term246 A).
Proof. exact (MK_COMB (@lem3771066 A) (@lem3771065 A f h1)). Qed.
Lemma lem3771072 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771073 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term269 A f) = (term248 A).
Proof. exact (MK_COMB (@lem3771072) (@lem3771067 A f h1)). Qed.
Lemma lem3771075 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3771076 {A : Type'} : (@INTERS A) = (@INTERS A).
Proof. exact (eq_refl (@INTERS A)). Qed.
Lemma lem3771077 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@INTERS A f) = (@INTERS A (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3771076 A) (@lem3771075 A f h1)). Qed.
Lemma lem3771079 {A : Type'} : (@INTERS A (@EMPTY (A -> Prop))) = (@UNIV A).
Proof. exact (EQ_MP (@lem3354637 A) (@lem3354697 A)). Qed.
Lemma lem3771080 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@INTERS A f) = (@UNIV A).
Proof. exact (TRANS (@lem3771077 A f h1) (@lem3771079 A)). Qed.
Lemma lem3771081 {A : Type'} : (@IN (A -> Prop)) = (@IN (A -> Prop)).
Proof. exact (eq_refl (@IN (A -> Prop))). Qed.
Lemma lem3771082 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term399 A f) = (@IN (A -> Prop) (@UNIV A)).
Proof. exact (MK_COMB (@lem3771081 A) (@lem3771080 A f h1)). Qed.
Lemma lem3771084 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3771085 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term166 A f) = (@IN (A -> Prop) (@UNIV A) (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3771082 A f h1) (@lem3771084 A f h1)). Qed.
Lemma lem3771086 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term270 A f) = (term400 A).
Proof. exact (MK_COMB (@lem3771073 A f h1) (@lem3771085 A f h1)). Qed.
Lemma lem3771089 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term271 A f) = (term401 A).
Proof. exact (MK_COMB (@lem3771022 A f h1) (@lem3771086 A f h1)). Qed.
Lemma lem3771091 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3771092 {A : Type'} : (term401 A) = True.
Proof. exact (@lem3771091 (term400 A)). Qed.
Lemma lem3771093 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term271 A f) = True.
Proof. exact (TRANS (@lem3771089 A f h1) (@lem3771092 A)). Qed.
Lemma lem3771094 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771095 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term272 A f) = (imp True).
Proof. exact (MK_COMB (@lem3771094) (@lem3771093 A f h1)). Qed.
Lemma lem3771109 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3771110 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t) = (@IN (A -> Prop) t).
Proof. exact (eq_refl (@IN (A -> Prop) t)). Qed.
Lemma lem3771111 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@IN (A -> Prop) t f) = (@IN (A -> Prop) t (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3771110 A t) (@lem3771109 A f h1)). Qed.
Lemma lem3771112 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771113 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term258 A t f) = (term231 A t).
Proof. exact (MK_COMB (@lem3771112) (@lem3771111 A t f h1)). Qed.
Lemma lem3771116 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term172 A t s) = (term172 A t s).
Proof. exact (eq_refl (term172 A t s)). Qed.
Lemma lem3771117 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term257 A f t s) = (term230 A t s).
Proof. exact (MK_COMB (@lem3771113 A t f h1) (@lem3771116 A t s)). Qed.
Lemma lem3771120 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term255 A f s) = (term228 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3771117 A t s f h1)). Qed.
Lemma lem3771121 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3771122 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term265 A f s) = (term241 A s).
Proof. exact (MK_COMB (@lem3771121 A) (@lem3771120 A s f h1)). Qed.
Lemma lem3771127 {A : Type'} (s : A -> Prop) : (term333 A s) = (term333 A s).
Proof. exact (eq_refl (term333 A s)). Qed.
Lemma lem3771128 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term334 A f s) = (term402 A s).
Proof. exact (MK_COMB (@lem3771127 A s) (@lem3771122 A s f h1)). Qed.
Lemma lem3771131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3771132 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term335 A f s) = (term403 A s).
Proof. exact (MK_COMB (@lem3771131) (@lem3771128 A s f h1)). Qed.
Lemma lem3771142 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3771143 {A : Type'} (s' : A -> Prop) : (@IN (A -> Prop) s') = (@IN (A -> Prop) s').
Proof. exact (eq_refl (@IN (A -> Prop) s')). Qed.
Lemma lem3771144 {A : Type'} (s' : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@IN (A -> Prop) s' f) = (@IN (A -> Prop) s' (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3771143 A s') (@lem3771142 A f h1)). Qed.
Lemma lem3771145 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771146 {A : Type'} (s' : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term258 A s' f) = (term231 A s').
Proof. exact (MK_COMB (@lem3771145) (@lem3771144 A s' f h1)). Qed.
Lemma lem3771149 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term172 A s s') = (term172 A s s').
Proof. exact (eq_refl (term172 A s s')). Qed.
Lemma lem3771150 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term365 A f s s') = (term404 A s s').
Proof. exact (MK_COMB (@lem3771146 A s' f h1) (@lem3771149 A s s')). Qed.
Lemma lem3771153 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term363 A f s) = (term405 A s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3771150 A s s' f h1)). Qed.
Lemma lem3771154 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3771155 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term375 A f s) = (term406 A s).
Proof. exact (MK_COMB (@lem3771154 A) (@lem3771153 A s f h1)). Qed.
Lemma lem3771160 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3771161 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term377 A f s) = (term407 A s).
Proof. exact (MK_COMB (@lem3771160) (@lem3771155 A s f h1)). Qed.
Lemma lem3771169 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3771170 {A : Type'} (s : A -> Prop) : (@IN (A -> Prop) s) = (@IN (A -> Prop) s).
Proof. exact (eq_refl (@IN (A -> Prop) s)). Qed.
Lemma lem3771171 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@IN (A -> Prop) s f) = (@IN (A -> Prop) s (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3771170 A s) (@lem3771169 A f h1)). Qed.
Lemma lem3771172 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771173 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term258 A s f) = (term231 A s).
Proof. exact (MK_COMB (@lem3771172) (@lem3771171 A s f h1)). Qed.
Lemma lem3771181 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3771182 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t) = (@IN (A -> Prop) t).
Proof. exact (eq_refl (@IN (A -> Prop) t)). Qed.
Lemma lem3771183 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@IN (A -> Prop) t f) = (@IN (A -> Prop) t (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3771182 A t) (@lem3771181 A f h1)). Qed.
Lemma lem3771184 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771185 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term258 A t f) = (term231 A t).
Proof. exact (MK_COMB (@lem3771184) (@lem3771183 A t f h1)). Qed.
Lemma lem3771188 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term172 A t s) = (term172 A t s).
Proof. exact (eq_refl (term172 A t s)). Qed.
Lemma lem3771189 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term257 A f t s) = (term230 A t s).
Proof. exact (MK_COMB (@lem3771185 A t f h1) (@lem3771188 A t s)). Qed.
Lemma lem3771192 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term255 A f s) = (term228 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3771189 A t s f h1)). Qed.
Lemma lem3771193 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3771194 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term265 A f s) = (term241 A s).
Proof. exact (MK_COMB (@lem3771193 A) (@lem3771192 A s f h1)). Qed.
Lemma lem3771199 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term266 A f s) = (term242 A s).
Proof. exact (MK_COMB (@lem3771173 A s f h1) (@lem3771194 A s f h1)). Qed.
Lemma lem3771202 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term267 A f) = (term244 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3771199 A s f h1)). Qed.
Lemma lem3771203 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3771204 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term268 A f) = (term246 A).
Proof. exact (MK_COMB (@lem3771203 A) (@lem3771202 A f h1)). Qed.
Lemma lem3771209 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term380 A s f) = (term408 A s).
Proof. exact (MK_COMB (@lem3771161 A s f h1) (@lem3771204 A f h1)). Qed.
Lemma lem3771212 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term381 A s f) = (term409 A s).
Proof. exact (MK_COMB (@lem3771132 A s f h1) (@lem3771209 A s f h1)). Qed.
Lemma lem3771215 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771216 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term382 A s f) = (term410 A s).
Proof. exact (MK_COMB (@lem3771215) (@lem3771212 A s f h1)). Qed.
Lemma lem3771218 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term397 A x y s) = (term398 A y x s).
Proof. exact (EQ_MP (@lem3770997 A y x s) (@lem3770996 A y x s)). Qed.
Lemma lem3771219 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : type686 A) : (term275 A x y s) = (term411 A y x s).
Proof. exact (@lem3771218 (A -> Prop) y x s). Qed.
Lemma lem3771220 {A : Type'} (s : A -> Prop) (f : type686 A) : (term344 A s f) = (term412 A s f).
Proof. exact (@lem3771219 A s (term340 A s f) f). Qed.
Lemma lem3771226 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3771227 {A : Type'} : (@INTERS A) = (@INTERS A).
Proof. exact (eq_refl (@INTERS A)). Qed.
Lemma lem3771228 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@INTERS A f) = (@INTERS A (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3771227 A) (@lem3771226 A f h1)). Qed.
Lemma lem3771230 {A : Type'} : (@INTERS A (@EMPTY (A -> Prop))) = (@UNIV A).
Proof. exact (EQ_MP (@lem3354637 A) (@lem3354697 A)). Qed.
Lemma lem3771231 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@INTERS A f) = (@UNIV A).
Proof. exact (TRANS (@lem3771228 A f h1) (@lem3771230 A)). Qed.
Lemma lem3771232 {A : Type'} (s : A -> Prop) : (@INTER A s) = (@INTER A s).
Proof. exact (eq_refl (@INTER A s)). Qed.
Lemma lem3771233 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term340 A s f) = (@INTER A s (@UNIV A)).
Proof. exact (MK_COMB (@lem3771232 A s) (@lem3771231 A f h1)). Qed.
Lemma lem3771235 {A : Type'} (s : A -> Prop) : (@INTER A s (@UNIV A)) = s.
Proof. exact (EQ_MP (@lem3770984 A s) (@lem3770983 A s)). Qed.
Lemma lem3771236 {A : Type'} (s : A -> Prop) : (@INTER A s (@UNIV A)) = s.
Proof. exact (@lem3771235 A s). Qed.
Lemma lem3771237 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term340 A s f) = s.
Proof. exact (TRANS (@lem3771233 A s f h1) (@lem3771236 A s)). Qed.
Lemma lem3771238 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3771239 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term413 A s f) = (@eq (A -> Prop) s).
Proof. exact (MK_COMB (@lem3771238 A) (@lem3771237 A s f h1)). Qed.
Lemma lem3771240 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3771241 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : ((term340 A s f) = s) = (s = s).
Proof. exact (MK_COMB (@lem3771239 A s f h1) (@lem3771240 A s)). Qed.
Lemma lem3771243 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3771244 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem3771243 (A -> Prop) x). Qed.
Lemma lem3771245 {A : Type'} (s : A -> Prop) : (s = s) = True.
Proof. exact (@lem3771244 A s). Qed.
Lemma lem3771246 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : ((term340 A s f) = s) = True.
Proof. exact (TRANS (@lem3771241 A s f h1) (@lem3771245 A s)). Qed.
Lemma lem3771247 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3771248 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term414 A f s) = (or True).
Proof. exact (MK_COMB (@lem3771247) (@lem3771246 A s f h1)). Qed.
Lemma lem3771250 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3771251 {A : Type'} : (@INTERS A) = (@INTERS A).
Proof. exact (eq_refl (@INTERS A)). Qed.
Lemma lem3771252 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@INTERS A f) = (@INTERS A (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3771251 A) (@lem3771250 A f h1)). Qed.
Lemma lem3771254 {A : Type'} : (@INTERS A (@EMPTY (A -> Prop))) = (@UNIV A).
Proof. exact (EQ_MP (@lem3354637 A) (@lem3354697 A)). Qed.
Lemma lem3771255 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@INTERS A f) = (@UNIV A).
Proof. exact (TRANS (@lem3771252 A f h1) (@lem3771254 A)). Qed.
Lemma lem3771256 {A : Type'} (s : A -> Prop) : (@INTER A s) = (@INTER A s).
Proof. exact (eq_refl (@INTER A s)). Qed.
Lemma lem3771257 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term340 A s f) = (@INTER A s (@UNIV A)).
Proof. exact (MK_COMB (@lem3771256 A s) (@lem3771255 A f h1)). Qed.
Lemma lem3771259 {A : Type'} (s : A -> Prop) : (@INTER A s (@UNIV A)) = s.
Proof. exact (EQ_MP (@lem3770984 A s) (@lem3770983 A s)). Qed.
Lemma lem3771260 {A : Type'} (s : A -> Prop) : (@INTER A s (@UNIV A)) = s.
Proof. exact (@lem3771259 A s). Qed.
Lemma lem3771261 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term340 A s f) = s.
Proof. exact (TRANS (@lem3771257 A s f h1) (@lem3771260 A s)). Qed.
Lemma lem3771262 {A : Type'} : (@IN (A -> Prop)) = (@IN (A -> Prop)).
Proof. exact (eq_refl (@IN (A -> Prop))). Qed.
Lemma lem3771263 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term342 A s f) = (@IN (A -> Prop) s).
Proof. exact (MK_COMB (@lem3771262 A) (@lem3771261 A s f h1)). Qed.
Lemma lem3771265 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3771266 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term415 A s f) = (@IN (A -> Prop) s (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3771263 A s f h1) (@lem3771265 A f h1)). Qed.
Lemma lem3771267 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term412 A s f) = (term416 A s).
Proof. exact (MK_COMB (@lem3771248 A s f h1) (@lem3771266 A s f h1)). Qed.
Lemma lem3771269 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem3771270 {A : Type'} (s : A -> Prop) : (term416 A s) = True.
Proof. exact (@lem3771269 (@IN (A -> Prop) s (@EMPTY (A -> Prop)))). Qed.
Lemma lem3771271 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term412 A s f) = True.
Proof. exact (TRANS (@lem3771267 A s f h1) (@lem3771270 A s)). Qed.
Lemma lem3771272 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term344 A s f) = True.
Proof. exact (TRANS (@lem3771220 A s f) (@lem3771271 A s f h1)). Qed.
Lemma lem3771273 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term383 A s f) = (term417 A s).
Proof. exact (MK_COMB (@lem3771216 A s f h1) (@lem3771272 A s f h1)). Qed.
Lemma lem3771275 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3771276 {A : Type'} (s : A -> Prop) : (term417 A s) = True.
Proof. exact (@lem3771275 (term409 A s)). Qed.
Lemma lem3771277 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term383 A s f) = True.
Proof. exact (TRANS (@lem3771273 A s f h1) (@lem3771276 A s)). Qed.
Lemma lem3771278 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term385 A s f) = (True -> True).
Proof. exact (MK_COMB (@lem3771095 A f h1) (@lem3771277 A s f h1)). Qed.
Lemma lem3771280 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3771281 : (True -> True) = True.
Proof. exact (@lem3771280 True). Qed.
Lemma lem3771282 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term385 A s f) = True.
Proof. exact (TRANS (@lem3771278 A s f h1) (@lem3771281)). Qed.
Lemma lem3771283 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : True = (term385 A s f).
Proof. exact (SYM (@lem3771282 A s f h1)). Qed.
Lemma lem3771284 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : term385 A s f.
Proof. exact (EQ_MP (@lem3771283 A s f h1) (@lem0)). Qed.
Lemma lem3771293 {A : Type'} (x : A) : term392 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3771294 {A : Type'} (x : A) : (term392 A x) = (term393 A x).
Proof. exact (eq_refl (term392 A x)). Qed.
Lemma lem3771295 {A : Type'} (x : A) : term393 A x.
Proof. exact (EQ_MP (@lem3771294 A x) (@lem3771293 A x)). Qed.
Lemma lem3771296 {A : Type'} (x : A) (y : A) : term394 A x y.
Proof. exact (@lem3771295 A x y). Qed.
Lemma lem3771297 {A : Type'} (y : A) (x : A) : (term394 A x y) = (term395 A y x).
Proof. exact (eq_refl (term394 A x y)). Qed.
Lemma lem3771298 {A : Type'} (y : A) (x : A) : term395 A y x.
Proof. exact (EQ_MP (@lem3771297 A y x) (@lem3771296 A x y)). Qed.
Lemma lem3771299 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term396 A y x s.
Proof. exact (@lem3771298 A y x s). Qed.
Lemma lem3771300 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term396 A y x s) = ((term397 A x y s) = (term398 A y x s)).
Proof. exact (eq_refl (term396 A y x s)). Qed.
Lemma lem3771302 {A : Type'} (f : type686 A) : term418 A f.
Proof. exact (@lem82 (f = (@EMPTY (A -> Prop)))). Qed.
Lemma lem3771320 {A : Type'} (f : type686 A) (h1 : term112 A f) : (f = (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3771302 A f (@lem3769779 A f h1)). Qed.
Lemma lem3771321 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3771322 {A : Type'} (f : type686 A) (h1 : term112 A f) : (term112 A f) = (~ False).
Proof. exact (MK_COMB (@lem3771321) (@lem3771320 A f h1)). Qed.
Lemma lem3771324 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3771325 {A : Type'} (f : type686 A) (h1 : term112 A f) : (term112 A f) = True.
Proof. exact (TRANS (@lem3771322 A f h1) (@lem3771324)). Qed.
Lemma lem3771326 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771327 {A : Type'} (f : type686 A) (h1 : term112 A f) : (term184 A f) = (imp True).
Proof. exact (MK_COMB (@lem3771326) (@lem3771325 A f h1)). Qed.
Lemma lem3771344 {A : Type'} (f : type686 A) : (term270 A f) = (term270 A f).
Proof. exact (eq_refl (term270 A f)). Qed.
Lemma lem3771345 {A : Type'} (f : type686 A) (h1 : term112 A f) : (term271 A f) = (term419 A f).
Proof. exact (MK_COMB (@lem3771327 A f h1) (@lem3771344 A f)). Qed.
Lemma lem3771347 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3771348 {A : Type'} (f : type686 A) : (term419 A f) = (term270 A f).
Proof. exact (@lem3771347 (term270 A f)). Qed.
Lemma lem3771365 {A : Type'} (f : type686 A) (h1 : term112 A f) : (term271 A f) = (term270 A f).
Proof. exact (TRANS (@lem3771345 A f h1) (@lem3771348 A f)). Qed.
Lemma lem3771366 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771367 {A : Type'} (f : type686 A) (h1 : term112 A f) : (term272 A f) = (term420 A f).
Proof. exact (MK_COMB (@lem3771366) (@lem3771365 A f h1)). Qed.
Lemma lem3771407 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term397 A x y s) = (term398 A y x s).
Proof. exact (EQ_MP (@lem3771300 A y x s) (@lem3771299 A y x s)). Qed.
Lemma lem3771408 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : type686 A) : (term275 A x y s) = (term411 A y x s).
Proof. exact (@lem3771407 (A -> Prop) y x s). Qed.
Lemma lem3771409 {A : Type'} (s : A -> Prop) (f : type686 A) : (term344 A s f) = (term412 A s f).
Proof. exact (@lem3771408 A s (term340 A s f) f). Qed.
Lemma lem3771414 {A : Type'} (s : A -> Prop) (f : type686 A) : (term382 A s f) = (term382 A s f).
Proof. exact (eq_refl (term382 A s f)). Qed.
Lemma lem3771415 {A : Type'} (s : A -> Prop) (f : type686 A) : (term383 A s f) = (term421 A s f).
Proof. exact (MK_COMB (@lem3771414 A s f) (@lem3771409 A s f)). Qed.
Lemma lem3771418 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) : (term385 A s f) = (term422 A s f).
Proof. exact (MK_COMB (@lem3771367 A f h1) (@lem3771415 A s f)). Qed.
Lemma lem3771421 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) : (term422 A s f) = (term385 A s f).
Proof. exact (SYM (@lem3771418 A s f h1)). Qed.
Lemma lem3771422 {A : Type'} (f : type686 A) (h1 : term270 A f) : term270 A f.
Proof. exact (h1). Qed.
Lemma lem3771423 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term381 A s f) : term381 A s f.
Proof. exact (h1). Qed.
Lemma lem3771424 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term380 A s f) : term380 A s f.
Proof. exact (h1). Qed.
Lemma lem3771425 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term334 A f s) : term334 A f s.
Proof. exact (h1). Qed.
Lemma lem3771426 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) : term265 A f s.
Proof. exact (h1). Qed.
Lemma lem3771427 {A : Type'} (s : A -> Prop) (h1 : @SUBSET A s s) : @SUBSET A s s.
Proof. exact (h1). Qed.
Lemma lem3771428 {A : Type'} (f : type686 A) (h1 : term268 A f) : term268 A f.
Proof. exact (h1). Qed.
Lemma lem3771429 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term375 A f s) : term375 A f s.
Proof. exact (h1). Qed.
Lemma lem3771455 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term268 A f) : term368 A f s.
Proof. exact (@lem3771428 A f h1 s). Qed.
Lemma lem3771456 {A : Type'} (f : type686 A) (s : A -> Prop) : (term368 A f s) = (term266 A f s).
Proof. exact (eq_refl (term368 A f s)). Qed.
Lemma lem3771457 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term268 A f) : term266 A f s.
Proof. exact (EQ_MP (@lem3771456 A f s) (@lem3771455 A s f h1)). Qed.
Lemma lem3771458 {A : Type'} (f : type686 A) (s : A -> Prop) : (term266 A f s) = ((term266 A f s) = True).
Proof. exact (@lem7 (term266 A f s)). Qed.
Lemma lem3771469 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term268 A f) : (term266 A f s) = True.
Proof. exact (EQ_MP (@lem3771458 A f s) (@lem3771457 A s f h1)). Qed.
Lemma lem3771470 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term268 A f) : (term266 A f s) = True.
Proof. exact (@lem3771469 A s f h1). Qed.
Lemma lem3771471 {A : Type'} (f : type686 A) (h1 : term268 A f) : (term267 A f) = (term423 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3771470 A s f h1)). Qed.
Lemma lem3771472 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3771473 {A : Type'} (f : type686 A) (h1 : term268 A f) : (term268 A f) = (term424 A).
Proof. exact (MK_COMB (@lem3771472 A) (@lem3771471 A f h1)). Qed.
Lemma lem3771475 {A : Type'} (t : Prop) : (term425 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3771476 {A : Type'} (t : Prop) : (term426 A t) = t.
Proof. exact (@lem3771475 (A -> Prop) t). Qed.
Lemma lem3771477 {A : Type'} : (term424 A) = True.
Proof. exact (@lem3771476 A True). Qed.
Lemma lem3771478 {A : Type'} (f : type686 A) (h1 : term268 A f) : (term268 A f) = True.
Proof. exact (TRANS (@lem3771473 A f h1) (@lem3771477 A)). Qed.
Lemma lem3771479 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771480 {A : Type'} (f : type686 A) (h1 : term268 A f) : (term269 A f) = (imp True).
Proof. exact (MK_COMB (@lem3771479) (@lem3771478 A f h1)). Qed.
Lemma lem3771481 {A : Type'} (f : type686 A) : (term166 A f) = (term166 A f).
Proof. exact (eq_refl (term166 A f)). Qed.
Lemma lem3771482 {A : Type'} (f : type686 A) (h1 : term268 A f) : (term270 A f) = (term427 A f).
Proof. exact (MK_COMB (@lem3771480 A f h1) (@lem3771481 A f)). Qed.
Lemma lem3771484 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3771485 {A : Type'} (f : type686 A) : (term427 A f) = (term166 A f).
Proof. exact (@lem3771484 (term166 A f)). Qed.
Lemma lem3771486 {A : Type'} (f : type686 A) (h1 : term268 A f) : (term270 A f) = (term166 A f).
Proof. exact (TRANS (@lem3771482 A f h1) (@lem3771485 A f)). Qed.
Lemma lem3771487 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771488 {A : Type'} (f : type686 A) (h1 : term268 A f) : (term420 A f) = (term428 A f).
Proof. exact (MK_COMB (@lem3771487) (@lem3771486 A f h1)). Qed.
Lemma lem3771493 {A : Type'} (s : A -> Prop) (f : type686 A) : (term412 A s f) = (term412 A s f).
Proof. exact (eq_refl (term412 A s f)). Qed.
Lemma lem3771494 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term268 A f) : (term429 A s f) = (term430 A s f).
Proof. exact (MK_COMB (@lem3771488 A f h1) (@lem3771493 A s f)). Qed.
Lemma lem3771497 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term268 A f) : (term430 A s f) = (term429 A s f).
Proof. exact (SYM (@lem3771494 A s f h1)). Qed.
Lemma lem3771499 {_98313 : Type'} (s : _98313 -> Prop) (t : _98313 -> Prop) (f : type686 _98313) : term1 _98313 s t f.
Proof. exact (@lem3769773 _98313 s t f (@lem3769765 _98313 s t f)). Qed.
Lemma lem3771500 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : type686 A) : term1 A s t f.
Proof. exact (@lem3771499 A s t f). Qed.
Lemma lem3771501 {A : Type'} (s : A -> Prop) (f : type686 A) : term431 A s f.
Proof. exact (@lem3771500 A s (@INTERS A f) f). Qed.
Lemma lem3771502 (t1 : Prop) : term432 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3771503 (t1 : Prop) : (term432 t1) = (term433 t1).
Proof. exact (eq_refl (term432 t1)). Qed.
Lemma lem3771504 (t1 : Prop) : term433 t1.
Proof. exact (EQ_MP (@lem3771503 t1) (@lem3771502 t1)). Qed.
Lemma lem3771505 (t1 : Prop) (t2 : Prop) : term434 t1 t2.
Proof. exact (@lem3771504 t1 t2). Qed.
Lemma lem3771506 (t1 : Prop) (t2 : Prop) : (term434 t1 t2) = (term435 t1 t2).
Proof. exact (eq_refl (term434 t1 t2)). Qed.
Lemma lem3771507 (t1 : Prop) (t2 : Prop) : term435 t1 t2.
Proof. exact (EQ_MP (@lem3771506 t1 t2) (@lem3771505 t1 t2)). Qed.
Lemma lem3771508 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term436 t1 t2 t3.
Proof. exact (@lem3771507 t1 t2 t3). Qed.
Lemma lem3771509 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term436 t1 t2 t3) = ((term51 t1 t2 t3) = (term437 t1 t2 t3)).
Proof. exact (eq_refl (term436 t1 t2 t3)). Qed.
Lemma lem3771510 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term51 t1 t2 t3) = (term437 t1 t2 t3).
Proof. exact (EQ_MP (@lem3771509 t1 t2 t3) (@lem3771508 t1 t2 t3)). Qed.
Lemma lem3771511 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term437 t1 t2 t3) = (term51 t1 t2 t3).
Proof. exact (SYM (@lem3771510 t1 t2 t3)). Qed.
Lemma lem3771512 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term112 A f) (h2 : @SUBSET A s s) : term438 A s f.
Proof. exact (conj (@lem3771427 A s h2) (@lem3769779 A f h1)). Qed.
Lemma lem3771513 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) (h2 : term112 A f) (h3 : @SUBSET A s s) : term439 A s f.
Proof. exact (conj (@lem3771426 A f s h1) (@lem3771512 A f s h2 h3)). Qed.
Lemma lem3771514 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term375 A f s) (h2 : term265 A f s) (h3 : term112 A f) (h4 : @SUBSET A s s) : term440 A s f.
Proof. exact (conj (@lem3771429 A f s h1) (@lem3771513 A f s h2 h3 h4)). Qed.
Lemma lem3771515 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : @SUBSET A s s) : term441 A s f.
Proof. exact (conj (@lem3771428 A f h1) (@lem3771514 A f s h2 h3 h4 h5)). Qed.
Lemma lem3771535 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3771536 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (@lem3771535 A s t). Qed.
Lemma lem3771543 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3771544 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term443 A s t) = (term444 A s t).
Proof. exact (MK_COMB (@lem3771543) (@lem3771536 A s t)). Qed.
Lemma lem3771546 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3771547 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (@lem3771546 A s t). Qed.
Lemma lem3771548 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term442 A t s).
Proof. exact (@lem3771547 A t s). Qed.
Lemma lem3771555 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term172 A t s) = (term445 A t s).
Proof. exact (MK_COMB (@lem3771544 A s t) (@lem3771548 A t s)). Qed.
Lemma lem3771558 {A : Type'} (t : A -> Prop) (f : type686 A) : (term258 A t f) = (term258 A t f).
Proof. exact (eq_refl (term258 A t f)). Qed.
Lemma lem3771559 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term257 A f t s) = (term446 A f t s).
Proof. exact (MK_COMB (@lem3771558 A t f) (@lem3771555 A t s)). Qed.
Lemma lem3771562 {A : Type'} (f : type686 A) (s : A -> Prop) : (term255 A f s) = (term447 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3771559 A f t s)). Qed.
Lemma lem3771563 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3771564 {A : Type'} (f : type686 A) (s : A -> Prop) : (term265 A f s) = (term448 A f s).
Proof. exact (MK_COMB (@lem3771563 A) (@lem3771562 A f s)). Qed.
Lemma lem3771569 {A : Type'} (s : A -> Prop) (f : type686 A) : (term258 A s f) = (term258 A s f).
Proof. exact (eq_refl (term258 A s f)). Qed.
Lemma lem3771570 {A : Type'} (f : type686 A) (s : A -> Prop) : (term266 A f s) = (term449 A f s).
Proof. exact (MK_COMB (@lem3771569 A s f) (@lem3771564 A f s)). Qed.
Lemma lem3771573 {A : Type'} (f : type686 A) : (term267 A f) = (term450 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3771570 A f s)). Qed.
Lemma lem3771574 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3771575 {A : Type'} (f : type686 A) : (term268 A f) = (term451 A f).
Proof. exact (MK_COMB (@lem3771574 A) (@lem3771573 A f)). Qed.
Lemma lem3771580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3771581 {A : Type'} (f : type686 A) : (term452 A f) = (term453 A f).
Proof. exact (MK_COMB (@lem3771580) (@lem3771575 A f)). Qed.
Lemma lem3771593 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3771594 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (@lem3771593 A s t). Qed.
Lemma lem3771595 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (@SUBSET A s' s) = (term442 A s' s).
Proof. exact (@lem3771594 A s' s). Qed.
Lemma lem3771602 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3771603 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term443 A s' s) = (term444 A s' s).
Proof. exact (MK_COMB (@lem3771602) (@lem3771595 A s' s)). Qed.
Lemma lem3771605 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3771606 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (@lem3771605 A s t). Qed.
Lemma lem3771607 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (@SUBSET A s s') = (term442 A s s').
Proof. exact (@lem3771606 A s s'). Qed.
Lemma lem3771614 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term172 A s s') = (term445 A s s').
Proof. exact (MK_COMB (@lem3771603 A s' s) (@lem3771607 A s s')). Qed.
Lemma lem3771617 {A : Type'} (s' : A -> Prop) (f : type686 A) : (term258 A s' f) = (term258 A s' f).
Proof. exact (eq_refl (term258 A s' f)). Qed.
Lemma lem3771618 {A : Type'} (f : type686 A) (s : A -> Prop) (s' : A -> Prop) : (term365 A f s s') = (term454 A f s s').
Proof. exact (MK_COMB (@lem3771617 A s' f) (@lem3771614 A s s')). Qed.
Lemma lem3771621 {A : Type'} (f : type686 A) (s : A -> Prop) : (term363 A f s) = (term455 A f s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3771618 A f s s')). Qed.
Lemma lem3771622 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3771623 {A : Type'} (f : type686 A) (s : A -> Prop) : (term375 A f s) = (term456 A f s).
Proof. exact (MK_COMB (@lem3771622 A) (@lem3771621 A f s)). Qed.
Lemma lem3771628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3771629 {A : Type'} (f : type686 A) (s : A -> Prop) : (term377 A f s) = (term457 A f s).
Proof. exact (MK_COMB (@lem3771628) (@lem3771623 A f s)). Qed.
Lemma lem3771641 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3771642 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (@lem3771641 A s t). Qed.
Lemma lem3771649 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3771650 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term443 A s t) = (term444 A s t).
Proof. exact (MK_COMB (@lem3771649) (@lem3771642 A s t)). Qed.
Lemma lem3771652 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3771653 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (@lem3771652 A s t). Qed.
Lemma lem3771654 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term442 A t s).
Proof. exact (@lem3771653 A t s). Qed.
Lemma lem3771661 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term172 A t s) = (term445 A t s).
Proof. exact (MK_COMB (@lem3771650 A s t) (@lem3771654 A t s)). Qed.
Lemma lem3771664 {A : Type'} (t : A -> Prop) (f : type686 A) : (term258 A t f) = (term258 A t f).
Proof. exact (eq_refl (term258 A t f)). Qed.
Lemma lem3771665 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term257 A f t s) = (term446 A f t s).
Proof. exact (MK_COMB (@lem3771664 A t f) (@lem3771661 A t s)). Qed.
Lemma lem3771668 {A : Type'} (f : type686 A) (s : A -> Prop) : (term255 A f s) = (term447 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3771665 A f t s)). Qed.
Lemma lem3771669 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3771670 {A : Type'} (f : type686 A) (s : A -> Prop) : (term265 A f s) = (term448 A f s).
Proof. exact (MK_COMB (@lem3771669 A) (@lem3771668 A f s)). Qed.
Lemma lem3771675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3771676 {A : Type'} (f : type686 A) (s : A -> Prop) : (term458 A f s) = (term459 A f s).
Proof. exact (MK_COMB (@lem3771675) (@lem3771670 A f s)). Qed.
Lemma lem3771680 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3771681 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (@lem3771680 A s t). Qed.
Lemma lem3771682 {A : Type'} (s : A -> Prop) : (@SUBSET A s s) = (term460 A s).
Proof. exact (@lem3771681 A s s). Qed.
Lemma lem3771688 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3771689 {A : Type'} (x : A) (s : A -> Prop) : (term461 A x s) = True.
Proof. exact (@lem3771688 (@IN A x s)). Qed.
Lemma lem3771690 {A : Type'} (s : A -> Prop) : (term462 A s) = (term463 A).
Proof. exact (fun_ext (fun x : A => @lem3771689 A x s)). Qed.
Lemma lem3771691 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3771692 {A : Type'} (s : A -> Prop) : (term460 A s) = (term464 A).
Proof. exact (MK_COMB (@lem3771691 A) (@lem3771690 A s)). Qed.
Lemma lem3771694 {A : Type'} (t : Prop) : (term425 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3771695 {A : Type'} (t : Prop) : (term425 A t) = t.
Proof. exact (@lem3771694 A t). Qed.
Lemma lem3771696 {A : Type'} : (term464 A) = True.
Proof. exact (@lem3771695 A True). Qed.
Lemma lem3771697 {A : Type'} (s : A -> Prop) : (term460 A s) = True.
Proof. exact (TRANS (@lem3771692 A s) (@lem3771696 A)). Qed.
Lemma lem3771698 {A : Type'} (s : A -> Prop) : (@SUBSET A s s) = True.
Proof. exact (TRANS (@lem3771682 A s) (@lem3771697 A s)). Qed.
Lemma lem3771699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3771700 {A : Type'} (s : A -> Prop) : (term333 A s) = (and True).
Proof. exact (MK_COMB (@lem3771699) (@lem3771698 A s)). Qed.
Lemma lem3771704 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term465 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3771705 {A : Type'} (s : type686 A) (t : type686 A) : (s = t) = (term466 A s t).
Proof. exact (@lem3771704 (A -> Prop) s t). Qed.
Lemma lem3771706 {A : Type'} (f : type686 A) : (f = (@EMPTY (A -> Prop))) = (term467 A f).
Proof. exact (@lem3771705 A f (@EMPTY (A -> Prop))). Qed.
Lemma lem3771715 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3771716 {A : Type'} (f : type686 A) : (term112 A f) = (term468 A f).
Proof. exact (MK_COMB (@lem3771715) (@lem3771706 A f)). Qed.
Lemma lem3771717 {A : Type'} (s : A -> Prop) (f : type686 A) : (term438 A s f) = (term469 A f).
Proof. exact (MK_COMB (@lem3771700 A s) (@lem3771716 A f)). Qed.
Lemma lem3771719 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3771720 {A : Type'} (f : type686 A) : (term469 A f) = (term468 A f).
Proof. exact (@lem3771719 (term468 A f)). Qed.
Lemma lem3771729 {A : Type'} (s : A -> Prop) (f : type686 A) : (term438 A s f) = (term468 A f).
Proof. exact (TRANS (@lem3771717 A s f) (@lem3771720 A f)). Qed.
Lemma lem3771730 {A : Type'} (s : A -> Prop) (f : type686 A) : (term439 A s f) = (term470 A s f).
Proof. exact (MK_COMB (@lem3771676 A f s) (@lem3771729 A s f)). Qed.
Lemma lem3771733 {A : Type'} (s : A -> Prop) (f : type686 A) : (term440 A s f) = (term471 A s f).
Proof. exact (MK_COMB (@lem3771629 A f s) (@lem3771730 A s f)). Qed.
Lemma lem3771736 {A : Type'} (s : A -> Prop) (f : type686 A) : (term441 A s f) = (term472 A s f).
Proof. exact (MK_COMB (@lem3771581 A f) (@lem3771733 A s f)). Qed.
Lemma lem3771739 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771740 {A : Type'} (s : A -> Prop) (f : type686 A) : (term473 A s f) = (term474 A s f).
Proof. exact (MK_COMB (@lem3771739) (@lem3771736 A s f)). Qed.
Lemma lem3771746 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term465 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3771747 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term465 A s t).
Proof. exact (@lem3771746 A s t). Qed.
Lemma lem3771748 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term340 A s f) = s) = (term475 A f s).
Proof. exact (@lem3771747 A (term340 A s f) s). Qed.
Lemma lem3771757 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3771758 {A : Type'} (f : type686 A) (s : A -> Prop) : (term414 A f s) = (term476 A f s).
Proof. exact (MK_COMB (@lem3771757) (@lem3771748 A f s)). Qed.
Lemma lem3771762 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term465 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3771763 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term465 A s t).
Proof. exact (@lem3771762 A s t). Qed.
Lemma lem3771764 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term340 A s f) = (@INTERS A f)) = (term477 A s f).
Proof. exact (@lem3771763 A (term340 A s f) (@INTERS A f)). Qed.
Lemma lem3771773 {A : Type'} (s : A -> Prop) (f : type686 A) : (term478 A s f) = (term479 A s f).
Proof. exact (MK_COMB (@lem3771758 A f s) (@lem3771764 A s f)). Qed.
Lemma lem3771776 {A : Type'} (s : A -> Prop) (f : type686 A) : (term480 A s f) = (term481 A s f).
Proof. exact (MK_COMB (@lem3771740 A s f) (@lem3771773 A s f)). Qed.
Lemma lem3771779 {A : Type'} (s : A -> Prop) (f : type686 A) : (term481 A s f) = (term480 A s f).
Proof. exact (SYM (@lem3771776 A s f)). Qed.
Lemma lem3771791 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3771792 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3771791 (A -> Prop) P x). Qed.
Lemma lem3771793 {A : Type'} (f : type686 A) (s : A -> Prop) : (@IN (A -> Prop) s f) = (f s).
Proof. exact (@lem3771792 A f s). Qed.
Lemma lem3771794 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771795 {A : Type'} (f : type686 A) (s : A -> Prop) : (term258 A s f) = (term482 A f s).
Proof. exact (MK_COMB (@lem3771794) (@lem3771793 A f s)). Qed.
Lemma lem3771803 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3771804 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3771803 (A -> Prop) P x). Qed.
Lemma lem3771805 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3771804 A f t). Qed.
Lemma lem3771806 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771807 {A : Type'} (f : type686 A) (t : A -> Prop) : (term258 A t f) = (term482 A f t).
Proof. exact (MK_COMB (@lem3771806) (@lem3771805 A f t)). Qed.
Lemma lem3771817 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3771818 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3771817 A P x). Qed.
Lemma lem3771819 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3771818 A s x). Qed.
Lemma lem3771820 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771821 {A : Type'} (s : A -> Prop) (x : A) : (term483 A x s) = (term484 A s x).
Proof. exact (MK_COMB (@lem3771820) (@lem3771819 A s x)). Qed.
Lemma lem3771823 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3771824 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3771823 A P x). Qed.
Lemma lem3771825 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3771824 A t x). Qed.
Lemma lem3771826 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term485 A s x t) = (term486 A s t x).
Proof. exact (MK_COMB (@lem3771821 A s x) (@lem3771825 A t x)). Qed.
Lemma lem3771829 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term487 A s t) = (term488 A s t).
Proof. exact (fun_ext (fun x : A => @lem3771826 A s t x)). Qed.
Lemma lem3771830 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3771831 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term442 A s t) = (term489 A s t).
Proof. exact (MK_COMB (@lem3771830 A) (@lem3771829 A s t)). Qed.
Lemma lem3771836 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3771837 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term444 A s t) = (term490 A s t).
Proof. exact (MK_COMB (@lem3771836) (@lem3771831 A s t)). Qed.
Lemma lem3771845 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3771846 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3771845 A P x). Qed.
Lemma lem3771847 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3771846 A t x). Qed.
Lemma lem3771848 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771849 {A : Type'} (t : A -> Prop) (x : A) : (term483 A x t) = (term484 A t x).
Proof. exact (MK_COMB (@lem3771848) (@lem3771847 A t x)). Qed.
Lemma lem3771851 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3771852 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3771851 A P x). Qed.
Lemma lem3771853 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3771852 A s x). Qed.
Lemma lem3771854 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term485 A t x s) = (term486 A t s x).
Proof. exact (MK_COMB (@lem3771849 A t x) (@lem3771853 A s x)). Qed.
Lemma lem3771857 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term487 A t s) = (term488 A t s).
Proof. exact (fun_ext (fun x : A => @lem3771854 A t s x)). Qed.
Lemma lem3771858 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3771859 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term442 A t s) = (term489 A t s).
Proof. exact (MK_COMB (@lem3771858 A) (@lem3771857 A t s)). Qed.
Lemma lem3771864 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term445 A t s) = (term491 A t s).
Proof. exact (MK_COMB (@lem3771837 A s t) (@lem3771859 A t s)). Qed.
Lemma lem3771867 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term446 A f t s) = (term492 A f t s).
Proof. exact (MK_COMB (@lem3771807 A f t) (@lem3771864 A t s)). Qed.
Lemma lem3771870 {A : Type'} (f : type686 A) (s : A -> Prop) : (term447 A f s) = (term493 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3771867 A f t s)). Qed.
Lemma lem3771871 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3771872 {A : Type'} (f : type686 A) (s : A -> Prop) : (term448 A f s) = (term494 A f s).
Proof. exact (MK_COMB (@lem3771871 A) (@lem3771870 A f s)). Qed.
Lemma lem3771877 {A : Type'} (f : type686 A) (s : A -> Prop) : (term449 A f s) = (term495 A f s).
Proof. exact (MK_COMB (@lem3771795 A f s) (@lem3771872 A f s)). Qed.
Lemma lem3771880 {A : Type'} (f : type686 A) : (term450 A f) = (term496 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3771877 A f s)). Qed.
Lemma lem3771881 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3771882 {A : Type'} (f : type686 A) : (term451 A f) = (term497 A f).
Proof. exact (MK_COMB (@lem3771881 A) (@lem3771880 A f)). Qed.
Lemma lem3771887 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3771888 {A : Type'} (f : type686 A) : (term453 A f) = (term498 A f).
Proof. exact (MK_COMB (@lem3771887) (@lem3771882 A f)). Qed.
Lemma lem3771898 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3771899 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3771898 (A -> Prop) P x). Qed.
Lemma lem3771900 {A : Type'} (f : type686 A) (s' : A -> Prop) : (@IN (A -> Prop) s' f) = (f s').
Proof. exact (@lem3771899 A f s'). Qed.
Lemma lem3771901 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771902 {A : Type'} (f : type686 A) (s' : A -> Prop) : (term258 A s' f) = (term482 A f s').
Proof. exact (MK_COMB (@lem3771901) (@lem3771900 A f s')). Qed.
Lemma lem3771912 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3771913 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3771912 A P x). Qed.
Lemma lem3771914 {A : Type'} (s' : A -> Prop) (x : A) : (@IN A x s') = (s' x).
Proof. exact (@lem3771913 A s' x). Qed.
Lemma lem3771915 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771916 {A : Type'} (s' : A -> Prop) (x : A) : (term483 A x s') = (term484 A s' x).
Proof. exact (MK_COMB (@lem3771915) (@lem3771914 A s' x)). Qed.
Lemma lem3771918 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3771919 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3771918 A P x). Qed.
Lemma lem3771920 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3771919 A s x). Qed.
Lemma lem3771921 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term485 A s' x s) = (term486 A s' s x).
Proof. exact (MK_COMB (@lem3771916 A s' x) (@lem3771920 A s x)). Qed.
Lemma lem3771924 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term487 A s' s) = (term488 A s' s).
Proof. exact (fun_ext (fun x : A => @lem3771921 A s' s x)). Qed.
Lemma lem3771925 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3771926 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term442 A s' s) = (term489 A s' s).
Proof. exact (MK_COMB (@lem3771925 A) (@lem3771924 A s' s)). Qed.
Lemma lem3771931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3771932 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term444 A s' s) = (term490 A s' s).
Proof. exact (MK_COMB (@lem3771931) (@lem3771926 A s' s)). Qed.
Lemma lem3771940 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3771941 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3771940 A P x). Qed.
Lemma lem3771942 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3771941 A s x). Qed.
Lemma lem3771943 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771944 {A : Type'} (s : A -> Prop) (x : A) : (term483 A x s) = (term484 A s x).
Proof. exact (MK_COMB (@lem3771943) (@lem3771942 A s x)). Qed.
Lemma lem3771946 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3771947 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3771946 A P x). Qed.
Lemma lem3771948 {A : Type'} (s' : A -> Prop) (x : A) : (@IN A x s') = (s' x).
Proof. exact (@lem3771947 A s' x). Qed.
Lemma lem3771949 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term485 A s x s') = (term486 A s s' x).
Proof. exact (MK_COMB (@lem3771944 A s x) (@lem3771948 A s' x)). Qed.
Lemma lem3771952 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term487 A s s') = (term488 A s s').
Proof. exact (fun_ext (fun x : A => @lem3771949 A s s' x)). Qed.
Lemma lem3771953 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3771954 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term442 A s s') = (term489 A s s').
Proof. exact (MK_COMB (@lem3771953 A) (@lem3771952 A s s')). Qed.
Lemma lem3771959 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term445 A s s') = (term491 A s s').
Proof. exact (MK_COMB (@lem3771932 A s' s) (@lem3771954 A s s')). Qed.
Lemma lem3771962 {A : Type'} (f : type686 A) (s : A -> Prop) (s' : A -> Prop) : (term454 A f s s') = (term499 A f s s').
Proof. exact (MK_COMB (@lem3771902 A f s') (@lem3771959 A s s')). Qed.
Lemma lem3771965 {A : Type'} (f : type686 A) (s : A -> Prop) : (term455 A f s) = (term500 A f s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3771962 A f s s')). Qed.
Lemma lem3771966 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3771967 {A : Type'} (f : type686 A) (s : A -> Prop) : (term456 A f s) = (term501 A f s).
Proof. exact (MK_COMB (@lem3771966 A) (@lem3771965 A f s)). Qed.
Lemma lem3771972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3771973 {A : Type'} (f : type686 A) (s : A -> Prop) : (term457 A f s) = (term502 A f s).
Proof. exact (MK_COMB (@lem3771972) (@lem3771967 A f s)). Qed.
Lemma lem3771983 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3771984 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3771983 (A -> Prop) P x). Qed.
Lemma lem3771985 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3771984 A f t). Qed.
Lemma lem3771986 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3771987 {A : Type'} (f : type686 A) (t : A -> Prop) : (term258 A t f) = (term482 A f t).
Proof. exact (MK_COMB (@lem3771986) (@lem3771985 A f t)). Qed.
Lemma lem3771997 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3771998 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3771997 A P x). Qed.
Lemma lem3771999 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3771998 A s x). Qed.
Lemma lem3772000 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3772001 {A : Type'} (s : A -> Prop) (x : A) : (term483 A x s) = (term484 A s x).
Proof. exact (MK_COMB (@lem3772000) (@lem3771999 A s x)). Qed.
Lemma lem3772003 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3772004 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3772003 A P x). Qed.
Lemma lem3772005 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3772004 A t x). Qed.
Lemma lem3772006 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term485 A s x t) = (term486 A s t x).
Proof. exact (MK_COMB (@lem3772001 A s x) (@lem3772005 A t x)). Qed.
Lemma lem3772009 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term487 A s t) = (term488 A s t).
Proof. exact (fun_ext (fun x : A => @lem3772006 A s t x)). Qed.
Lemma lem3772010 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772011 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term442 A s t) = (term489 A s t).
Proof. exact (MK_COMB (@lem3772010 A) (@lem3772009 A s t)). Qed.
Lemma lem3772016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3772017 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term444 A s t) = (term490 A s t).
Proof. exact (MK_COMB (@lem3772016) (@lem3772011 A s t)). Qed.
Lemma lem3772025 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3772026 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3772025 A P x). Qed.
Lemma lem3772027 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3772026 A t x). Qed.
Lemma lem3772028 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3772029 {A : Type'} (t : A -> Prop) (x : A) : (term483 A x t) = (term484 A t x).
Proof. exact (MK_COMB (@lem3772028) (@lem3772027 A t x)). Qed.
Lemma lem3772031 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3772032 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3772031 A P x). Qed.
Lemma lem3772033 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3772032 A s x). Qed.
Lemma lem3772034 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term485 A t x s) = (term486 A t s x).
Proof. exact (MK_COMB (@lem3772029 A t x) (@lem3772033 A s x)). Qed.
Lemma lem3772037 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term487 A t s) = (term488 A t s).
Proof. exact (fun_ext (fun x : A => @lem3772034 A t s x)). Qed.
Lemma lem3772038 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772039 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term442 A t s) = (term489 A t s).
Proof. exact (MK_COMB (@lem3772038 A) (@lem3772037 A t s)). Qed.
Lemma lem3772044 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term445 A t s) = (term491 A t s).
Proof. exact (MK_COMB (@lem3772017 A s t) (@lem3772039 A t s)). Qed.
Lemma lem3772047 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term446 A f t s) = (term492 A f t s).
Proof. exact (MK_COMB (@lem3771987 A f t) (@lem3772044 A t s)). Qed.
Lemma lem3772050 {A : Type'} (f : type686 A) (s : A -> Prop) : (term447 A f s) = (term493 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3772047 A f t s)). Qed.
Lemma lem3772051 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772052 {A : Type'} (f : type686 A) (s : A -> Prop) : (term448 A f s) = (term494 A f s).
Proof. exact (MK_COMB (@lem3772051 A) (@lem3772050 A f s)). Qed.
Lemma lem3772057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3772058 {A : Type'} (f : type686 A) (s : A -> Prop) : (term459 A f s) = (term503 A f s).
Proof. exact (MK_COMB (@lem3772057) (@lem3772052 A f s)). Qed.
Lemma lem3772066 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3772067 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3772066 (A -> Prop) P x). Qed.
Lemma lem3772068 {A : Type'} (f : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x f) = (f x).
Proof. exact (@lem3772067 A f x). Qed.
Lemma lem3772069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3772070 {A : Type'} (f : type686 A) (x : A -> Prop) : (term504 A x f) = (term505 A f x).
Proof. exact (MK_COMB (@lem3772069) (@lem3772068 A f x)). Qed.
Lemma lem3772072 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3772073 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3772072 (A -> Prop) x). Qed.
Lemma lem3772074 {A : Type'} (f : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x f) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem3772070 A f x) (@lem3772073 A x)). Qed.
Lemma lem3772076 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3772077 {A : Type'} (f : type686 A) (x : A -> Prop) : ((f x) = False) = (term506 A f x).
Proof. exact (@lem3772076 (f x)). Qed.
Lemma lem3772078 {A : Type'} (f : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x f) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = (term506 A f x).
Proof. exact (TRANS (@lem3772074 A f x) (@lem3772077 A f x)). Qed.
Lemma lem3772079 {A : Type'} (f : type686 A) : (term507 A f) = (term508 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3772078 A f x)). Qed.
Lemma lem3772080 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772081 {A : Type'} (f : type686 A) : (term467 A f) = (term509 A f).
Proof. exact (MK_COMB (@lem3772080 A) (@lem3772079 A f)). Qed.
Lemma lem3772086 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3772087 {A : Type'} (f : type686 A) : (term468 A f) = (term510 A f).
Proof. exact (MK_COMB (@lem3772086) (@lem3772081 A f)). Qed.
Lemma lem3772088 {A : Type'} (s : A -> Prop) (f : type686 A) : (term470 A s f) = (term511 A s f).
Proof. exact (MK_COMB (@lem3772058 A f s) (@lem3772087 A f)). Qed.
Lemma lem3772091 {A : Type'} (s : A -> Prop) (f : type686 A) : (term471 A s f) = (term512 A s f).
Proof. exact (MK_COMB (@lem3771973 A f s) (@lem3772088 A s f)). Qed.
Lemma lem3772094 {A : Type'} (s : A -> Prop) (f : type686 A) : (term472 A s f) = (term513 A s f).
Proof. exact (MK_COMB (@lem3771888 A f) (@lem3772091 A s f)). Qed.
Lemma lem3772097 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3772098 {A : Type'} (s : A -> Prop) (f : type686 A) : (term474 A s f) = (term514 A s f).
Proof. exact (MK_COMB (@lem3772097) (@lem3772094 A s f)). Qed.
Lemma lem3772108 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term515 A x s t) = (term516 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3772109 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term515 A x s t) = (term516 A s x t).
Proof. exact (@lem3772108 A s x t). Qed.
Lemma lem3772110 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) : (term517 A x s f) = (term518 A s x f).
Proof. exact (@lem3772109 A s x (@INTERS A f)). Qed.
Lemma lem3772114 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3772115 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3772114 A P x). Qed.
Lemma lem3772116 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3772115 A s x). Qed.
Lemma lem3772117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3772118 {A : Type'} (s : A -> Prop) (x : A) : (term519 A x s) = (term520 A s x).
Proof. exact (MK_COMB (@lem3772117) (@lem3772116 A s x)). Qed.
Lemma lem3772120 {A : Type'} (s : type686 A) (x : A) : (term521 A x s) = (term522 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3772121 {A : Type'} (s : type686 A) (x : A) : (term521 A x s) = (term522 A s x).
Proof. exact (@lem3772120 A s x). Qed.
Lemma lem3772122 {A : Type'} (f : type686 A) (x : A) : (term521 A x f) = (term522 A f x).
Proof. exact (@lem3772121 A f x). Qed.
Lemma lem3772130 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3772131 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3772130 (A -> Prop) P x). Qed.
Lemma lem3772132 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3772131 A f t). Qed.
Lemma lem3772133 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3772134 {A : Type'} (f : type686 A) (t : A -> Prop) : (term258 A t f) = (term482 A f t).
Proof. exact (MK_COMB (@lem3772133) (@lem3772132 A f t)). Qed.
Lemma lem3772136 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3772137 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3772136 A P x). Qed.
Lemma lem3772138 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3772137 A t x). Qed.
Lemma lem3772139 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term523 A f x t) = (term524 A f t x).
Proof. exact (MK_COMB (@lem3772134 A f t) (@lem3772138 A t x)). Qed.
Lemma lem3772142 {A : Type'} (f : type686 A) (x : A) : (term525 A f x) = (term526 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3772139 A f t x)). Qed.
Lemma lem3772143 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772144 {A : Type'} (f : type686 A) (x : A) : (term522 A f x) = (term527 A f x).
Proof. exact (MK_COMB (@lem3772143 A) (@lem3772142 A f x)). Qed.
Lemma lem3772149 {A : Type'} (f : type686 A) (x : A) : (term521 A x f) = (term527 A f x).
Proof. exact (TRANS (@lem3772122 A f x) (@lem3772144 A f x)). Qed.
Lemma lem3772150 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term518 A s x f) = (term528 A s f x).
Proof. exact (MK_COMB (@lem3772118 A s x) (@lem3772149 A f x)). Qed.
Lemma lem3772153 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term517 A x s f) = (term528 A s f x).
Proof. exact (TRANS (@lem3772110 A s x f) (@lem3772150 A s f x)). Qed.
Lemma lem3772154 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3772155 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term529 A x s f) = (term530 A s f x).
Proof. exact (MK_COMB (@lem3772154) (@lem3772153 A s f x)). Qed.
Lemma lem3772157 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3772158 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3772157 A P x). Qed.
Lemma lem3772159 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3772158 A s x). Qed.
Lemma lem3772160 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term517 A x s f) = (@IN A x s)) = ((term528 A s f x) = (s x)).
Proof. exact (MK_COMB (@lem3772155 A s f x) (@lem3772159 A s x)). Qed.
Lemma lem3772163 {A : Type'} (f : type686 A) (s : A -> Prop) : (term531 A f s) = (term532 A f s).
Proof. exact (fun_ext (fun x : A => @lem3772160 A f s x)). Qed.
Lemma lem3772164 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772165 {A : Type'} (f : type686 A) (s : A -> Prop) : (term475 A f s) = (term533 A f s).
Proof. exact (MK_COMB (@lem3772164 A) (@lem3772163 A f s)). Qed.
Lemma lem3772170 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3772171 {A : Type'} (f : type686 A) (s : A -> Prop) : (term476 A f s) = (term534 A f s).
Proof. exact (MK_COMB (@lem3772170) (@lem3772165 A f s)). Qed.
Lemma lem3772179 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term515 A x s t) = (term516 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3772180 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term515 A x s t) = (term516 A s x t).
Proof. exact (@lem3772179 A s x t). Qed.
Lemma lem3772181 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) : (term517 A x s f) = (term518 A s x f).
Proof. exact (@lem3772180 A s x (@INTERS A f)). Qed.
Lemma lem3772185 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3772186 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3772185 A P x). Qed.
Lemma lem3772187 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3772186 A s x). Qed.
Lemma lem3772188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3772189 {A : Type'} (s : A -> Prop) (x : A) : (term519 A x s) = (term520 A s x).
Proof. exact (MK_COMB (@lem3772188) (@lem3772187 A s x)). Qed.
Lemma lem3772191 {A : Type'} (s : type686 A) (x : A) : (term521 A x s) = (term522 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3772192 {A : Type'} (s : type686 A) (x : A) : (term521 A x s) = (term522 A s x).
Proof. exact (@lem3772191 A s x). Qed.
Lemma lem3772193 {A : Type'} (f : type686 A) (x : A) : (term521 A x f) = (term522 A f x).
Proof. exact (@lem3772192 A f x). Qed.
Lemma lem3772201 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3772202 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3772201 (A -> Prop) P x). Qed.
Lemma lem3772203 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3772202 A f t). Qed.
Lemma lem3772204 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3772205 {A : Type'} (f : type686 A) (t : A -> Prop) : (term258 A t f) = (term482 A f t).
Proof. exact (MK_COMB (@lem3772204) (@lem3772203 A f t)). Qed.
Lemma lem3772207 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3772208 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3772207 A P x). Qed.
Lemma lem3772209 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3772208 A t x). Qed.
Lemma lem3772210 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term523 A f x t) = (term524 A f t x).
Proof. exact (MK_COMB (@lem3772205 A f t) (@lem3772209 A t x)). Qed.
Lemma lem3772213 {A : Type'} (f : type686 A) (x : A) : (term525 A f x) = (term526 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3772210 A f t x)). Qed.
Lemma lem3772214 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772215 {A : Type'} (f : type686 A) (x : A) : (term522 A f x) = (term527 A f x).
Proof. exact (MK_COMB (@lem3772214 A) (@lem3772213 A f x)). Qed.
Lemma lem3772220 {A : Type'} (f : type686 A) (x : A) : (term521 A x f) = (term527 A f x).
Proof. exact (TRANS (@lem3772193 A f x) (@lem3772215 A f x)). Qed.
Lemma lem3772221 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term518 A s x f) = (term528 A s f x).
Proof. exact (MK_COMB (@lem3772189 A s x) (@lem3772220 A f x)). Qed.
Lemma lem3772224 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term517 A x s f) = (term528 A s f x).
Proof. exact (TRANS (@lem3772181 A s x f) (@lem3772221 A s f x)). Qed.
Lemma lem3772225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3772226 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term529 A x s f) = (term530 A s f x).
Proof. exact (MK_COMB (@lem3772225) (@lem3772224 A s f x)). Qed.
Lemma lem3772228 {A : Type'} (s : type686 A) (x : A) : (term521 A x s) = (term522 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3772229 {A : Type'} (s : type686 A) (x : A) : (term521 A x s) = (term522 A s x).
Proof. exact (@lem3772228 A s x). Qed.
Lemma lem3772230 {A : Type'} (f : type686 A) (x : A) : (term521 A x f) = (term522 A f x).
Proof. exact (@lem3772229 A f x). Qed.
Lemma lem3772238 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3772239 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3772238 (A -> Prop) P x). Qed.
Lemma lem3772240 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3772239 A f t). Qed.
Lemma lem3772241 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3772242 {A : Type'} (f : type686 A) (t : A -> Prop) : (term258 A t f) = (term482 A f t).
Proof. exact (MK_COMB (@lem3772241) (@lem3772240 A f t)). Qed.
Lemma lem3772244 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3772245 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3772244 A P x). Qed.
Lemma lem3772246 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3772245 A t x). Qed.
Lemma lem3772247 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term523 A f x t) = (term524 A f t x).
Proof. exact (MK_COMB (@lem3772242 A f t) (@lem3772246 A t x)). Qed.
Lemma lem3772250 {A : Type'} (f : type686 A) (x : A) : (term525 A f x) = (term526 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3772247 A f t x)). Qed.
Lemma lem3772251 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772252 {A : Type'} (f : type686 A) (x : A) : (term522 A f x) = (term527 A f x).
Proof. exact (MK_COMB (@lem3772251 A) (@lem3772250 A f x)). Qed.
Lemma lem3772257 {A : Type'} (f : type686 A) (x : A) : (term521 A x f) = (term527 A f x).
Proof. exact (TRANS (@lem3772230 A f x) (@lem3772252 A f x)). Qed.
Lemma lem3772258 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term517 A x s f) = (term521 A x f)) = ((term528 A s f x) = (term527 A f x)).
Proof. exact (MK_COMB (@lem3772226 A s f x) (@lem3772257 A f x)). Qed.
Lemma lem3772261 {A : Type'} (s : A -> Prop) (f : type686 A) : (term535 A s f) = (term536 A s f).
Proof. exact (fun_ext (fun x : A => @lem3772258 A s f x)). Qed.
Lemma lem3772262 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772263 {A : Type'} (s : A -> Prop) (f : type686 A) : (term477 A s f) = (term537 A s f).
Proof. exact (MK_COMB (@lem3772262 A) (@lem3772261 A s f)). Qed.
Lemma lem3772268 {A : Type'} (s : A -> Prop) (f : type686 A) : (term479 A s f) = (term538 A s f).
Proof. exact (MK_COMB (@lem3772171 A f s) (@lem3772263 A s f)). Qed.
Lemma lem3772271 {A : Type'} (s : A -> Prop) (f : type686 A) : (term481 A s f) = (term539 A s f).
Proof. exact (MK_COMB (@lem3772098 A s f) (@lem3772268 A s f)). Qed.
Lemma lem3772274 {A : Type'} (s : A -> Prop) (f : type686 A) : (term539 A s f) = (term481 A s f).
Proof. exact (SYM (@lem3772271 A s f)). Qed.
Lemma lem3772276 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3772277 {A : Type'} (s : A -> Prop) (f : type686 A) : (term539 A s f) = (term540 A s f).
Proof. exact (@lem3772276 (term539 A s f)). Qed.
Lemma lem3772278 {A : Type'} (s : A -> Prop) (f : type686 A) : (term540 A s f) = (term539 A s f).
Proof. exact (SYM (@lem3772277 A s f)). Qed.
Lemma lem3772279 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term541 A s f) : term541 A s f.
Proof. exact (h1). Qed.
Lemma lem3772282 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term540 A s f) : term540 A s f.
Proof. exact (h1). Qed.
Lemma lem3772283 {A : Type'} (s : A -> Prop) (f : type686 A) : term542 A s f.
Proof. exact (fun h0 : term540 A s f => @lem3772282 A s f h0). Qed.
Lemma lem3772284 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term542 A s f) : term542 A s f.
Proof. exact (h1). Qed.
Lemma lem3772285 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term540 A s f) : term540 A s f.
Proof. exact (h1). Qed.
Lemma lem3772286 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term540 A s f) (h2 : term542 A s f) : term540 A s f.
Proof. exact (@lem3772284 A s f h2 (@lem3772285 A s f h1)). Qed.
Lemma lem3772287 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term540 A s f) : term543 A s f.
Proof. exact (fun h0 : term542 A s f => @lem3772286 A s f h1 h0). Qed.
Lemma lem3772288 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term542 A s f) : term542 A s f.
Proof. exact (h1). Qed.
Lemma lem3772289 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term540 A s f) (h2 : term542 A s f) : term540 A s f.
Proof. exact (@lem3772287 A s f h1 (@lem3772288 A s f h2)). Qed.
Lemma lem3772290 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term542 A s f) : term542 A s f.
Proof. exact (fun h0 : term540 A s f => @lem3772289 A s f h0 h1). Qed.
Lemma lem3772291 {A : Type'} (s : A -> Prop) (f : type686 A) : term544 A s f.
Proof. exact (fun h0 : term542 A s f => @lem3772290 A s f h0). Qed.
Lemma lem3772294 {A : Type'} (s : A -> Prop) (f : type686 A) : term542 A s f.
Proof. exact (@lem3772291 A s f (@lem3772283 A s f)). Qed.
Lemma lem3772295 {A : Type'} (s : A -> Prop) (f : type686 A) : term542 A s f.
Proof. exact (@lem3772294 A s f). Qed.
Lemma lem3772305 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3772306 {A : Type'} (s : A -> Prop) (f : type686 A) : (term540 A s f) = (term545 A s f).
Proof. exact (@lem3772305 (term541 A s f)). Qed.
Lemma lem3772308 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3772309 {A : Type'} (s : A -> Prop) (f : type686 A) : (term545 A s f) = (term539 A s f).
Proof. exact (@lem3772308 (term539 A s f)). Qed.
Lemma lem3772312 {A : Type'} (s : A -> Prop) (f : type686 A) : (term540 A s f) = (term539 A s f).
Proof. exact (TRANS (@lem3772306 A s f) (@lem3772309 A s f)). Qed.
Lemma lem3772421 {A : Type'} (f : type686 A) : (term546 A f) = (term547 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3772312 A s f)). Qed.
Lemma lem3772422 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772423 {A : Type'} (f : type686 A) : (term548 A f) = (term549 A f).
Proof. exact (MK_COMB (@lem3772422 A) (@lem3772421 A f)). Qed.
Lemma lem3772428 {A : Type'} : (term550 A) = (term551 A).
Proof. exact (fun_ext (fun f : type686 A => @lem3772423 A f)). Qed.
Lemma lem3772429 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3772438 {A : Type'} : (term552 A) = (term553 A).
Proof. exact (MK_COMB (@lem3772429 A) (@lem3772428 A)). Qed.
Lemma lem3772443 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term524 A f t x) = (term524 A f t x).
Proof. exact (eq_refl (term524 A f t x)). Qed.
Lemma lem3772444 {A : Type'} (f : type686 A) (x : A) : (term526 A f x) = (term526 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3772443 A f t x)). Qed.
Lemma lem3772445 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772446 {A : Type'} (f : type686 A) (x : A) : (term527 A f x) = (term527 A f x).
Proof. exact (MK_COMB (@lem3772445 A) (@lem3772444 A f x)). Qed.
Lemma lem3772451 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term524 A f t x) = (term524 A f t x).
Proof. exact (eq_refl (term524 A f t x)). Qed.
Lemma lem3772452 {A : Type'} (f : type686 A) (x : A) : (term526 A f x) = (term526 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3772451 A f t x)). Qed.
Lemma lem3772453 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772454 {A : Type'} (f : type686 A) (x : A) : (term527 A f x) = (term527 A f x).
Proof. exact (MK_COMB (@lem3772453 A) (@lem3772452 A f x)). Qed.
Lemma lem3772457 {A : Type'} (s : A -> Prop) (x : A) : (term520 A s x) = (term520 A s x).
Proof. exact (eq_refl (term520 A s x)). Qed.
Lemma lem3772458 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term528 A s f x) = (term528 A s f x).
Proof. exact (MK_COMB (@lem3772457 A s x) (@lem3772454 A f x)). Qed.
Lemma lem3772459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3772460 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term530 A s f x) = (term530 A s f x).
Proof. exact (MK_COMB (@lem3772459) (@lem3772458 A s f x)). Qed.
Lemma lem3772461 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term528 A s f x) = (term527 A f x)) = ((term528 A s f x) = (term527 A f x)).
Proof. exact (MK_COMB (@lem3772460 A s f x) (@lem3772446 A f x)). Qed.
Lemma lem3772462 {A : Type'} (s : A -> Prop) (f : type686 A) : (term536 A s f) = (term536 A s f).
Proof. exact (fun_ext (fun x : A => @lem3772461 A s f x)). Qed.
Lemma lem3772463 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772464 {A : Type'} (s : A -> Prop) (f : type686 A) : (term537 A s f) = (term537 A s f).
Proof. exact (MK_COMB (@lem3772463 A) (@lem3772462 A s f)). Qed.
Lemma lem3772465 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3772470 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term524 A f t x) = (term524 A f t x).
Proof. exact (eq_refl (term524 A f t x)). Qed.
Lemma lem3772471 {A : Type'} (f : type686 A) (x : A) : (term526 A f x) = (term526 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3772470 A f t x)). Qed.
Lemma lem3772472 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772473 {A : Type'} (f : type686 A) (x : A) : (term527 A f x) = (term527 A f x).
Proof. exact (MK_COMB (@lem3772472 A) (@lem3772471 A f x)). Qed.
Lemma lem3772476 {A : Type'} (s : A -> Prop) (x : A) : (term520 A s x) = (term520 A s x).
Proof. exact (eq_refl (term520 A s x)). Qed.
Lemma lem3772477 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term528 A s f x) = (term528 A s f x).
Proof. exact (MK_COMB (@lem3772476 A s x) (@lem3772473 A f x)). Qed.
Lemma lem3772478 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3772479 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term530 A s f x) = (term530 A s f x).
Proof. exact (MK_COMB (@lem3772478) (@lem3772477 A s f x)). Qed.
Lemma lem3772480 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term528 A s f x) = (s x)) = ((term528 A s f x) = (s x)).
Proof. exact (MK_COMB (@lem3772479 A s f x) (@lem3772465 A s x)). Qed.
Lemma lem3772481 {A : Type'} (f : type686 A) (s : A -> Prop) : (term532 A f s) = (term532 A f s).
Proof. exact (fun_ext (fun x : A => @lem3772480 A f s x)). Qed.
Lemma lem3772482 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772483 {A : Type'} (f : type686 A) (s : A -> Prop) : (term533 A f s) = (term533 A f s).
Proof. exact (MK_COMB (@lem3772482 A) (@lem3772481 A f s)). Qed.
Lemma lem3772484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3772485 {A : Type'} (f : type686 A) (s : A -> Prop) : (term534 A f s) = (term534 A f s).
Proof. exact (MK_COMB (@lem3772484) (@lem3772483 A f s)). Qed.
Lemma lem3772486 {A : Type'} (s : A -> Prop) (f : type686 A) : (term538 A s f) = (term538 A s f).
Proof. exact (MK_COMB (@lem3772485 A f s) (@lem3772464 A s f)). Qed.
Lemma lem3772489 {A : Type'} (f : type686 A) (x : A -> Prop) : (term506 A f x) = (term506 A f x).
Proof. exact (eq_refl (term506 A f x)). Qed.
Lemma lem3772490 {A : Type'} (f : type686 A) : (term508 A f) = (term508 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3772489 A f x)). Qed.
Lemma lem3772491 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772492 {A : Type'} (f : type686 A) : (term509 A f) = (term509 A f).
Proof. exact (MK_COMB (@lem3772491 A) (@lem3772490 A f)). Qed.
Lemma lem3772493 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3772494 {A : Type'} (f : type686 A) : (term510 A f) = (term510 A f).
Proof. exact (MK_COMB (@lem3772493) (@lem3772492 A f)). Qed.
Lemma lem3772499 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term486 A t s x) = (term486 A t s x).
Proof. exact (eq_refl (term486 A t s x)). Qed.
Lemma lem3772500 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term488 A t s) = (term488 A t s).
Proof. exact (fun_ext (fun x : A => @lem3772499 A t s x)). Qed.
Lemma lem3772501 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772502 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term489 A t s) = (term489 A t s).
Proof. exact (MK_COMB (@lem3772501 A) (@lem3772500 A t s)). Qed.
Lemma lem3772507 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term486 A s t x) = (term486 A s t x).
Proof. exact (eq_refl (term486 A s t x)). Qed.
Lemma lem3772508 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term488 A s t) = (term488 A s t).
Proof. exact (fun_ext (fun x : A => @lem3772507 A s t x)). Qed.
Lemma lem3772509 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772510 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term489 A s t) = (term489 A s t).
Proof. exact (MK_COMB (@lem3772509 A) (@lem3772508 A s t)). Qed.
Lemma lem3772511 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3772512 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term490 A s t) = (term490 A s t).
Proof. exact (MK_COMB (@lem3772511) (@lem3772510 A s t)). Qed.
Lemma lem3772513 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term491 A t s) = (term491 A t s).
Proof. exact (MK_COMB (@lem3772512 A s t) (@lem3772502 A t s)). Qed.
Lemma lem3772516 {A : Type'} (f : type686 A) (t : A -> Prop) : (term482 A f t) = (term482 A f t).
Proof. exact (eq_refl (term482 A f t)). Qed.
Lemma lem3772517 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term492 A f t s) = (term492 A f t s).
Proof. exact (MK_COMB (@lem3772516 A f t) (@lem3772513 A t s)). Qed.
Lemma lem3772518 {A : Type'} (f : type686 A) (s : A -> Prop) : (term493 A f s) = (term493 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3772517 A f t s)). Qed.
Lemma lem3772519 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772520 {A : Type'} (f : type686 A) (s : A -> Prop) : (term494 A f s) = (term494 A f s).
Proof. exact (MK_COMB (@lem3772519 A) (@lem3772518 A f s)). Qed.
Lemma lem3772521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3772522 {A : Type'} (f : type686 A) (s : A -> Prop) : (term503 A f s) = (term503 A f s).
Proof. exact (MK_COMB (@lem3772521) (@lem3772520 A f s)). Qed.
Lemma lem3772523 {A : Type'} (s : A -> Prop) (f : type686 A) : (term511 A s f) = (term511 A s f).
Proof. exact (MK_COMB (@lem3772522 A f s) (@lem3772494 A f)). Qed.
Lemma lem3772528 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term486 A s s' x) = (term486 A s s' x).
Proof. exact (eq_refl (term486 A s s' x)). Qed.
Lemma lem3772529 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term488 A s s') = (term488 A s s').
Proof. exact (fun_ext (fun x : A => @lem3772528 A s s' x)). Qed.
Lemma lem3772530 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772531 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term489 A s s') = (term489 A s s').
Proof. exact (MK_COMB (@lem3772530 A) (@lem3772529 A s s')). Qed.
Lemma lem3772536 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term486 A s' s x) = (term486 A s' s x).
Proof. exact (eq_refl (term486 A s' s x)). Qed.
Lemma lem3772537 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term488 A s' s) = (term488 A s' s).
Proof. exact (fun_ext (fun x : A => @lem3772536 A s' s x)). Qed.
Lemma lem3772538 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772539 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term489 A s' s) = (term489 A s' s).
Proof. exact (MK_COMB (@lem3772538 A) (@lem3772537 A s' s)). Qed.
Lemma lem3772540 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3772541 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term490 A s' s) = (term490 A s' s).
Proof. exact (MK_COMB (@lem3772540) (@lem3772539 A s' s)). Qed.
Lemma lem3772542 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term491 A s s') = (term491 A s s').
Proof. exact (MK_COMB (@lem3772541 A s' s) (@lem3772531 A s s')). Qed.
Lemma lem3772545 {A : Type'} (f : type686 A) (s' : A -> Prop) : (term482 A f s') = (term482 A f s').
Proof. exact (eq_refl (term482 A f s')). Qed.
Lemma lem3772546 {A : Type'} (f : type686 A) (s : A -> Prop) (s' : A -> Prop) : (term499 A f s s') = (term499 A f s s').
Proof. exact (MK_COMB (@lem3772545 A f s') (@lem3772542 A s s')). Qed.
Lemma lem3772547 {A : Type'} (f : type686 A) (s : A -> Prop) : (term500 A f s) = (term500 A f s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3772546 A f s s')). Qed.
Lemma lem3772548 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772549 {A : Type'} (f : type686 A) (s : A -> Prop) : (term501 A f s) = (term501 A f s).
Proof. exact (MK_COMB (@lem3772548 A) (@lem3772547 A f s)). Qed.
Lemma lem3772550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3772551 {A : Type'} (f : type686 A) (s : A -> Prop) : (term502 A f s) = (term502 A f s).
Proof. exact (MK_COMB (@lem3772550) (@lem3772549 A f s)). Qed.
Lemma lem3772552 {A : Type'} (s : A -> Prop) (f : type686 A) : (term512 A s f) = (term512 A s f).
Proof. exact (MK_COMB (@lem3772551 A f s) (@lem3772523 A s f)). Qed.
Lemma lem3772557 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term486 A t s x) = (term486 A t s x).
Proof. exact (eq_refl (term486 A t s x)). Qed.
Lemma lem3772558 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term488 A t s) = (term488 A t s).
Proof. exact (fun_ext (fun x : A => @lem3772557 A t s x)). Qed.
Lemma lem3772559 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772560 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term489 A t s) = (term489 A t s).
Proof. exact (MK_COMB (@lem3772559 A) (@lem3772558 A t s)). Qed.
Lemma lem3772565 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term486 A s t x) = (term486 A s t x).
Proof. exact (eq_refl (term486 A s t x)). Qed.
Lemma lem3772566 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term488 A s t) = (term488 A s t).
Proof. exact (fun_ext (fun x : A => @lem3772565 A s t x)). Qed.
Lemma lem3772567 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772568 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term489 A s t) = (term489 A s t).
Proof. exact (MK_COMB (@lem3772567 A) (@lem3772566 A s t)). Qed.
Lemma lem3772569 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3772570 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term490 A s t) = (term490 A s t).
Proof. exact (MK_COMB (@lem3772569) (@lem3772568 A s t)). Qed.
Lemma lem3772571 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term491 A t s) = (term491 A t s).
Proof. exact (MK_COMB (@lem3772570 A s t) (@lem3772560 A t s)). Qed.
Lemma lem3772574 {A : Type'} (f : type686 A) (t : A -> Prop) : (term482 A f t) = (term482 A f t).
Proof. exact (eq_refl (term482 A f t)). Qed.
Lemma lem3772575 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term492 A f t s) = (term492 A f t s).
Proof. exact (MK_COMB (@lem3772574 A f t) (@lem3772571 A t s)). Qed.
Lemma lem3772576 {A : Type'} (f : type686 A) (s : A -> Prop) : (term493 A f s) = (term493 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3772575 A f t s)). Qed.
Lemma lem3772577 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772578 {A : Type'} (f : type686 A) (s : A -> Prop) : (term494 A f s) = (term494 A f s).
Proof. exact (MK_COMB (@lem3772577 A) (@lem3772576 A f s)). Qed.
Lemma lem3772581 {A : Type'} (f : type686 A) (s : A -> Prop) : (term482 A f s) = (term482 A f s).
Proof. exact (eq_refl (term482 A f s)). Qed.
Lemma lem3772582 {A : Type'} (f : type686 A) (s : A -> Prop) : (term495 A f s) = (term495 A f s).
Proof. exact (MK_COMB (@lem3772581 A f s) (@lem3772578 A f s)). Qed.
Lemma lem3772583 {A : Type'} (f : type686 A) : (term496 A f) = (term496 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3772582 A f s)). Qed.
Lemma lem3772584 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772585 {A : Type'} (f : type686 A) : (term497 A f) = (term497 A f).
Proof. exact (MK_COMB (@lem3772584 A) (@lem3772583 A f)). Qed.
Lemma lem3772586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3772587 {A : Type'} (f : type686 A) : (term498 A f) = (term498 A f).
Proof. exact (MK_COMB (@lem3772586) (@lem3772585 A f)). Qed.
Lemma lem3772588 {A : Type'} (s : A -> Prop) (f : type686 A) : (term513 A s f) = (term513 A s f).
Proof. exact (MK_COMB (@lem3772587 A f) (@lem3772552 A s f)). Qed.
Lemma lem3772589 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3772590 {A : Type'} (s : A -> Prop) (f : type686 A) : (term514 A s f) = (term514 A s f).
Proof. exact (MK_COMB (@lem3772589) (@lem3772588 A s f)). Qed.
Lemma lem3772591 {A : Type'} (s : A -> Prop) (f : type686 A) : (term539 A s f) = (term539 A s f).
Proof. exact (MK_COMB (@lem3772590 A s f) (@lem3772486 A s f)). Qed.
Lemma lem3772592 {A : Type'} (f : type686 A) : (term547 A f) = (term547 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3772591 A s f)). Qed.
Lemma lem3772593 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772594 {A : Type'} (f : type686 A) : (term549 A f) = (term549 A f).
Proof. exact (MK_COMB (@lem3772593 A) (@lem3772592 A f)). Qed.
Lemma lem3772595 {A : Type'} : (term551 A) = (term551 A).
Proof. exact (fun_ext (fun f : type686 A => @lem3772594 A f)). Qed.
Lemma lem3772596 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3772597 {A : Type'} : (term553 A) = (term553 A).
Proof. exact (MK_COMB (@lem3772596 A) (@lem3772595 A)). Qed.
Lemma lem3772754 {A : Type'} : (term552 A) = (term553 A).
Proof. exact (TRANS (@lem3772438 A) (@lem3772597 A)). Qed.
Lemma lem3772755 {A : Type'} : (term553 A) = (term552 A).
Proof. exact (SYM (@lem3772754 A)). Qed.
Lemma lem3772756 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term513 A s f) : term513 A s f.
Proof. exact (h1). Qed.
Lemma lem3772758 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3772759 {A : Type'} (s : A -> Prop) (f : type686 A) : (term538 A s f) = (term554 A s f).
Proof. exact (@lem3772758 (term538 A s f)). Qed.
Lemma lem3772760 {A : Type'} (s : A -> Prop) (f : type686 A) : (term554 A s f) = (term538 A s f).
Proof. exact (SYM (@lem3772759 A s f)). Qed.
Lemma lem3772761 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term555 A s f) : term555 A s f.
Proof. exact (h1). Qed.
Lemma lem3772770 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term486 A s t x) = (term556 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3772771 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term488 A s t) = (term557 A s t).
Proof. exact (fun_ext (fun x : A => @lem3772770 A s t x)). Qed.
Lemma lem3772772 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772773 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term489 A s t) = (term558 A s t).
Proof. exact (MK_COMB (@lem3772772 A) (@lem3772771 A s t)). Qed.
Lemma lem3772780 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term486 A t s x) = (term556 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem3772781 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term488 A t s) = (term557 A t s).
Proof. exact (fun_ext (fun x : A => @lem3772780 A t s x)). Qed.
Lemma lem3772782 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772783 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term489 A t s) = (term558 A t s).
Proof. exact (MK_COMB (@lem3772782 A) (@lem3772781 A t s)). Qed.
Lemma lem3772784 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3772785 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term490 A s t) = (term559 A s t).
Proof. exact (MK_COMB (@lem3772784) (@lem3772773 A s t)). Qed.
Lemma lem3772786 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term491 A t s) = (term560 A t s).
Proof. exact (MK_COMB (@lem3772785 A s t) (@lem3772783 A t s)). Qed.
Lemma lem3772788 {A : Type'} (f : type686 A) (t : A -> Prop) : (term561 A f t) = (term561 A f t).
Proof. exact (eq_refl (term561 A f t)). Qed.
Lemma lem3772789 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term562 A f t s) = (term563 A f t s).
Proof. exact (MK_COMB (@lem3772788 A f t) (@lem3772786 A t s)). Qed.
Lemma lem3772790 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term492 A f t s) = (term562 A f t s).
Proof. exact (@lem17265 (f t) (term491 A t s)). Qed.
Lemma lem3772791 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term492 A f t s) = (term563 A f t s).
Proof. exact (TRANS (@lem3772790 A f t s) (@lem3772789 A f t s)). Qed.
Lemma lem3772792 {A : Type'} (f : type686 A) (s : A -> Prop) : (term493 A f s) = (term564 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3772791 A f t s)). Qed.
Lemma lem3772793 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772794 {A : Type'} (f : type686 A) (s : A -> Prop) : (term494 A f s) = (term565 A f s).
Proof. exact (MK_COMB (@lem3772793 A) (@lem3772792 A f s)). Qed.
Lemma lem3772796 {A : Type'} (f : type686 A) (s : A -> Prop) : (term561 A f s) = (term561 A f s).
Proof. exact (eq_refl (term561 A f s)). Qed.
Lemma lem3772797 {A : Type'} (f : type686 A) (s : A -> Prop) : (term566 A f s) = (term567 A f s).
Proof. exact (MK_COMB (@lem3772796 A f s) (@lem3772794 A f s)). Qed.
Lemma lem3772798 {A : Type'} (f : type686 A) (s : A -> Prop) : (term495 A f s) = (term566 A f s).
Proof. exact (@lem17265 (f s) (term494 A f s)). Qed.
Lemma lem3772799 {A : Type'} (f : type686 A) (s : A -> Prop) : (term495 A f s) = (term567 A f s).
Proof. exact (TRANS (@lem3772798 A f s) (@lem3772797 A f s)). Qed.
Lemma lem3772800 {A : Type'} (f : type686 A) : (term496 A f) = (term568 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3772799 A f s)). Qed.
Lemma lem3772801 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772802 {A : Type'} (f : type686 A) : (term497 A f) = (term569 A f).
Proof. exact (MK_COMB (@lem3772801 A) (@lem3772800 A f)). Qed.
Lemma lem3772810 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term486 A s' s x) = (term556 A s' s x).
Proof. exact (@lem17265 (s' x) (s x)). Qed.
Lemma lem3772811 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term488 A s' s) = (term557 A s' s).
Proof. exact (fun_ext (fun x : A => @lem3772810 A s' s x)). Qed.
Lemma lem3772812 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772813 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term489 A s' s) = (term558 A s' s).
Proof. exact (MK_COMB (@lem3772812 A) (@lem3772811 A s' s)). Qed.
Lemma lem3772820 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term486 A s s' x) = (term556 A s s' x).
Proof. exact (@lem17265 (s x) (s' x)). Qed.
Lemma lem3772821 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term488 A s s') = (term557 A s s').
Proof. exact (fun_ext (fun x : A => @lem3772820 A s s' x)). Qed.
Lemma lem3772822 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772823 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term489 A s s') = (term558 A s s').
Proof. exact (MK_COMB (@lem3772822 A) (@lem3772821 A s s')). Qed.
Lemma lem3772824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3772825 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term490 A s' s) = (term559 A s' s).
Proof. exact (MK_COMB (@lem3772824) (@lem3772813 A s' s)). Qed.
Lemma lem3772826 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term491 A s s') = (term560 A s s').
Proof. exact (MK_COMB (@lem3772825 A s' s) (@lem3772823 A s s')). Qed.
Lemma lem3772828 {A : Type'} (f : type686 A) (s' : A -> Prop) : (term561 A f s') = (term561 A f s').
Proof. exact (eq_refl (term561 A f s')). Qed.
Lemma lem3772829 {A : Type'} (f : type686 A) (s : A -> Prop) (s' : A -> Prop) : (term570 A f s s') = (term571 A f s s').
Proof. exact (MK_COMB (@lem3772828 A f s') (@lem3772826 A s s')). Qed.
Lemma lem3772830 {A : Type'} (f : type686 A) (s : A -> Prop) (s' : A -> Prop) : (term499 A f s s') = (term570 A f s s').
Proof. exact (@lem17265 (f s') (term491 A s s')). Qed.
Lemma lem3772831 {A : Type'} (f : type686 A) (s : A -> Prop) (s' : A -> Prop) : (term499 A f s s') = (term571 A f s s').
Proof. exact (TRANS (@lem3772830 A f s s') (@lem3772829 A f s s')). Qed.
Lemma lem3772832 {A : Type'} (f : type686 A) (s : A -> Prop) : (term500 A f s) = (term572 A f s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3772831 A f s s')). Qed.
Lemma lem3772833 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772834 {A : Type'} (f : type686 A) (s : A -> Prop) : (term501 A f s) = (term573 A f s).
Proof. exact (MK_COMB (@lem3772833 A) (@lem3772832 A f s)). Qed.
Lemma lem3772842 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term486 A s t x) = (term556 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3772843 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term488 A s t) = (term557 A s t).
Proof. exact (fun_ext (fun x : A => @lem3772842 A s t x)). Qed.
Lemma lem3772844 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772845 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term489 A s t) = (term558 A s t).
Proof. exact (MK_COMB (@lem3772844 A) (@lem3772843 A s t)). Qed.
Lemma lem3772852 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term486 A t s x) = (term556 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem3772853 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term488 A t s) = (term557 A t s).
Proof. exact (fun_ext (fun x : A => @lem3772852 A t s x)). Qed.
Lemma lem3772854 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3772855 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term489 A t s) = (term558 A t s).
Proof. exact (MK_COMB (@lem3772854 A) (@lem3772853 A t s)). Qed.
Lemma lem3772856 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3772857 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term490 A s t) = (term559 A s t).
Proof. exact (MK_COMB (@lem3772856) (@lem3772845 A s t)). Qed.
Lemma lem3772858 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term491 A t s) = (term560 A t s).
Proof. exact (MK_COMB (@lem3772857 A s t) (@lem3772855 A t s)). Qed.
Lemma lem3772860 {A : Type'} (f : type686 A) (t : A -> Prop) : (term561 A f t) = (term561 A f t).
Proof. exact (eq_refl (term561 A f t)). Qed.
Lemma lem3772861 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term562 A f t s) = (term563 A f t s).
Proof. exact (MK_COMB (@lem3772860 A f t) (@lem3772858 A t s)). Qed.
Lemma lem3772862 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term492 A f t s) = (term562 A f t s).
Proof. exact (@lem17265 (f t) (term491 A t s)). Qed.
Lemma lem3772863 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term492 A f t s) = (term563 A f t s).
Proof. exact (TRANS (@lem3772862 A f t s) (@lem3772861 A f t s)). Qed.
Lemma lem3772864 {A : Type'} (f : type686 A) (s : A -> Prop) : (term493 A f s) = (term564 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3772863 A f t s)). Qed.
Lemma lem3772865 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3772866 {A : Type'} (f : type686 A) (s : A -> Prop) : (term494 A f s) = (term565 A f s).
Proof. exact (MK_COMB (@lem3772865 A) (@lem3772864 A f s)). Qed.
Lemma lem3772869 {A : Type'} (f : type686 A) (x : A -> Prop) : (term574 A f x) = (f x).
Proof. exact (@lem16933 (f x)). Qed.
Lemma lem3772870 {A : Type'} (P : type686 A) : (term575 A P) = (term576 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3772871 {A : Type'} (f : type686 A) : (term510 A f) = (term577 A f).
Proof. exact (@lem3772870 A (term508 A f)). Qed.
Lemma lem3772872 {A : Type'} (f : type686 A) (x : A -> Prop) : (term578 A f x) = (term506 A f x).
Proof. exact (eq_refl (term578 A f x)). Qed.
Lemma lem3772873 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3772874 {A : Type'} (f : type686 A) (x : A -> Prop) : (term579 A f x) = (term574 A f x).
Proof. exact (MK_COMB (@lem3772873) (@lem3772872 A f x)). Qed.
Lemma lem3772875 {A : Type'} (f : type686 A) (x : A -> Prop) : (term579 A f x) = (f x).
Proof. exact (TRANS (@lem3772874 A f x) (@lem3772869 A f x)). Qed.
Lemma lem3772876 {A : Type'} (f : type686 A) : (term580 A f) = (term581 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3772875 A f x)). Qed.
Lemma lem3772877 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3772878 {A : Type'} (f : type686 A) : (term577 A f) = (term582 A f).
Proof. exact (MK_COMB (@lem3772877 A) (@lem3772876 A f)). Qed.
Lemma lem3772879 {A : Type'} (f : type686 A) : (term510 A f) = (term582 A f).
Proof. exact (TRANS (@lem3772871 A f) (@lem3772878 A f)). Qed.
Lemma lem3772880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3772881 {A : Type'} (f : type686 A) (s : A -> Prop) : (term503 A f s) = (term583 A f s).
Proof. exact (MK_COMB (@lem3772880) (@lem3772866 A f s)). Qed.
Lemma lem3772882 {A : Type'} (s : A -> Prop) (f : type686 A) : (term511 A s f) = (term584 A s f).
Proof. exact (MK_COMB (@lem3772881 A f s) (@lem3772879 A f)). Qed.
Lemma lem3772883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3772884 {A : Type'} (f : type686 A) (s : A -> Prop) : (term502 A f s) = (term585 A f s).
Proof. exact (MK_COMB (@lem3772883) (@lem3772834 A f s)). Qed.
Lemma lem3772885 {A : Type'} (s : A -> Prop) (f : type686 A) : (term512 A s f) = (term586 A s f).
Proof. exact (MK_COMB (@lem3772884 A f s) (@lem3772882 A s f)). Qed.
Lemma lem3772886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3772887 {A : Type'} (f : type686 A) : (term498 A f) = (term587 A f).
Proof. exact (MK_COMB (@lem3772886) (@lem3772802 A f)). Qed.
Lemma lem3772888 {A : Type'} (s : A -> Prop) (f : type686 A) : (term513 A s f) = (term588 A s f).
Proof. exact (MK_COMB (@lem3772887 A f) (@lem3772885 A s f)). Qed.
Lemma lem3773279 {A : Type'} (P : Prop) (Q : A -> Prop) : (term589 A P Q) = (term590 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3773280 {A : Type'} (P : Prop) (Q : type686 A) : (term591 A P Q) = (term592 A P Q).
Proof. exact (@lem3773279 (A -> Prop) P Q). Qed.
Lemma lem3773281 {A : Type'} (s : A -> Prop) (f : type686 A) : (term584 A s f) = (term593 A s f).
Proof. exact (@lem3773280 A (term565 A f s) f). Qed.
Lemma lem3773282 {A : Type'} (f : type686 A) (s : A -> Prop) : (term585 A f s) = (term585 A f s).
Proof. exact (eq_refl (term585 A f s)). Qed.
Lemma lem3773283 {A : Type'} (s : A -> Prop) (f : type686 A) : (term586 A s f) = (term594 A s f).
Proof. exact (MK_COMB (@lem3773282 A f s) (@lem3773281 A s f)). Qed.
Lemma lem3773285 {A : Type'} (P : Prop) (Q : A -> Prop) : (term589 A P Q) = (term590 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3773286 {A : Type'} (P : Prop) (Q : type686 A) : (term591 A P Q) = (term592 A P Q).
Proof. exact (@lem3773285 (A -> Prop) P Q). Qed.
Lemma lem3773287 {A : Type'} (s : A -> Prop) (f : type686 A) : (term595 A s f) = (term596 A s f).
Proof. exact (@lem3773286 A (term573 A f s) (term597 A s f)). Qed.
Lemma lem3773288 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term598 A s f x) = (term599 A s f x).
Proof. exact (eq_refl (term598 A s f x)). Qed.
Lemma lem3773289 {A : Type'} (s : A -> Prop) (f : type686 A) : (term600 A s f) = (term597 A s f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3773288 A s f x)). Qed.
Lemma lem3773290 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3773291 {A : Type'} (s : A -> Prop) (f : type686 A) : (term601 A s f) = (term593 A s f).
Proof. exact (MK_COMB (@lem3773290 A) (@lem3773289 A s f)). Qed.
Lemma lem3773292 {A : Type'} (f : type686 A) (s : A -> Prop) : (term585 A f s) = (term585 A f s).
Proof. exact (eq_refl (term585 A f s)). Qed.
Lemma lem3773293 {A : Type'} (s : A -> Prop) (f : type686 A) : (term595 A s f) = (term594 A s f).
Proof. exact (MK_COMB (@lem3773292 A f s) (@lem3773291 A s f)). Qed.
Lemma lem3773294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3773295 {A : Type'} (s : A -> Prop) (f : type686 A) : (term602 A s f) = (term603 A s f).
Proof. exact (MK_COMB (@lem3773294) (@lem3773293 A s f)). Qed.
Lemma lem3773296 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term598 A s f x) = (term599 A s f x).
Proof. exact (eq_refl (term598 A s f x)). Qed.
Lemma lem3773297 {A : Type'} (f : type686 A) (s : A -> Prop) : (term585 A f s) = (term585 A f s).
Proof. exact (eq_refl (term585 A f s)). Qed.
Lemma lem3773298 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term604 A s f x) = (term605 A s f x).
Proof. exact (MK_COMB (@lem3773297 A f s) (@lem3773296 A s f x)). Qed.
Lemma lem3773299 {A : Type'} (s : A -> Prop) (f : type686 A) : (term606 A s f) = (term607 A s f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3773298 A s f x)). Qed.
Lemma lem3773300 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3773301 {A : Type'} (s : A -> Prop) (f : type686 A) : (term596 A s f) = (term608 A s f).
Proof. exact (MK_COMB (@lem3773300 A) (@lem3773299 A s f)). Qed.
Lemma lem3773302 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term595 A s f) = (term596 A s f)) = ((term594 A s f) = (term608 A s f)).
Proof. exact (MK_COMB (@lem3773295 A s f) (@lem3773301 A s f)). Qed.
Lemma lem3773303 {A : Type'} (s : A -> Prop) (f : type686 A) : (term594 A s f) = (term608 A s f).
Proof. exact (EQ_MP (@lem3773302 A s f) (@lem3773287 A s f)). Qed.
Lemma lem3773304 {A : Type'} (s : A -> Prop) (f : type686 A) : (term586 A s f) = (term608 A s f).
Proof. exact (TRANS (@lem3773283 A s f) (@lem3773303 A s f)). Qed.
Lemma lem3773305 {A : Type'} (f : type686 A) : (term587 A f) = (term587 A f).
Proof. exact (eq_refl (term587 A f)). Qed.
Lemma lem3773306 {A : Type'} (s : A -> Prop) (f : type686 A) : (term588 A s f) = (term609 A s f).
Proof. exact (MK_COMB (@lem3773305 A f) (@lem3773304 A s f)). Qed.
Lemma lem3773308 {A : Type'} (P : Prop) (Q : A -> Prop) : (term589 A P Q) = (term590 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3773309 {A : Type'} (P : Prop) (Q : type686 A) : (term591 A P Q) = (term592 A P Q).
Proof. exact (@lem3773308 (A -> Prop) P Q). Qed.
Lemma lem3773310 {A : Type'} (s : A -> Prop) (f : type686 A) : (term610 A s f) = (term611 A s f).
Proof. exact (@lem3773309 A (term569 A f) (term607 A s f)). Qed.
Lemma lem3773311 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term612 A s f x) = (term605 A s f x).
Proof. exact (eq_refl (term612 A s f x)). Qed.
Lemma lem3773312 {A : Type'} (s : A -> Prop) (f : type686 A) : (term613 A s f) = (term607 A s f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3773311 A s f x)). Qed.
Lemma lem3773313 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3773314 {A : Type'} (s : A -> Prop) (f : type686 A) : (term614 A s f) = (term608 A s f).
Proof. exact (MK_COMB (@lem3773313 A) (@lem3773312 A s f)). Qed.
Lemma lem3773315 {A : Type'} (f : type686 A) : (term587 A f) = (term587 A f).
Proof. exact (eq_refl (term587 A f)). Qed.
Lemma lem3773316 {A : Type'} (s : A -> Prop) (f : type686 A) : (term610 A s f) = (term609 A s f).
Proof. exact (MK_COMB (@lem3773315 A f) (@lem3773314 A s f)). Qed.
Lemma lem3773317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3773318 {A : Type'} (s : A -> Prop) (f : type686 A) : (term615 A s f) = (term616 A s f).
Proof. exact (MK_COMB (@lem3773317) (@lem3773316 A s f)). Qed.
Lemma lem3773319 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term612 A s f x) = (term605 A s f x).
Proof. exact (eq_refl (term612 A s f x)). Qed.
Lemma lem3773320 {A : Type'} (f : type686 A) : (term587 A f) = (term587 A f).
Proof. exact (eq_refl (term587 A f)). Qed.
Lemma lem3773321 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term617 A s f x) = (term618 A s f x).
Proof. exact (MK_COMB (@lem3773320 A f) (@lem3773319 A s f x)). Qed.
Lemma lem3773322 {A : Type'} (s : A -> Prop) (f : type686 A) : (term619 A s f) = (term620 A s f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3773321 A s f x)). Qed.
Lemma lem3773323 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3773324 {A : Type'} (s : A -> Prop) (f : type686 A) : (term611 A s f) = (term621 A s f).
Proof. exact (MK_COMB (@lem3773323 A) (@lem3773322 A s f)). Qed.
Lemma lem3773325 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term610 A s f) = (term611 A s f)) = ((term609 A s f) = (term621 A s f)).
Proof. exact (MK_COMB (@lem3773318 A s f) (@lem3773324 A s f)). Qed.
Lemma lem3773326 {A : Type'} (s : A -> Prop) (f : type686 A) : (term609 A s f) = (term621 A s f).
Proof. exact (EQ_MP (@lem3773325 A s f) (@lem3773310 A s f)). Qed.
Lemma lem3773328 {A : Type'} (s : A -> Prop) (f : type686 A) : (term588 A s f) = (term621 A s f).
Proof. exact (TRANS (@lem3773306 A s f) (@lem3773326 A s f)). Qed.
Lemma lem3773329 {A : Type'} (s : A -> Prop) (f : type686 A) : (term513 A s f) = (term621 A s f).
Proof. exact (TRANS (@lem3772888 A s f) (@lem3773328 A s f)). Qed.
Lemma lem3773330 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term513 A s f) : term621 A s f.
Proof. exact (EQ_MP (@lem3773329 A s f) (@lem3772756 A s f h1)). Qed.
Lemma lem3773341 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term622 A f t x) = (term623 A f t x).
Proof. exact (@lem17362 (f t) (t x)). Qed.
Lemma lem3773346 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term524 A f t x) = (term624 A f t x).
Proof. exact (@lem17265 (f t) (t x)). Qed.
Lemma lem3773347 {A : Type'} (P : type686 A) : (term575 A P) = (term576 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3773348 {A : Type'} (f : type686 A) (x : A) : (term625 A f x) = (term626 A f x).
Proof. exact (@lem3773347 A (term526 A f x)). Qed.
Lemma lem3773349 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term627 A f x t) = (term524 A f t x).
Proof. exact (eq_refl (term627 A f x t)). Qed.
Lemma lem3773350 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3773351 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term628 A f x t) = (term622 A f t x).
Proof. exact (MK_COMB (@lem3773350) (@lem3773349 A f t x)). Qed.
Lemma lem3773352 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term628 A f x t) = (term623 A f t x).
Proof. exact (TRANS (@lem3773351 A f t x) (@lem3773341 A f t x)). Qed.
Lemma lem3773353 {A : Type'} (f : type686 A) (x : A) : (term629 A f x) = (term630 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3773352 A f t x)). Qed.
Lemma lem3773354 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3773355 {A : Type'} (f : type686 A) (x : A) : (term626 A f x) = (term631 A f x).
Proof. exact (MK_COMB (@lem3773354 A) (@lem3773353 A f x)). Qed.
Lemma lem3773356 {A : Type'} (f : type686 A) (x : A) : (term625 A f x) = (term631 A f x).
Proof. exact (TRANS (@lem3773348 A f x) (@lem3773355 A f x)). Qed.
Lemma lem3773357 {A : Type'} (f : type686 A) (x : A) : (term526 A f x) = (term632 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3773346 A f t x)). Qed.
Lemma lem3773358 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3773359 {A : Type'} (f : type686 A) (x : A) : (term527 A f x) = (term633 A f x).
Proof. exact (MK_COMB (@lem3773358 A) (@lem3773357 A f x)). Qed.
Lemma lem3773361 {A : Type'} (s : A -> Prop) (x : A) : (term634 A s x) = (term634 A s x).
Proof. exact (eq_refl (term634 A s x)). Qed.
Lemma lem3773362 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term635 A s f x) = (term636 A s f x).
Proof. exact (MK_COMB (@lem3773361 A s x) (@lem3773356 A f x)). Qed.
Lemma lem3773363 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term637 A s f x) = (term635 A s f x).
Proof. exact (@lem17045 (s x) (term527 A f x)). Qed.
Lemma lem3773364 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term637 A s f x) = (term636 A s f x).
Proof. exact (TRANS (@lem3773363 A s f x) (@lem3773362 A s f x)). Qed.
Lemma lem3773366 {A : Type'} (s : A -> Prop) (x : A) : (term520 A s x) = (term520 A s x).
Proof. exact (eq_refl (term520 A s x)). Qed.
Lemma lem3773367 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term528 A s f x) = (term638 A s f x).
Proof. exact (MK_COMB (@lem3773366 A s x) (@lem3773359 A f x)). Qed.
Lemma lem3773368 {A : Type'} (s : A -> Prop) (x : A) : (term639 A s x) = (term639 A s x).
Proof. exact (eq_refl (term639 A s x)). Qed.
Lemma lem3773369 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3773370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3773371 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term640 A s f x) = (term641 A s f x).
Proof. exact (MK_COMB (@lem3773370) (@lem3773364 A s f x)). Qed.
Lemma lem3773372 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term642 A f s x) = (term643 A f s x).
Proof. exact (MK_COMB (@lem3773371 A s f x) (@lem3773369 A s x)). Qed.
Lemma lem3773373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3773374 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term644 A s f x) = (term645 A s f x).
Proof. exact (MK_COMB (@lem3773373) (@lem3773367 A s f x)). Qed.
Lemma lem3773375 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term646 A f s x) = (term647 A f s x).
Proof. exact (MK_COMB (@lem3773374 A s f x) (@lem3773368 A s x)). Qed.
Lemma lem3773376 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3773377 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term648 A f s x) = (term649 A f s x).
Proof. exact (MK_COMB (@lem3773376) (@lem3773375 A f s x)). Qed.
Lemma lem3773378 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term650 A f s x) = (term651 A f s x).
Proof. exact (MK_COMB (@lem3773377 A f s x) (@lem3773372 A f s x)). Qed.
Lemma lem3773379 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term652 A f s x) = (term650 A f s x).
Proof. exact (@lem17646 (term528 A s f x) (s x)). Qed.
Lemma lem3773380 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term652 A f s x) = (term651 A f s x).
Proof. exact (TRANS (@lem3773379 A f s x) (@lem3773378 A f s x)). Qed.
Lemma lem3773381 {A : Type'} (P : A -> Prop) : (term653 A P) = (term654 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3773382 {A : Type'} (f : type686 A) (s : A -> Prop) : (term655 A f s) = (term656 A f s).
Proof. exact (@lem3773381 A (term532 A f s)). Qed.
Lemma lem3773383 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term657 A f s x) = ((term528 A s f x) = (s x)).
Proof. exact (eq_refl (term657 A f s x)). Qed.
Lemma lem3773384 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3773385 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term658 A f s x) = (term652 A f s x).
Proof. exact (MK_COMB (@lem3773384) (@lem3773383 A f s x)). Qed.
Lemma lem3773386 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term658 A f s x) = (term651 A f s x).
Proof. exact (TRANS (@lem3773385 A f s x) (@lem3773380 A f s x)). Qed.
Lemma lem3773387 {A : Type'} (f : type686 A) (s : A -> Prop) : (term659 A f s) = (term660 A f s).
Proof. exact (fun_ext (fun x : A => @lem3773386 A f s x)). Qed.
Lemma lem3773388 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3773389 {A : Type'} (f : type686 A) (s : A -> Prop) : (term656 A f s) = (term661 A f s).
Proof. exact (MK_COMB (@lem3773388 A) (@lem3773387 A f s)). Qed.
Lemma lem3773390 {A : Type'} (f : type686 A) (s : A -> Prop) : (term655 A f s) = (term661 A f s).
Proof. exact (TRANS (@lem3773382 A f s) (@lem3773389 A f s)). Qed.
Lemma lem3773401 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term622 A f t x) = (term623 A f t x).
Proof. exact (@lem17362 (f t) (t x)). Qed.
Lemma lem3773406 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term524 A f t x) = (term624 A f t x).
Proof. exact (@lem17265 (f t) (t x)). Qed.
Lemma lem3773407 {A : Type'} (P : type686 A) : (term575 A P) = (term576 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3773408 {A : Type'} (f : type686 A) (x : A) : (term625 A f x) = (term626 A f x).
Proof. exact (@lem3773407 A (term526 A f x)). Qed.
Lemma lem3773409 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term627 A f x t) = (term524 A f t x).
Proof. exact (eq_refl (term627 A f x t)). Qed.
Lemma lem3773410 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3773411 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term628 A f x t) = (term622 A f t x).
Proof. exact (MK_COMB (@lem3773410) (@lem3773409 A f t x)). Qed.
Lemma lem3773412 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term628 A f x t) = (term623 A f t x).
Proof. exact (TRANS (@lem3773411 A f t x) (@lem3773401 A f t x)). Qed.
Lemma lem3773413 {A : Type'} (f : type686 A) (x : A) : (term629 A f x) = (term630 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3773412 A f t x)). Qed.
Lemma lem3773414 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3773415 {A : Type'} (f : type686 A) (x : A) : (term626 A f x) = (term631 A f x).
Proof. exact (MK_COMB (@lem3773414 A) (@lem3773413 A f x)). Qed.
Lemma lem3773416 {A : Type'} (f : type686 A) (x : A) : (term625 A f x) = (term631 A f x).
Proof. exact (TRANS (@lem3773408 A f x) (@lem3773415 A f x)). Qed.
Lemma lem3773417 {A : Type'} (f : type686 A) (x : A) : (term526 A f x) = (term632 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3773406 A f t x)). Qed.
Lemma lem3773418 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3773419 {A : Type'} (f : type686 A) (x : A) : (term527 A f x) = (term633 A f x).
Proof. exact (MK_COMB (@lem3773418 A) (@lem3773417 A f x)). Qed.
Lemma lem3773421 {A : Type'} (s : A -> Prop) (x : A) : (term634 A s x) = (term634 A s x).
Proof. exact (eq_refl (term634 A s x)). Qed.
Lemma lem3773422 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term635 A s f x) = (term636 A s f x).
Proof. exact (MK_COMB (@lem3773421 A s x) (@lem3773416 A f x)). Qed.
Lemma lem3773423 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term637 A s f x) = (term635 A s f x).
Proof. exact (@lem17045 (s x) (term527 A f x)). Qed.
Lemma lem3773424 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term637 A s f x) = (term636 A s f x).
Proof. exact (TRANS (@lem3773423 A s f x) (@lem3773422 A s f x)). Qed.
Lemma lem3773426 {A : Type'} (s : A -> Prop) (x : A) : (term520 A s x) = (term520 A s x).
Proof. exact (eq_refl (term520 A s x)). Qed.
Lemma lem3773427 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term528 A s f x) = (term638 A s f x).
Proof. exact (MK_COMB (@lem3773426 A s x) (@lem3773419 A f x)). Qed.
Lemma lem3773436 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term622 A f t x) = (term623 A f t x).
Proof. exact (@lem17362 (f t) (t x)). Qed.
Lemma lem3773441 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term524 A f t x) = (term624 A f t x).
Proof. exact (@lem17265 (f t) (t x)). Qed.
Lemma lem3773442 {A : Type'} (P : type686 A) : (term575 A P) = (term576 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3773443 {A : Type'} (f : type686 A) (x : A) : (term625 A f x) = (term626 A f x).
Proof. exact (@lem3773442 A (term526 A f x)). Qed.
Lemma lem3773444 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term627 A f x t) = (term524 A f t x).
Proof. exact (eq_refl (term627 A f x t)). Qed.
Lemma lem3773445 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3773446 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term628 A f x t) = (term622 A f t x).
Proof. exact (MK_COMB (@lem3773445) (@lem3773444 A f t x)). Qed.
Lemma lem3773447 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term628 A f x t) = (term623 A f t x).
Proof. exact (TRANS (@lem3773446 A f t x) (@lem3773436 A f t x)). Qed.
Lemma lem3773448 {A : Type'} (f : type686 A) (x : A) : (term629 A f x) = (term630 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3773447 A f t x)). Qed.
Lemma lem3773449 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3773450 {A : Type'} (f : type686 A) (x : A) : (term626 A f x) = (term631 A f x).
Proof. exact (MK_COMB (@lem3773449 A) (@lem3773448 A f x)). Qed.
Lemma lem3773451 {A : Type'} (f : type686 A) (x : A) : (term625 A f x) = (term631 A f x).
Proof. exact (TRANS (@lem3773443 A f x) (@lem3773450 A f x)). Qed.
Lemma lem3773452 {A : Type'} (f : type686 A) (x : A) : (term526 A f x) = (term632 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3773441 A f t x)). Qed.
Lemma lem3773453 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3773454 {A : Type'} (f : type686 A) (x : A) : (term527 A f x) = (term633 A f x).
Proof. exact (MK_COMB (@lem3773453 A) (@lem3773452 A f x)). Qed.
Lemma lem3773455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3773456 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term640 A s f x) = (term641 A s f x).
Proof. exact (MK_COMB (@lem3773455) (@lem3773424 A s f x)). Qed.
Lemma lem3773457 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term662 A s f x) = (term663 A s f x).
Proof. exact (MK_COMB (@lem3773456 A s f x) (@lem3773454 A f x)). Qed.
Lemma lem3773458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3773459 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term644 A s f x) = (term645 A s f x).
Proof. exact (MK_COMB (@lem3773458) (@lem3773427 A s f x)). Qed.
Lemma lem3773460 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term664 A s f x) = (term665 A s f x).
Proof. exact (MK_COMB (@lem3773459 A s f x) (@lem3773451 A f x)). Qed.
Lemma lem3773461 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3773462 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term666 A s f x) = (term667 A s f x).
Proof. exact (MK_COMB (@lem3773461) (@lem3773460 A s f x)). Qed.
Lemma lem3773463 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term668 A s f x) = (term669 A s f x).
Proof. exact (MK_COMB (@lem3773462 A s f x) (@lem3773457 A s f x)). Qed.
Lemma lem3773464 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term670 A s f x) = (term668 A s f x).
Proof. exact (@lem17646 (term528 A s f x) (term527 A f x)). Qed.
Lemma lem3773465 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term670 A s f x) = (term669 A s f x).
Proof. exact (TRANS (@lem3773464 A s f x) (@lem3773463 A s f x)). Qed.
Lemma lem3773466 {A : Type'} (P : A -> Prop) : (term653 A P) = (term654 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3773467 {A : Type'} (s : A -> Prop) (f : type686 A) : (term671 A s f) = (term672 A s f).
Proof. exact (@lem3773466 A (term536 A s f)). Qed.
Lemma lem3773468 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term673 A s f x) = ((term528 A s f x) = (term527 A f x)).
Proof. exact (eq_refl (term673 A s f x)). Qed.
Lemma lem3773469 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3773470 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term674 A s f x) = (term670 A s f x).
Proof. exact (MK_COMB (@lem3773469) (@lem3773468 A s f x)). Qed.
Lemma lem3773471 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term674 A s f x) = (term669 A s f x).
Proof. exact (TRANS (@lem3773470 A s f x) (@lem3773465 A s f x)). Qed.
Lemma lem3773472 {A : Type'} (s : A -> Prop) (f : type686 A) : (term675 A s f) = (term676 A s f).
Proof. exact (fun_ext (fun x : A => @lem3773471 A s f x)). Qed.
Lemma lem3773473 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3773474 {A : Type'} (s : A -> Prop) (f : type686 A) : (term672 A s f) = (term677 A s f).
Proof. exact (MK_COMB (@lem3773473 A) (@lem3773472 A s f)). Qed.
Lemma lem3773475 {A : Type'} (s : A -> Prop) (f : type686 A) : (term671 A s f) = (term677 A s f).
Proof. exact (TRANS (@lem3773467 A s f) (@lem3773474 A s f)). Qed.
Lemma lem3773476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3773477 {A : Type'} (f : type686 A) (s : A -> Prop) : (term678 A f s) = (term679 A f s).
Proof. exact (MK_COMB (@lem3773476) (@lem3773390 A f s)). Qed.
Lemma lem3773478 {A : Type'} (s : A -> Prop) (f : type686 A) : (term680 A s f) = (term681 A s f).
Proof. exact (MK_COMB (@lem3773477 A f s) (@lem3773475 A s f)). Qed.
Lemma lem3773479 {A : Type'} (s : A -> Prop) (f : type686 A) : (term555 A s f) = (term680 A s f).
Proof. exact (@lem17160 (term533 A f s) (term537 A s f)). Qed.
Lemma lem3773480 {A : Type'} (s : A -> Prop) (f : type686 A) : (term555 A s f) = (term681 A s f).
Proof. exact (TRANS (@lem3773479 A s f) (@lem3773478 A s f)). Qed.
Lemma lem3773482 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term682 A P Q) = (term683 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3773483 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term682 A P Q) = (term683 A P Q).
Proof. exact (@lem3773482 A P Q). Qed.
Lemma lem3773484 {A : Type'} (f : type686 A) (s : A -> Prop) : (term684 A f s) = (term685 A f s).
Proof. exact (@lem3773483 A (term686 A f s) (term687 A f s)). Qed.
Lemma lem3773485 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term688 A f s x) = (term647 A f s x).
Proof. exact (eq_refl (term688 A f s x)). Qed.
Lemma lem3773486 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3773487 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term689 A f s x) = (term649 A f s x).
Proof. exact (MK_COMB (@lem3773486) (@lem3773485 A f s x)). Qed.
Lemma lem3773488 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term690 A f s x) = (term643 A f s x).
Proof. exact (eq_refl (term690 A f s x)). Qed.
Lemma lem3773489 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term691 A f s x) = (term651 A f s x).
Proof. exact (MK_COMB (@lem3773487 A f s x) (@lem3773488 A f s x)). Qed.
Lemma lem3773490 {A : Type'} (f : type686 A) (s : A -> Prop) : (term692 A f s) = (term660 A f s).
Proof. exact (fun_ext (fun x : A => @lem3773489 A f s x)). Qed.
Lemma lem3773491 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3773492 {A : Type'} (f : type686 A) (s : A -> Prop) : (term684 A f s) = (term661 A f s).
Proof. exact (MK_COMB (@lem3773491 A) (@lem3773490 A f s)). Qed.
Lemma lem3773493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3773494 {A : Type'} (f : type686 A) (s : A -> Prop) : (term693 A f s) = (term694 A f s).
Proof. exact (MK_COMB (@lem3773493) (@lem3773492 A f s)). Qed.
Lemma lem3773495 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term688 A f s x) = (term647 A f s x).
Proof. exact (eq_refl (term688 A f s x)). Qed.
Lemma lem3773496 {A : Type'} (f : type686 A) (s : A -> Prop) : (term695 A f s) = (term686 A f s).
Proof. exact (fun_ext (fun x : A => @lem3773495 A f s x)). Qed.
Lemma lem3773497 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3773498 {A : Type'} (f : type686 A) (s : A -> Prop) : (term696 A f s) = (term697 A f s).
Proof. exact (MK_COMB (@lem3773497 A) (@lem3773496 A f s)). Qed.
Lemma lem3773499 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3773500 {A : Type'} (f : type686 A) (s : A -> Prop) : (term698 A f s) = (term699 A f s).
Proof. exact (MK_COMB (@lem3773499) (@lem3773498 A f s)). Qed.
Lemma lem3773501 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term690 A f s x) = (term643 A f s x).
Proof. exact (eq_refl (term690 A f s x)). Qed.
Lemma lem3773502 {A : Type'} (f : type686 A) (s : A -> Prop) : (term700 A f s) = (term687 A f s).
Proof. exact (fun_ext (fun x : A => @lem3773501 A f s x)). Qed.
Lemma lem3773503 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3773504 {A : Type'} (f : type686 A) (s : A -> Prop) : (term701 A f s) = (term702 A f s).
Proof. exact (MK_COMB (@lem3773503 A) (@lem3773502 A f s)). Qed.
Lemma lem3773505 {A : Type'} (f : type686 A) (s : A -> Prop) : (term685 A f s) = (term703 A f s).
Proof. exact (MK_COMB (@lem3773500 A f s) (@lem3773504 A f s)). Qed.
Lemma lem3773506 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term684 A f s) = (term685 A f s)) = ((term661 A f s) = (term703 A f s)).
Proof. exact (MK_COMB (@lem3773494 A f s) (@lem3773505 A f s)). Qed.
Lemma lem3773507 {A : Type'} (f : type686 A) (s : A -> Prop) : (term661 A f s) = (term703 A f s).
Proof. exact (EQ_MP (@lem3773506 A f s) (@lem3773484 A f s)). Qed.
Lemma lem3773664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3773665 {A : Type'} (f : type686 A) (s : A -> Prop) : (term679 A f s) = (term704 A f s).
Proof. exact (MK_COMB (@lem3773664) (@lem3773507 A f s)). Qed.
Lemma lem3773667 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term682 A P Q) = (term683 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3773668 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term682 A P Q) = (term683 A P Q).
Proof. exact (@lem3773667 A P Q). Qed.
Lemma lem3773669 {A : Type'} (s : A -> Prop) (f : type686 A) : (term705 A s f) = (term706 A s f).
Proof. exact (@lem3773668 A (term707 A s f) (term708 A s f)). Qed.
Lemma lem3773670 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term709 A s f x) = (term665 A s f x).
Proof. exact (eq_refl (term709 A s f x)). Qed.
Lemma lem3773671 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3773672 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term710 A s f x) = (term667 A s f x).
Proof. exact (MK_COMB (@lem3773671) (@lem3773670 A s f x)). Qed.
Lemma lem3773673 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term711 A s f x) = (term663 A s f x).
Proof. exact (eq_refl (term711 A s f x)). Qed.
Lemma lem3773674 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term712 A s f x) = (term669 A s f x).
Proof. exact (MK_COMB (@lem3773672 A s f x) (@lem3773673 A s f x)). Qed.
Lemma lem3773675 {A : Type'} (s : A -> Prop) (f : type686 A) : (term713 A s f) = (term676 A s f).
Proof. exact (fun_ext (fun x : A => @lem3773674 A s f x)). Qed.
Lemma lem3773676 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3773677 {A : Type'} (s : A -> Prop) (f : type686 A) : (term705 A s f) = (term677 A s f).
Proof. exact (MK_COMB (@lem3773676 A) (@lem3773675 A s f)). Qed.
Lemma lem3773678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3773679 {A : Type'} (s : A -> Prop) (f : type686 A) : (term714 A s f) = (term715 A s f).
Proof. exact (MK_COMB (@lem3773678) (@lem3773677 A s f)). Qed.
Lemma lem3773680 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term709 A s f x) = (term665 A s f x).
Proof. exact (eq_refl (term709 A s f x)). Qed.
Lemma lem3773681 {A : Type'} (s : A -> Prop) (f : type686 A) : (term716 A s f) = (term707 A s f).
Proof. exact (fun_ext (fun x : A => @lem3773680 A s f x)). Qed.
Lemma lem3773682 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3773683 {A : Type'} (s : A -> Prop) (f : type686 A) : (term717 A s f) = (term718 A s f).
Proof. exact (MK_COMB (@lem3773682 A) (@lem3773681 A s f)). Qed.
Lemma lem3773684 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3773685 {A : Type'} (s : A -> Prop) (f : type686 A) : (term719 A s f) = (term720 A s f).
Proof. exact (MK_COMB (@lem3773684) (@lem3773683 A s f)). Qed.
Lemma lem3773686 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term711 A s f x) = (term663 A s f x).
Proof. exact (eq_refl (term711 A s f x)). Qed.
Lemma lem3773687 {A : Type'} (s : A -> Prop) (f : type686 A) : (term721 A s f) = (term708 A s f).
Proof. exact (fun_ext (fun x : A => @lem3773686 A s f x)). Qed.
Lemma lem3773688 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3773689 {A : Type'} (s : A -> Prop) (f : type686 A) : (term722 A s f) = (term723 A s f).
Proof. exact (MK_COMB (@lem3773688 A) (@lem3773687 A s f)). Qed.
Lemma lem3773690 {A : Type'} (s : A -> Prop) (f : type686 A) : (term706 A s f) = (term724 A s f).
Proof. exact (MK_COMB (@lem3773685 A s f) (@lem3773689 A s f)). Qed.
Lemma lem3773691 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term705 A s f) = (term706 A s f)) = ((term677 A s f) = (term724 A s f)).
Proof. exact (MK_COMB (@lem3773679 A s f) (@lem3773690 A s f)). Qed.
Lemma lem3773692 {A : Type'} (s : A -> Prop) (f : type686 A) : (term677 A s f) = (term724 A s f).
Proof. exact (EQ_MP (@lem3773691 A s f) (@lem3773669 A s f)). Qed.
Lemma lem3773941 {A : Type'} (s : A -> Prop) (f : type686 A) : (term681 A s f) = (term725 A s f).
Proof. exact (MK_COMB (@lem3773665 A f s) (@lem3773692 A s f)). Qed.
Lemma lem3773943 {A : Type'} (P : Prop) (Q : A -> Prop) : (term726 A P Q) = (term727 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3773944 {A : Type'} (P : Prop) (Q : type686 A) : (term728 A P Q) = (term729 A P Q).
Proof. exact (@lem3773943 (A -> Prop) P Q). Qed.
Lemma lem3773945 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term730 A s f x) = (term731 A s f x).
Proof. exact (@lem3773944 A (term639 A s x) (term630 A f x)). Qed.
Lemma lem3773946 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term732 A f x t) = (term623 A f t x).
Proof. exact (eq_refl (term732 A f x t)). Qed.
Lemma lem3773947 {A : Type'} (f : type686 A) (x : A) : (term733 A f x) = (term630 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3773946 A f t x)). Qed.
Lemma lem3773948 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3773949 {A : Type'} (f : type686 A) (x : A) : (term734 A f x) = (term631 A f x).
Proof. exact (MK_COMB (@lem3773948 A) (@lem3773947 A f x)). Qed.
Lemma lem3773950 {A : Type'} (s : A -> Prop) (x : A) : (term634 A s x) = (term634 A s x).
Proof. exact (eq_refl (term634 A s x)). Qed.
Lemma lem3773951 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term730 A s f x) = (term636 A s f x).
Proof. exact (MK_COMB (@lem3773950 A s x) (@lem3773949 A f x)). Qed.
Lemma lem3773952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3773953 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term735 A s f x) = (term736 A s f x).
Proof. exact (MK_COMB (@lem3773952) (@lem3773951 A s f x)). Qed.
Lemma lem3773954 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term732 A f x t) = (term623 A f t x).
Proof. exact (eq_refl (term732 A f x t)). Qed.
Lemma lem3773955 {A : Type'} (s : A -> Prop) (x : A) : (term634 A s x) = (term634 A s x).
Proof. exact (eq_refl (term634 A s x)). Qed.
Lemma lem3773956 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term737 A s f x t) = (term738 A s f t x).
Proof. exact (MK_COMB (@lem3773955 A s x) (@lem3773954 A f t x)). Qed.
Lemma lem3773957 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term739 A s f x) = (term740 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3773956 A s f t x)). Qed.
Lemma lem3773958 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3773959 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term731 A s f x) = (term741 A s f x).
Proof. exact (MK_COMB (@lem3773958 A) (@lem3773957 A s f x)). Qed.
Lemma lem3773960 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term730 A s f x) = (term731 A s f x)) = ((term636 A s f x) = (term741 A s f x)).
Proof. exact (MK_COMB (@lem3773953 A s f x) (@lem3773959 A s f x)). Qed.
Lemma lem3773961 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term636 A s f x) = (term741 A s f x).
Proof. exact (EQ_MP (@lem3773960 A s f x) (@lem3773945 A s f x)). Qed.
Lemma lem3773962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3773963 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term641 A s f x) = (term742 A s f x).
Proof. exact (MK_COMB (@lem3773962) (@lem3773961 A s f x)). Qed.
Lemma lem3773964 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3773965 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term643 A f s x) = (term743 A f s x).
Proof. exact (MK_COMB (@lem3773963 A s f x) (@lem3773964 A s x)). Qed.
Lemma lem3773967 {A : Type'} (P : A -> Prop) (Q : Prop) : (term744 A P Q) = (term745 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3773968 {A : Type'} (P : type686 A) (Q : Prop) : (term746 A P Q) = (term747 A P Q).
Proof. exact (@lem3773967 (A -> Prop) P Q). Qed.
Lemma lem3773969 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term748 A f s x) = (term749 A f s x).
Proof. exact (@lem3773968 A (term740 A s f x) (s x)). Qed.
Lemma lem3773970 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term750 A s f x t) = (term738 A s f t x).
Proof. exact (eq_refl (term750 A s f x t)). Qed.
Lemma lem3773971 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term751 A s f x) = (term740 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3773970 A s f t x)). Qed.
Lemma lem3773972 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3773973 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term752 A s f x) = (term741 A s f x).
Proof. exact (MK_COMB (@lem3773972 A) (@lem3773971 A s f x)). Qed.
Lemma lem3773974 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3773975 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term753 A s f x) = (term742 A s f x).
Proof. exact (MK_COMB (@lem3773974) (@lem3773973 A s f x)). Qed.
Lemma lem3773976 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3773977 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term748 A f s x) = (term743 A f s x).
Proof. exact (MK_COMB (@lem3773975 A s f x) (@lem3773976 A s x)). Qed.
Lemma lem3773978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3773979 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term754 A f s x) = (term755 A f s x).
Proof. exact (MK_COMB (@lem3773978) (@lem3773977 A f s x)). Qed.
Lemma lem3773980 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term750 A s f x t) = (term738 A s f t x).
Proof. exact (eq_refl (term750 A s f x t)). Qed.
Lemma lem3773981 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3773982 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term756 A s f x t) = (term757 A s f t x).
Proof. exact (MK_COMB (@lem3773981) (@lem3773980 A s f t x)). Qed.
Lemma lem3773983 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3773984 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term758 A f t s x) = (term759 A f t s x).
Proof. exact (MK_COMB (@lem3773982 A s f t x) (@lem3773983 A s x)). Qed.
Lemma lem3773985 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term760 A f s x) = (term761 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3773984 A f t s x)). Qed.
Lemma lem3773986 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3773987 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term749 A f s x) = (term762 A f s x).
Proof. exact (MK_COMB (@lem3773986 A) (@lem3773985 A f s x)). Qed.
Lemma lem3773988 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term748 A f s x) = (term749 A f s x)) = ((term743 A f s x) = (term762 A f s x)).
Proof. exact (MK_COMB (@lem3773979 A f s x) (@lem3773987 A f s x)). Qed.
Lemma lem3773989 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term743 A f s x) = (term762 A f s x).
Proof. exact (EQ_MP (@lem3773988 A f s x) (@lem3773969 A f s x)). Qed.
Lemma lem3773990 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term643 A f s x) = (term762 A f s x).
Proof. exact (TRANS (@lem3773965 A f s x) (@lem3773989 A f s x)). Qed.
Lemma lem3773991 {A : Type'} (f : type686 A) (s : A -> Prop) : (term687 A f s) = (term763 A f s).
Proof. exact (fun_ext (fun x : A => @lem3773990 A f s x)). Qed.
Lemma lem3773992 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3773993 {A : Type'} (f : type686 A) (s : A -> Prop) : (term702 A f s) = (term764 A f s).
Proof. exact (MK_COMB (@lem3773992 A) (@lem3773991 A f s)). Qed.
Lemma lem3773994 {A : Type'} (f : type686 A) (s : A -> Prop) : (term699 A f s) = (term699 A f s).
Proof. exact (eq_refl (term699 A f s)). Qed.
Lemma lem3773995 {A : Type'} (f : type686 A) (s : A -> Prop) : (term703 A f s) = (term765 A f s).
Proof. exact (MK_COMB (@lem3773994 A f s) (@lem3773993 A f s)). Qed.
Lemma lem3773997 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term683 A P Q) = (term682 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3773998 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term683 A P Q) = (term682 A P Q).
Proof. exact (@lem3773997 A P Q). Qed.
Lemma lem3773999 {A : Type'} (f : type686 A) (s : A -> Prop) : (term766 A f s) = (term767 A f s).
Proof. exact (@lem3773998 A (term686 A f s) (term763 A f s)). Qed.
Lemma lem3774000 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term688 A f s x) = (term647 A f s x).
Proof. exact (eq_refl (term688 A f s x)). Qed.
Lemma lem3774001 {A : Type'} (f : type686 A) (s : A -> Prop) : (term695 A f s) = (term686 A f s).
Proof. exact (fun_ext (fun x : A => @lem3774000 A f s x)). Qed.
Lemma lem3774002 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774003 {A : Type'} (f : type686 A) (s : A -> Prop) : (term696 A f s) = (term697 A f s).
Proof. exact (MK_COMB (@lem3774002 A) (@lem3774001 A f s)). Qed.
Lemma lem3774004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774005 {A : Type'} (f : type686 A) (s : A -> Prop) : (term698 A f s) = (term699 A f s).
Proof. exact (MK_COMB (@lem3774004) (@lem3774003 A f s)). Qed.
Lemma lem3774006 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term768 A f s x) = (term762 A f s x).
Proof. exact (eq_refl (term768 A f s x)). Qed.
Lemma lem3774007 {A : Type'} (f : type686 A) (s : A -> Prop) : (term769 A f s) = (term763 A f s).
Proof. exact (fun_ext (fun x : A => @lem3774006 A f s x)). Qed.
Lemma lem3774008 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774009 {A : Type'} (f : type686 A) (s : A -> Prop) : (term770 A f s) = (term764 A f s).
Proof. exact (MK_COMB (@lem3774008 A) (@lem3774007 A f s)). Qed.
Lemma lem3774010 {A : Type'} (f : type686 A) (s : A -> Prop) : (term766 A f s) = (term765 A f s).
Proof. exact (MK_COMB (@lem3774005 A f s) (@lem3774009 A f s)). Qed.
Lemma lem3774011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3774012 {A : Type'} (f : type686 A) (s : A -> Prop) : (term771 A f s) = (term772 A f s).
Proof. exact (MK_COMB (@lem3774011) (@lem3774010 A f s)). Qed.
Lemma lem3774013 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term688 A f s x) = (term647 A f s x).
Proof. exact (eq_refl (term688 A f s x)). Qed.
Lemma lem3774014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774015 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term689 A f s x) = (term649 A f s x).
Proof. exact (MK_COMB (@lem3774014) (@lem3774013 A f s x)). Qed.
Lemma lem3774016 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term768 A f s x) = (term762 A f s x).
Proof. exact (eq_refl (term768 A f s x)). Qed.
Lemma lem3774017 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term773 A f s x) = (term774 A f s x).
Proof. exact (MK_COMB (@lem3774015 A f s x) (@lem3774016 A f s x)). Qed.
Lemma lem3774018 {A : Type'} (f : type686 A) (s : A -> Prop) : (term775 A f s) = (term776 A f s).
Proof. exact (fun_ext (fun x : A => @lem3774017 A f s x)). Qed.
Lemma lem3774019 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774020 {A : Type'} (f : type686 A) (s : A -> Prop) : (term767 A f s) = (term777 A f s).
Proof. exact (MK_COMB (@lem3774019 A) (@lem3774018 A f s)). Qed.
Lemma lem3774021 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term766 A f s) = (term767 A f s)) = ((term765 A f s) = (term777 A f s)).
Proof. exact (MK_COMB (@lem3774012 A f s) (@lem3774020 A f s)). Qed.
Lemma lem3774022 {A : Type'} (f : type686 A) (s : A -> Prop) : (term765 A f s) = (term777 A f s).
Proof. exact (EQ_MP (@lem3774021 A f s) (@lem3773999 A f s)). Qed.
Lemma lem3774024 {A : Type'} (P : Prop) (Q : A -> Prop) : (term726 A P Q) = (term727 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3774025 {A : Type'} (P : Prop) (Q : type686 A) : (term728 A P Q) = (term729 A P Q).
Proof. exact (@lem3774024 (A -> Prop) P Q). Qed.
Lemma lem3774026 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term778 A f s x) = (term779 A f s x).
Proof. exact (@lem3774025 A (term647 A f s x) (term761 A f s x)). Qed.
Lemma lem3774027 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term780 A f s x t) = (term759 A f t s x).
Proof. exact (eq_refl (term780 A f s x t)). Qed.
Lemma lem3774028 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term781 A f s x) = (term761 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774027 A f t s x)). Qed.
Lemma lem3774029 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774030 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term782 A f s x) = (term762 A f s x).
Proof. exact (MK_COMB (@lem3774029 A) (@lem3774028 A f s x)). Qed.
Lemma lem3774031 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term649 A f s x) = (term649 A f s x).
Proof. exact (eq_refl (term649 A f s x)). Qed.
Lemma lem3774032 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term778 A f s x) = (term774 A f s x).
Proof. exact (MK_COMB (@lem3774031 A f s x) (@lem3774030 A f s x)). Qed.
Lemma lem3774033 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3774034 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term783 A f s x) = (term784 A f s x).
Proof. exact (MK_COMB (@lem3774033) (@lem3774032 A f s x)). Qed.
Lemma lem3774035 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term780 A f s x t) = (term759 A f t s x).
Proof. exact (eq_refl (term780 A f s x t)). Qed.
Lemma lem3774036 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term649 A f s x) = (term649 A f s x).
Proof. exact (eq_refl (term649 A f s x)). Qed.
Lemma lem3774037 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term785 A f s x t) = (term786 A f t s x).
Proof. exact (MK_COMB (@lem3774036 A f s x) (@lem3774035 A f t s x)). Qed.
Lemma lem3774038 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term787 A f s x) = (term788 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774037 A f t s x)). Qed.
Lemma lem3774039 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774040 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term779 A f s x) = (term789 A f s x).
Proof. exact (MK_COMB (@lem3774039 A) (@lem3774038 A f s x)). Qed.
Lemma lem3774041 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term778 A f s x) = (term779 A f s x)) = ((term774 A f s x) = (term789 A f s x)).
Proof. exact (MK_COMB (@lem3774034 A f s x) (@lem3774040 A f s x)). Qed.
Lemma lem3774042 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term774 A f s x) = (term789 A f s x).
Proof. exact (EQ_MP (@lem3774041 A f s x) (@lem3774026 A f s x)). Qed.
Lemma lem3774043 {A : Type'} (f : type686 A) (s : A -> Prop) : (term776 A f s) = (term790 A f s).
Proof. exact (fun_ext (fun x : A => @lem3774042 A f s x)). Qed.
Lemma lem3774044 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774045 {A : Type'} (f : type686 A) (s : A -> Prop) : (term777 A f s) = (term791 A f s).
Proof. exact (MK_COMB (@lem3774044 A) (@lem3774043 A f s)). Qed.
Lemma lem3774046 {A : Type'} (f : type686 A) (s : A -> Prop) : (term765 A f s) = (term791 A f s).
Proof. exact (TRANS (@lem3774022 A f s) (@lem3774045 A f s)). Qed.
Lemma lem3774047 {A : Type'} (f : type686 A) (s : A -> Prop) : (term703 A f s) = (term791 A f s).
Proof. exact (TRANS (@lem3773995 A f s) (@lem3774046 A f s)). Qed.
Lemma lem3774048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774049 {A : Type'} (f : type686 A) (s : A -> Prop) : (term704 A f s) = (term792 A f s).
Proof. exact (MK_COMB (@lem3774048) (@lem3774047 A f s)). Qed.
Lemma lem3774051 {A : Type'} (P : Prop) (Q : A -> Prop) : (term589 A P Q) = (term590 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3774052 {A : Type'} (P : Prop) (Q : type686 A) : (term591 A P Q) = (term592 A P Q).
Proof. exact (@lem3774051 (A -> Prop) P Q). Qed.
Lemma lem3774053 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term793 A s f x) = (term794 A s f x).
Proof. exact (@lem3774052 A (term638 A s f x) (term630 A f x)). Qed.
Lemma lem3774054 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term732 A f x t) = (term623 A f t x).
Proof. exact (eq_refl (term732 A f x t)). Qed.
Lemma lem3774055 {A : Type'} (f : type686 A) (x : A) : (term733 A f x) = (term630 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774054 A f t x)). Qed.
Lemma lem3774056 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774057 {A : Type'} (f : type686 A) (x : A) : (term734 A f x) = (term631 A f x).
Proof. exact (MK_COMB (@lem3774056 A) (@lem3774055 A f x)). Qed.
Lemma lem3774058 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term645 A s f x) = (term645 A s f x).
Proof. exact (eq_refl (term645 A s f x)). Qed.
Lemma lem3774059 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term793 A s f x) = (term665 A s f x).
Proof. exact (MK_COMB (@lem3774058 A s f x) (@lem3774057 A f x)). Qed.
Lemma lem3774060 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3774061 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term795 A s f x) = (term796 A s f x).
Proof. exact (MK_COMB (@lem3774060) (@lem3774059 A s f x)). Qed.
Lemma lem3774062 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term732 A f x t) = (term623 A f t x).
Proof. exact (eq_refl (term732 A f x t)). Qed.
Lemma lem3774063 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term645 A s f x) = (term645 A s f x).
Proof. exact (eq_refl (term645 A s f x)). Qed.
Lemma lem3774064 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term797 A s f x t) = (term798 A s f t x).
Proof. exact (MK_COMB (@lem3774063 A s f x) (@lem3774062 A f t x)). Qed.
Lemma lem3774065 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term799 A s f x) = (term800 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774064 A s f t x)). Qed.
Lemma lem3774066 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774067 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term794 A s f x) = (term801 A s f x).
Proof. exact (MK_COMB (@lem3774066 A) (@lem3774065 A s f x)). Qed.
Lemma lem3774068 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term793 A s f x) = (term794 A s f x)) = ((term665 A s f x) = (term801 A s f x)).
Proof. exact (MK_COMB (@lem3774061 A s f x) (@lem3774067 A s f x)). Qed.
Lemma lem3774069 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term665 A s f x) = (term801 A s f x).
Proof. exact (EQ_MP (@lem3774068 A s f x) (@lem3774053 A s f x)). Qed.
Lemma lem3774070 {A : Type'} (s : A -> Prop) (f : type686 A) : (term707 A s f) = (term802 A s f).
Proof. exact (fun_ext (fun x : A => @lem3774069 A s f x)). Qed.
Lemma lem3774071 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774072 {A : Type'} (s : A -> Prop) (f : type686 A) : (term718 A s f) = (term803 A s f).
Proof. exact (MK_COMB (@lem3774071 A) (@lem3774070 A s f)). Qed.
Lemma lem3774073 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774074 {A : Type'} (s : A -> Prop) (f : type686 A) : (term720 A s f) = (term804 A s f).
Proof. exact (MK_COMB (@lem3774073) (@lem3774072 A s f)). Qed.
Lemma lem3774076 {A : Type'} (P : Prop) (Q : A -> Prop) : (term726 A P Q) = (term727 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3774077 {A : Type'} (P : Prop) (Q : type686 A) : (term728 A P Q) = (term729 A P Q).
Proof. exact (@lem3774076 (A -> Prop) P Q). Qed.
Lemma lem3774078 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term730 A s f x) = (term731 A s f x).
Proof. exact (@lem3774077 A (term639 A s x) (term630 A f x)). Qed.
Lemma lem3774079 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term732 A f x t) = (term623 A f t x).
Proof. exact (eq_refl (term732 A f x t)). Qed.
Lemma lem3774080 {A : Type'} (f : type686 A) (x : A) : (term733 A f x) = (term630 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774079 A f t x)). Qed.
Lemma lem3774081 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774082 {A : Type'} (f : type686 A) (x : A) : (term734 A f x) = (term631 A f x).
Proof. exact (MK_COMB (@lem3774081 A) (@lem3774080 A f x)). Qed.
Lemma lem3774083 {A : Type'} (s : A -> Prop) (x : A) : (term634 A s x) = (term634 A s x).
Proof. exact (eq_refl (term634 A s x)). Qed.
Lemma lem3774084 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term730 A s f x) = (term636 A s f x).
Proof. exact (MK_COMB (@lem3774083 A s x) (@lem3774082 A f x)). Qed.
Lemma lem3774085 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3774086 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term735 A s f x) = (term736 A s f x).
Proof. exact (MK_COMB (@lem3774085) (@lem3774084 A s f x)). Qed.
Lemma lem3774087 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term732 A f x t) = (term623 A f t x).
Proof. exact (eq_refl (term732 A f x t)). Qed.
Lemma lem3774088 {A : Type'} (s : A -> Prop) (x : A) : (term634 A s x) = (term634 A s x).
Proof. exact (eq_refl (term634 A s x)). Qed.
Lemma lem3774089 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term737 A s f x t) = (term738 A s f t x).
Proof. exact (MK_COMB (@lem3774088 A s x) (@lem3774087 A f t x)). Qed.
Lemma lem3774090 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term739 A s f x) = (term740 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774089 A s f t x)). Qed.
Lemma lem3774091 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774092 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term731 A s f x) = (term741 A s f x).
Proof. exact (MK_COMB (@lem3774091 A) (@lem3774090 A s f x)). Qed.
Lemma lem3774093 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term730 A s f x) = (term731 A s f x)) = ((term636 A s f x) = (term741 A s f x)).
Proof. exact (MK_COMB (@lem3774086 A s f x) (@lem3774092 A s f x)). Qed.
Lemma lem3774094 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term636 A s f x) = (term741 A s f x).
Proof. exact (EQ_MP (@lem3774093 A s f x) (@lem3774078 A s f x)). Qed.
Lemma lem3774095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774096 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term641 A s f x) = (term742 A s f x).
Proof. exact (MK_COMB (@lem3774095) (@lem3774094 A s f x)). Qed.
Lemma lem3774097 {A : Type'} (f : type686 A) (x : A) : (term633 A f x) = (term633 A f x).
Proof. exact (eq_refl (term633 A f x)). Qed.
Lemma lem3774098 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term663 A s f x) = (term805 A s f x).
Proof. exact (MK_COMB (@lem3774096 A s f x) (@lem3774097 A f x)). Qed.
Lemma lem3774100 {A : Type'} (P : A -> Prop) (Q : Prop) : (term744 A P Q) = (term745 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3774101 {A : Type'} (P : type686 A) (Q : Prop) : (term746 A P Q) = (term747 A P Q).
Proof. exact (@lem3774100 (A -> Prop) P Q). Qed.
Lemma lem3774102 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term806 A s f x) = (term807 A s f x).
Proof. exact (@lem3774101 A (term740 A s f x) (term633 A f x)). Qed.
Lemma lem3774103 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term750 A s f x t) = (term738 A s f t x).
Proof. exact (eq_refl (term750 A s f x t)). Qed.
Lemma lem3774104 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term751 A s f x) = (term740 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774103 A s f t x)). Qed.
Lemma lem3774105 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774106 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term752 A s f x) = (term741 A s f x).
Proof. exact (MK_COMB (@lem3774105 A) (@lem3774104 A s f x)). Qed.
Lemma lem3774107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774108 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term753 A s f x) = (term742 A s f x).
Proof. exact (MK_COMB (@lem3774107) (@lem3774106 A s f x)). Qed.
Lemma lem3774109 {A : Type'} (f : type686 A) (x : A) : (term633 A f x) = (term633 A f x).
Proof. exact (eq_refl (term633 A f x)). Qed.
Lemma lem3774110 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term806 A s f x) = (term805 A s f x).
Proof. exact (MK_COMB (@lem3774108 A s f x) (@lem3774109 A f x)). Qed.
Lemma lem3774111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3774112 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term808 A s f x) = (term809 A s f x).
Proof. exact (MK_COMB (@lem3774111) (@lem3774110 A s f x)). Qed.
Lemma lem3774113 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term750 A s f x t) = (term738 A s f t x).
Proof. exact (eq_refl (term750 A s f x t)). Qed.
Lemma lem3774114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774115 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term756 A s f x t) = (term757 A s f t x).
Proof. exact (MK_COMB (@lem3774114) (@lem3774113 A s f t x)). Qed.
Lemma lem3774116 {A : Type'} (f : type686 A) (x : A) : (term633 A f x) = (term633 A f x).
Proof. exact (eq_refl (term633 A f x)). Qed.
Lemma lem3774117 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : type686 A) (x : A) : (term810 A s t f x) = (term811 A s t f x).
Proof. exact (MK_COMB (@lem3774115 A s f t x) (@lem3774116 A f x)). Qed.
Lemma lem3774118 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term812 A s f x) = (term813 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774117 A s t f x)). Qed.
Lemma lem3774119 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774120 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term807 A s f x) = (term814 A s f x).
Proof. exact (MK_COMB (@lem3774119 A) (@lem3774118 A s f x)). Qed.
Lemma lem3774121 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term806 A s f x) = (term807 A s f x)) = ((term805 A s f x) = (term814 A s f x)).
Proof. exact (MK_COMB (@lem3774112 A s f x) (@lem3774120 A s f x)). Qed.
Lemma lem3774122 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term805 A s f x) = (term814 A s f x).
Proof. exact (EQ_MP (@lem3774121 A s f x) (@lem3774102 A s f x)). Qed.
Lemma lem3774123 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term663 A s f x) = (term814 A s f x).
Proof. exact (TRANS (@lem3774098 A s f x) (@lem3774122 A s f x)). Qed.
Lemma lem3774124 {A : Type'} (s : A -> Prop) (f : type686 A) : (term708 A s f) = (term815 A s f).
Proof. exact (fun_ext (fun x : A => @lem3774123 A s f x)). Qed.
Lemma lem3774125 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774126 {A : Type'} (s : A -> Prop) (f : type686 A) : (term723 A s f) = (term816 A s f).
Proof. exact (MK_COMB (@lem3774125 A) (@lem3774124 A s f)). Qed.
Lemma lem3774127 {A : Type'} (s : A -> Prop) (f : type686 A) : (term724 A s f) = (term817 A s f).
Proof. exact (MK_COMB (@lem3774074 A s f) (@lem3774126 A s f)). Qed.
Lemma lem3774129 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term683 A P Q) = (term682 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3774130 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term683 A P Q) = (term682 A P Q).
Proof. exact (@lem3774129 A P Q). Qed.
Lemma lem3774131 {A : Type'} (s : A -> Prop) (f : type686 A) : (term818 A s f) = (term819 A s f).
Proof. exact (@lem3774130 A (term802 A s f) (term815 A s f)). Qed.
Lemma lem3774132 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term820 A s f x) = (term801 A s f x).
Proof. exact (eq_refl (term820 A s f x)). Qed.
Lemma lem3774133 {A : Type'} (s : A -> Prop) (f : type686 A) : (term821 A s f) = (term802 A s f).
Proof. exact (fun_ext (fun x : A => @lem3774132 A s f x)). Qed.
Lemma lem3774134 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774135 {A : Type'} (s : A -> Prop) (f : type686 A) : (term822 A s f) = (term803 A s f).
Proof. exact (MK_COMB (@lem3774134 A) (@lem3774133 A s f)). Qed.
Lemma lem3774136 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774137 {A : Type'} (s : A -> Prop) (f : type686 A) : (term823 A s f) = (term804 A s f).
Proof. exact (MK_COMB (@lem3774136) (@lem3774135 A s f)). Qed.
Lemma lem3774138 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term824 A s f x) = (term814 A s f x).
Proof. exact (eq_refl (term824 A s f x)). Qed.
Lemma lem3774139 {A : Type'} (s : A -> Prop) (f : type686 A) : (term825 A s f) = (term815 A s f).
Proof. exact (fun_ext (fun x : A => @lem3774138 A s f x)). Qed.
Lemma lem3774140 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774141 {A : Type'} (s : A -> Prop) (f : type686 A) : (term826 A s f) = (term816 A s f).
Proof. exact (MK_COMB (@lem3774140 A) (@lem3774139 A s f)). Qed.
Lemma lem3774142 {A : Type'} (s : A -> Prop) (f : type686 A) : (term818 A s f) = (term817 A s f).
Proof. exact (MK_COMB (@lem3774137 A s f) (@lem3774141 A s f)). Qed.
Lemma lem3774143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3774144 {A : Type'} (s : A -> Prop) (f : type686 A) : (term827 A s f) = (term828 A s f).
Proof. exact (MK_COMB (@lem3774143) (@lem3774142 A s f)). Qed.
Lemma lem3774145 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term820 A s f x) = (term801 A s f x).
Proof. exact (eq_refl (term820 A s f x)). Qed.
Lemma lem3774146 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774147 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term829 A s f x) = (term830 A s f x).
Proof. exact (MK_COMB (@lem3774146) (@lem3774145 A s f x)). Qed.
Lemma lem3774148 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term824 A s f x) = (term814 A s f x).
Proof. exact (eq_refl (term824 A s f x)). Qed.
Lemma lem3774149 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term831 A s f x) = (term832 A s f x).
Proof. exact (MK_COMB (@lem3774147 A s f x) (@lem3774148 A s f x)). Qed.
Lemma lem3774150 {A : Type'} (s : A -> Prop) (f : type686 A) : (term833 A s f) = (term834 A s f).
Proof. exact (fun_ext (fun x : A => @lem3774149 A s f x)). Qed.
Lemma lem3774151 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774152 {A : Type'} (s : A -> Prop) (f : type686 A) : (term819 A s f) = (term835 A s f).
Proof. exact (MK_COMB (@lem3774151 A) (@lem3774150 A s f)). Qed.
Lemma lem3774153 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term818 A s f) = (term819 A s f)) = ((term817 A s f) = (term835 A s f)).
Proof. exact (MK_COMB (@lem3774144 A s f) (@lem3774152 A s f)). Qed.
Lemma lem3774154 {A : Type'} (s : A -> Prop) (f : type686 A) : (term817 A s f) = (term835 A s f).
Proof. exact (EQ_MP (@lem3774153 A s f) (@lem3774131 A s f)). Qed.
Lemma lem3774156 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term683 A P Q) = (term682 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3774157 {A : Type'} (P : type686 A) (Q : type686 A) : (term836 A P Q) = (term837 A P Q).
Proof. exact (@lem3774156 (A -> Prop) P Q). Qed.
Lemma lem3774158 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term838 A s f x) = (term839 A s f x).
Proof. exact (@lem3774157 A (term800 A s f x) (term813 A s f x)). Qed.
Lemma lem3774159 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term840 A s f x t) = (term798 A s f t x).
Proof. exact (eq_refl (term840 A s f x t)). Qed.
Lemma lem3774160 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term841 A s f x) = (term800 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774159 A s f t x)). Qed.
Lemma lem3774161 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774162 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term842 A s f x) = (term801 A s f x).
Proof. exact (MK_COMB (@lem3774161 A) (@lem3774160 A s f x)). Qed.
Lemma lem3774163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774164 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term843 A s f x) = (term830 A s f x).
Proof. exact (MK_COMB (@lem3774163) (@lem3774162 A s f x)). Qed.
Lemma lem3774165 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : type686 A) (x : A) : (term844 A s f x t) = (term811 A s t f x).
Proof. exact (eq_refl (term844 A s f x t)). Qed.
Lemma lem3774166 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term845 A s f x) = (term813 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774165 A s t f x)). Qed.
Lemma lem3774167 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774168 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term846 A s f x) = (term814 A s f x).
Proof. exact (MK_COMB (@lem3774167 A) (@lem3774166 A s f x)). Qed.
Lemma lem3774169 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term838 A s f x) = (term832 A s f x).
Proof. exact (MK_COMB (@lem3774164 A s f x) (@lem3774168 A s f x)). Qed.
Lemma lem3774170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3774171 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term847 A s f x) = (term848 A s f x).
Proof. exact (MK_COMB (@lem3774170) (@lem3774169 A s f x)). Qed.
Lemma lem3774172 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term840 A s f x t) = (term798 A s f t x).
Proof. exact (eq_refl (term840 A s f x t)). Qed.
Lemma lem3774173 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774174 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term849 A s f x t) = (term850 A s f t x).
Proof. exact (MK_COMB (@lem3774173) (@lem3774172 A s f t x)). Qed.
Lemma lem3774175 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : type686 A) (x : A) : (term844 A s f x t) = (term811 A s t f x).
Proof. exact (eq_refl (term844 A s f x t)). Qed.
Lemma lem3774176 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : type686 A) (x : A) : (term851 A s f x t) = (term852 A s t f x).
Proof. exact (MK_COMB (@lem3774174 A s f t x) (@lem3774175 A s t f x)). Qed.
Lemma lem3774177 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term853 A s f x) = (term854 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774176 A s t f x)). Qed.
Lemma lem3774178 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774179 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term839 A s f x) = (term855 A s f x).
Proof. exact (MK_COMB (@lem3774178 A) (@lem3774177 A s f x)). Qed.
Lemma lem3774180 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term838 A s f x) = (term839 A s f x)) = ((term832 A s f x) = (term855 A s f x)).
Proof. exact (MK_COMB (@lem3774171 A s f x) (@lem3774179 A s f x)). Qed.
Lemma lem3774181 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term832 A s f x) = (term855 A s f x).
Proof. exact (EQ_MP (@lem3774180 A s f x) (@lem3774158 A s f x)). Qed.
Lemma lem3774182 {A : Type'} (s : A -> Prop) (f : type686 A) : (term834 A s f) = (term856 A s f).
Proof. exact (fun_ext (fun x : A => @lem3774181 A s f x)). Qed.
Lemma lem3774183 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774184 {A : Type'} (s : A -> Prop) (f : type686 A) : (term835 A s f) = (term857 A s f).
Proof. exact (MK_COMB (@lem3774183 A) (@lem3774182 A s f)). Qed.
Lemma lem3774185 {A : Type'} (s : A -> Prop) (f : type686 A) : (term817 A s f) = (term857 A s f).
Proof. exact (TRANS (@lem3774154 A s f) (@lem3774184 A s f)). Qed.
Lemma lem3774186 {A : Type'} (s : A -> Prop) (f : type686 A) : (term724 A s f) = (term857 A s f).
Proof. exact (TRANS (@lem3774127 A s f) (@lem3774185 A s f)). Qed.
Lemma lem3774187 {A : Type'} (s : A -> Prop) (f : type686 A) : (term725 A s f) = (term858 A s f).
Proof. exact (MK_COMB (@lem3774049 A f s) (@lem3774186 A s f)). Qed.
Lemma lem3774189 {A : Type'} (P : A -> Prop) (Q : Prop) : (term744 A P Q) = (term745 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3774190 {A : Type'} (P : A -> Prop) (Q : Prop) : (term744 A P Q) = (term745 A P Q).
Proof. exact (@lem3774189 A P Q). Qed.
Lemma lem3774191 {A : Type'} (s : A -> Prop) (f : type686 A) : (term859 A s f) = (term860 A s f).
Proof. exact (@lem3774190 A (term790 A f s) (term857 A s f)). Qed.
Lemma lem3774192 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term861 A f s x) = (term789 A f s x).
Proof. exact (eq_refl (term861 A f s x)). Qed.
Lemma lem3774193 {A : Type'} (f : type686 A) (s : A -> Prop) : (term862 A f s) = (term790 A f s).
Proof. exact (fun_ext (fun x : A => @lem3774192 A f s x)). Qed.
Lemma lem3774194 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774195 {A : Type'} (f : type686 A) (s : A -> Prop) : (term863 A f s) = (term791 A f s).
Proof. exact (MK_COMB (@lem3774194 A) (@lem3774193 A f s)). Qed.
Lemma lem3774196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774197 {A : Type'} (f : type686 A) (s : A -> Prop) : (term864 A f s) = (term792 A f s).
Proof. exact (MK_COMB (@lem3774196) (@lem3774195 A f s)). Qed.
Lemma lem3774198 {A : Type'} (s : A -> Prop) (f : type686 A) : (term857 A s f) = (term857 A s f).
Proof. exact (eq_refl (term857 A s f)). Qed.
Lemma lem3774199 {A : Type'} (s : A -> Prop) (f : type686 A) : (term859 A s f) = (term858 A s f).
Proof. exact (MK_COMB (@lem3774197 A f s) (@lem3774198 A s f)). Qed.
Lemma lem3774200 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3774201 {A : Type'} (s : A -> Prop) (f : type686 A) : (term865 A s f) = (term866 A s f).
Proof. exact (MK_COMB (@lem3774200) (@lem3774199 A s f)). Qed.
Lemma lem3774202 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term861 A f s x) = (term789 A f s x).
Proof. exact (eq_refl (term861 A f s x)). Qed.
Lemma lem3774203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774204 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term867 A f s x) = (term868 A f s x).
Proof. exact (MK_COMB (@lem3774203) (@lem3774202 A f s x)). Qed.
Lemma lem3774205 {A : Type'} (s : A -> Prop) (f : type686 A) : (term857 A s f) = (term857 A s f).
Proof. exact (eq_refl (term857 A s f)). Qed.
Lemma lem3774206 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term869 A x s f) = (term870 A x s f).
Proof. exact (MK_COMB (@lem3774204 A f s x) (@lem3774205 A s f)). Qed.
Lemma lem3774207 {A : Type'} (s : A -> Prop) (f : type686 A) : (term871 A s f) = (term872 A s f).
Proof. exact (fun_ext (fun x : A => @lem3774206 A x s f)). Qed.
Lemma lem3774208 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774209 {A : Type'} (s : A -> Prop) (f : type686 A) : (term860 A s f) = (term873 A s f).
Proof. exact (MK_COMB (@lem3774208 A) (@lem3774207 A s f)). Qed.
Lemma lem3774210 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term859 A s f) = (term860 A s f)) = ((term858 A s f) = (term873 A s f)).
Proof. exact (MK_COMB (@lem3774201 A s f) (@lem3774209 A s f)). Qed.
Lemma lem3774211 {A : Type'} (s : A -> Prop) (f : type686 A) : (term858 A s f) = (term873 A s f).
Proof. exact (EQ_MP (@lem3774210 A s f) (@lem3774191 A s f)). Qed.
Lemma lem3774213 {A : Type'} (P : A -> Prop) (Q : Prop) : (term744 A P Q) = (term745 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3774214 {A : Type'} (P : type686 A) (Q : Prop) : (term746 A P Q) = (term747 A P Q).
Proof. exact (@lem3774213 (A -> Prop) P Q). Qed.
Lemma lem3774215 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term874 A x s f) = (term875 A x s f).
Proof. exact (@lem3774214 A (term788 A f s x) (term857 A s f)). Qed.
Lemma lem3774216 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term876 A f s x t) = (term786 A f t s x).
Proof. exact (eq_refl (term876 A f s x t)). Qed.
Lemma lem3774217 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term877 A f s x) = (term788 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774216 A f t s x)). Qed.
Lemma lem3774218 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774219 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term878 A f s x) = (term789 A f s x).
Proof. exact (MK_COMB (@lem3774218 A) (@lem3774217 A f s x)). Qed.
Lemma lem3774220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774221 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term879 A f s x) = (term868 A f s x).
Proof. exact (MK_COMB (@lem3774220) (@lem3774219 A f s x)). Qed.
Lemma lem3774222 {A : Type'} (s : A -> Prop) (f : type686 A) : (term857 A s f) = (term857 A s f).
Proof. exact (eq_refl (term857 A s f)). Qed.
Lemma lem3774223 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term874 A x s f) = (term870 A x s f).
Proof. exact (MK_COMB (@lem3774221 A f s x) (@lem3774222 A s f)). Qed.
Lemma lem3774224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3774225 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term880 A x s f) = (term881 A x s f).
Proof. exact (MK_COMB (@lem3774224) (@lem3774223 A x s f)). Qed.
Lemma lem3774226 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term876 A f s x t) = (term786 A f t s x).
Proof. exact (eq_refl (term876 A f s x t)). Qed.
Lemma lem3774227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774228 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term882 A f s x t) = (term883 A f t s x).
Proof. exact (MK_COMB (@lem3774227) (@lem3774226 A f t s x)). Qed.
Lemma lem3774229 {A : Type'} (s : A -> Prop) (f : type686 A) : (term857 A s f) = (term857 A s f).
Proof. exact (eq_refl (term857 A s f)). Qed.
Lemma lem3774230 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term884 A x t s f) = (term885 A t x s f).
Proof. exact (MK_COMB (@lem3774228 A f t s x) (@lem3774229 A s f)). Qed.
Lemma lem3774231 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term886 A x s f) = (term887 A x s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774230 A t x s f)). Qed.
Lemma lem3774232 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774233 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term875 A x s f) = (term888 A x s f).
Proof. exact (MK_COMB (@lem3774232 A) (@lem3774231 A x s f)). Qed.
Lemma lem3774234 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : ((term874 A x s f) = (term875 A x s f)) = ((term870 A x s f) = (term888 A x s f)).
Proof. exact (MK_COMB (@lem3774225 A x s f) (@lem3774233 A x s f)). Qed.
Lemma lem3774235 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term870 A x s f) = (term888 A x s f).
Proof. exact (EQ_MP (@lem3774234 A x s f) (@lem3774215 A x s f)). Qed.
Lemma lem3774237 {A : Type'} (P : Prop) (Q : A -> Prop) : (term589 A P Q) = (term590 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3774238 {A : Type'} (P : Prop) (Q : A -> Prop) : (term589 A P Q) = (term590 A P Q).
Proof. exact (@lem3774237 A P Q). Qed.
Lemma lem3774239 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term889 A t x s f) = (term890 A t x s f).
Proof. exact (@lem3774238 A (term786 A f t s x) (term856 A s f)). Qed.
Lemma lem3774240 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term891 A s f x) = (term855 A s f x).
Proof. exact (eq_refl (term891 A s f x)). Qed.
Lemma lem3774241 {A : Type'} (s : A -> Prop) (f : type686 A) : (term892 A s f) = (term856 A s f).
Proof. exact (fun_ext (fun x : A => @lem3774240 A s f x)). Qed.
Lemma lem3774242 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774243 {A : Type'} (s : A -> Prop) (f : type686 A) : (term893 A s f) = (term857 A s f).
Proof. exact (MK_COMB (@lem3774242 A) (@lem3774241 A s f)). Qed.
Lemma lem3774244 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term883 A f t s x) = (term883 A f t s x).
Proof. exact (eq_refl (term883 A f t s x)). Qed.
Lemma lem3774245 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term889 A t x s f) = (term885 A t x s f).
Proof. exact (MK_COMB (@lem3774244 A f t s x) (@lem3774243 A s f)). Qed.
Lemma lem3774246 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3774247 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term894 A t x s f) = (term895 A t x s f).
Proof. exact (MK_COMB (@lem3774246) (@lem3774245 A t x s f)). Qed.
Lemma lem3774248 {A : Type'} (s : A -> Prop) (f : type686 A) (x' : A) : (term891 A s f x') = (term855 A s f x').
Proof. exact (eq_refl (term891 A s f x')). Qed.
Lemma lem3774249 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term883 A f t s x) = (term883 A f t s x).
Proof. exact (eq_refl (term883 A f t s x)). Qed.
Lemma lem3774250 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : (term896 A t x s f x') = (term897 A t x s f x').
Proof. exact (MK_COMB (@lem3774249 A f t s x) (@lem3774248 A s f x')). Qed.
Lemma lem3774251 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term898 A t x s f) = (term899 A t x s f).
Proof. exact (fun_ext (fun x' : A => @lem3774250 A t x s f x')). Qed.
Lemma lem3774252 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774253 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term890 A t x s f) = (term900 A t x s f).
Proof. exact (MK_COMB (@lem3774252 A) (@lem3774251 A t x s f)). Qed.
Lemma lem3774254 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : ((term889 A t x s f) = (term890 A t x s f)) = ((term885 A t x s f) = (term900 A t x s f)).
Proof. exact (MK_COMB (@lem3774247 A t x s f) (@lem3774253 A t x s f)). Qed.
Lemma lem3774255 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term885 A t x s f) = (term900 A t x s f).
Proof. exact (EQ_MP (@lem3774254 A t x s f) (@lem3774239 A t x s f)). Qed.
Lemma lem3774257 {A : Type'} (P : Prop) (Q : A -> Prop) : (term589 A P Q) = (term590 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3774258 {A : Type'} (P : Prop) (Q : type686 A) : (term591 A P Q) = (term592 A P Q).
Proof. exact (@lem3774257 (A -> Prop) P Q). Qed.
Lemma lem3774259 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : (term901 A t x s f x') = (term902 A t x s f x').
Proof. exact (@lem3774258 A (term786 A f t s x) (term854 A s f x')). Qed.
Lemma lem3774260 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : type686 A) (x' : A) : (term903 A s f x' t) = (term852 A s t f x').
Proof. exact (eq_refl (term903 A s f x' t)). Qed.
Lemma lem3774261 {A : Type'} (s : A -> Prop) (f : type686 A) (x' : A) : (term904 A s f x') = (term854 A s f x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774260 A s t f x')). Qed.
Lemma lem3774262 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774263 {A : Type'} (s : A -> Prop) (f : type686 A) (x' : A) : (term905 A s f x') = (term855 A s f x').
Proof. exact (MK_COMB (@lem3774262 A) (@lem3774261 A s f x')). Qed.
Lemma lem3774264 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term883 A f t s x) = (term883 A f t s x).
Proof. exact (eq_refl (term883 A f t s x)). Qed.
Lemma lem3774265 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : (term901 A t x s f x') = (term897 A t x s f x').
Proof. exact (MK_COMB (@lem3774264 A f t s x) (@lem3774263 A s f x')). Qed.
Lemma lem3774266 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3774267 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : (term906 A t x s f x') = (term907 A t x s f x').
Proof. exact (MK_COMB (@lem3774266) (@lem3774265 A t x s f x')). Qed.
Lemma lem3774268 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) : (term903 A s f x' t') = (term852 A s t' f x').
Proof. exact (eq_refl (term903 A s f x' t')). Qed.
Lemma lem3774269 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term883 A f t s x) = (term883 A f t s x).
Proof. exact (eq_refl (term883 A f t s x)). Qed.
Lemma lem3774270 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) : (term908 A t x s f x' t') = (term909 A t x s t' f x').
Proof. exact (MK_COMB (@lem3774269 A f t s x) (@lem3774268 A s t' f x')). Qed.
Lemma lem3774271 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : (term910 A t x s f x') = (term911 A t x s f x').
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3774270 A t x s t' f x')). Qed.
Lemma lem3774272 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774273 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : (term902 A t x s f x') = (term912 A t x s f x').
Proof. exact (MK_COMB (@lem3774272 A) (@lem3774271 A t x s f x')). Qed.
Lemma lem3774274 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : ((term901 A t x s f x') = (term902 A t x s f x')) = ((term897 A t x s f x') = (term912 A t x s f x')).
Proof. exact (MK_COMB (@lem3774267 A t x s f x') (@lem3774273 A t x s f x')). Qed.
Lemma lem3774275 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : (term897 A t x s f x') = (term912 A t x s f x').
Proof. exact (EQ_MP (@lem3774274 A t x s f x') (@lem3774259 A t x s f x')). Qed.
Lemma lem3774276 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term899 A t x s f) = (term913 A t x s f).
Proof. exact (fun_ext (fun x' : A => @lem3774275 A t x s f x')). Qed.
Lemma lem3774277 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774278 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term900 A t x s f) = (term914 A t x s f).
Proof. exact (MK_COMB (@lem3774277 A) (@lem3774276 A t x s f)). Qed.
Lemma lem3774279 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term885 A t x s f) = (term914 A t x s f).
Proof. exact (TRANS (@lem3774255 A t x s f) (@lem3774278 A t x s f)). Qed.
Lemma lem3774280 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term887 A x s f) = (term915 A x s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774279 A t x s f)). Qed.
Lemma lem3774281 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3774282 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term888 A x s f) = (term916 A x s f).
Proof. exact (MK_COMB (@lem3774281 A) (@lem3774280 A x s f)). Qed.
Lemma lem3774283 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term870 A x s f) = (term916 A x s f).
Proof. exact (TRANS (@lem3774235 A x s f) (@lem3774282 A x s f)). Qed.
Lemma lem3774284 {A : Type'} (s : A -> Prop) (f : type686 A) : (term872 A s f) = (term917 A s f).
Proof. exact (fun_ext (fun x : A => @lem3774283 A x s f)). Qed.
Lemma lem3774285 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3774286 {A : Type'} (s : A -> Prop) (f : type686 A) : (term873 A s f) = (term918 A s f).
Proof. exact (MK_COMB (@lem3774285 A) (@lem3774284 A s f)). Qed.
Lemma lem3774287 {A : Type'} (s : A -> Prop) (f : type686 A) : (term858 A s f) = (term918 A s f).
Proof. exact (TRANS (@lem3774211 A s f) (@lem3774286 A s f)). Qed.
Lemma lem3774288 {A : Type'} (s : A -> Prop) (f : type686 A) : (term725 A s f) = (term918 A s f).
Proof. exact (TRANS (@lem3774187 A s f) (@lem3774287 A s f)). Qed.
Lemma lem3774289 {A : Type'} (s : A -> Prop) (f : type686 A) : (term681 A s f) = (term918 A s f).
Proof. exact (TRANS (@lem3773941 A s f) (@lem3774288 A s f)). Qed.
Lemma lem3774290 {A : Type'} (s : A -> Prop) (f : type686 A) : (term555 A s f) = (term918 A s f).
Proof. exact (TRANS (@lem3773480 A s f) (@lem3774289 A s f)). Qed.
Lemma lem3774291 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term555 A s f) : term918 A s f.
Proof. exact (EQ_MP (@lem3774290 A s f) (@lem3772761 A s f h1)). Qed.
Lemma lem3774292 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) (h1 : term916 A x s f) : term916 A x s f.
Proof. exact (h1). Qed.
Lemma lem3774293 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (h1 : term914 A t x s f) : term914 A t x s f.
Proof. exact (h1). Qed.
Lemma lem3774294 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) (h1 : term912 A t x s f x') : term912 A t x s f x'.
Proof. exact (h1). Qed.
Lemma lem3774295 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term909 A t x s t' f x') : term909 A t x s t' f x'.
Proof. exact (h1). Qed.
Lemma lem3774296 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term618 A s f x''.
Proof. exact (h1). Qed.
Lemma lem3774301 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774302 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774301 A Prop f x). Qed.
Lemma lem3774304 {A : Type'} (t : A -> Prop) (x' : A) : (t x') = (@I (A -> Prop) t x').
Proof. exact (@lem3774302 A t x'). Qed.
Lemma lem3774305 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774310 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774311 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3774310 (A -> Prop) Prop f x). Qed.
Lemma lem3774313 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3774311 A f t). Qed.
Lemma lem3774314 {A : Type'} (f : type686 A) (t : A -> Prop) : (term506 A f t) = (term919 A f t).
Proof. exact (MK_COMB (@lem3774305) (@lem3774313 A f t)). Qed.
Lemma lem3774315 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774316 {A : Type'} (f : type686 A) (t : A -> Prop) : (term561 A f t) = (term920 A f t).
Proof. exact (MK_COMB (@lem3774315) (@lem3774314 A f t)). Qed.
Lemma lem3774317 {A : Type'} (f : type686 A) (t : A -> Prop) (x' : A) : (term624 A f t x') = (term921 A f t x').
Proof. exact (MK_COMB (@lem3774316 A f t) (@lem3774304 A t x')). Qed.
Lemma lem3774318 {A : Type'} (f : type686 A) (x' : A) : (term632 A f x') = (term922 A f x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774317 A f t x')). Qed.
Lemma lem3774319 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3774320 {A : Type'} (f : type686 A) (x' : A) : (term633 A f x') = (term923 A f x').
Proof. exact (MK_COMB (@lem3774319 A) (@lem3774318 A f x')). Qed.
Lemma lem3774321 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774326 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774327 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774326 A Prop f x). Qed.
Lemma lem3774329 {A : Type'} (t' : A -> Prop) (x' : A) : (t' x') = (@I (A -> Prop) t' x').
Proof. exact (@lem3774327 A t' x'). Qed.
Lemma lem3774330 {A : Type'} (t' : A -> Prop) (x' : A) : (term639 A t' x') = (term924 A t' x').
Proof. exact (MK_COMB (@lem3774321) (@lem3774329 A t' x')). Qed.
Lemma lem3774335 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774336 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3774335 (A -> Prop) Prop f x). Qed.
Lemma lem3774338 {A : Type'} (f : type686 A) (t' : A -> Prop) : (f t') = (@I ((A -> Prop) -> Prop) f t').
Proof. exact (@lem3774336 A f t'). Qed.
Lemma lem3774339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774340 {A : Type'} (f : type686 A) (t' : A -> Prop) : (term925 A f t') = (term926 A f t').
Proof. exact (MK_COMB (@lem3774339) (@lem3774338 A f t')). Qed.
Lemma lem3774341 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) : (term623 A f t' x') = (term927 A f t' x').
Proof. exact (MK_COMB (@lem3774340 A f t') (@lem3774330 A t' x')). Qed.
Lemma lem3774342 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774347 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774348 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774347 A Prop f x). Qed.
Lemma lem3774350 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem3774348 A s x'). Qed.
Lemma lem3774351 {A : Type'} (s : A -> Prop) (x' : A) : (term639 A s x') = (term924 A s x').
Proof. exact (MK_COMB (@lem3774342) (@lem3774350 A s x')). Qed.
Lemma lem3774352 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774353 {A : Type'} (s : A -> Prop) (x' : A) : (term634 A s x') = (term928 A s x').
Proof. exact (MK_COMB (@lem3774352) (@lem3774351 A s x')). Qed.
Lemma lem3774354 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) : (term738 A s f t' x') = (term929 A s f t' x').
Proof. exact (MK_COMB (@lem3774353 A s x') (@lem3774341 A f t' x')). Qed.
Lemma lem3774355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774356 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) : (term757 A s f t' x') = (term930 A s f t' x').
Proof. exact (MK_COMB (@lem3774355) (@lem3774354 A s f t' x')). Qed.
Lemma lem3774357 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) : (term811 A s t' f x') = (term931 A s t' f x').
Proof. exact (MK_COMB (@lem3774356 A s f t' x') (@lem3774320 A f x')). Qed.
Lemma lem3774358 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774363 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774364 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774363 A Prop f x). Qed.
Lemma lem3774366 {A : Type'} (t' : A -> Prop) (x' : A) : (t' x') = (@I (A -> Prop) t' x').
Proof. exact (@lem3774364 A t' x'). Qed.
Lemma lem3774367 {A : Type'} (t' : A -> Prop) (x' : A) : (term639 A t' x') = (term924 A t' x').
Proof. exact (MK_COMB (@lem3774358) (@lem3774366 A t' x')). Qed.
Lemma lem3774372 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774373 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3774372 (A -> Prop) Prop f x). Qed.
Lemma lem3774375 {A : Type'} (f : type686 A) (t' : A -> Prop) : (f t') = (@I ((A -> Prop) -> Prop) f t').
Proof. exact (@lem3774373 A f t'). Qed.
Lemma lem3774376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774377 {A : Type'} (f : type686 A) (t' : A -> Prop) : (term925 A f t') = (term926 A f t').
Proof. exact (MK_COMB (@lem3774376) (@lem3774375 A f t')). Qed.
Lemma lem3774378 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) : (term623 A f t' x') = (term927 A f t' x').
Proof. exact (MK_COMB (@lem3774377 A f t') (@lem3774367 A t' x')). Qed.
Lemma lem3774383 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774384 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774383 A Prop f x). Qed.
Lemma lem3774386 {A : Type'} (t : A -> Prop) (x' : A) : (t x') = (@I (A -> Prop) t x').
Proof. exact (@lem3774384 A t x'). Qed.
Lemma lem3774387 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774392 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774393 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3774392 (A -> Prop) Prop f x). Qed.
Lemma lem3774395 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3774393 A f t). Qed.
Lemma lem3774396 {A : Type'} (f : type686 A) (t : A -> Prop) : (term506 A f t) = (term919 A f t).
Proof. exact (MK_COMB (@lem3774387) (@lem3774395 A f t)). Qed.
Lemma lem3774397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774398 {A : Type'} (f : type686 A) (t : A -> Prop) : (term561 A f t) = (term920 A f t).
Proof. exact (MK_COMB (@lem3774397) (@lem3774396 A f t)). Qed.
Lemma lem3774399 {A : Type'} (f : type686 A) (t : A -> Prop) (x' : A) : (term624 A f t x') = (term921 A f t x').
Proof. exact (MK_COMB (@lem3774398 A f t) (@lem3774386 A t x')). Qed.
Lemma lem3774400 {A : Type'} (f : type686 A) (x' : A) : (term632 A f x') = (term922 A f x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774399 A f t x')). Qed.
Lemma lem3774401 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3774402 {A : Type'} (f : type686 A) (x' : A) : (term633 A f x') = (term923 A f x').
Proof. exact (MK_COMB (@lem3774401 A) (@lem3774400 A f x')). Qed.
Lemma lem3774407 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774408 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774407 A Prop f x). Qed.
Lemma lem3774410 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem3774408 A s x'). Qed.
Lemma lem3774411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774412 {A : Type'} (s : A -> Prop) (x' : A) : (term520 A s x') = (term932 A s x').
Proof. exact (MK_COMB (@lem3774411) (@lem3774410 A s x')). Qed.
Lemma lem3774413 {A : Type'} (s : A -> Prop) (f : type686 A) (x' : A) : (term638 A s f x') = (term933 A s f x').
Proof. exact (MK_COMB (@lem3774412 A s x') (@lem3774402 A f x')). Qed.
Lemma lem3774414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774415 {A : Type'} (s : A -> Prop) (f : type686 A) (x' : A) : (term645 A s f x') = (term934 A s f x').
Proof. exact (MK_COMB (@lem3774414) (@lem3774413 A s f x')). Qed.
Lemma lem3774416 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) : (term798 A s f t' x') = (term935 A s f t' x').
Proof. exact (MK_COMB (@lem3774415 A s f x') (@lem3774378 A f t' x')). Qed.
Lemma lem3774417 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774418 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) : (term850 A s f t' x') = (term936 A s f t' x').
Proof. exact (MK_COMB (@lem3774417) (@lem3774416 A s f t' x')). Qed.
Lemma lem3774419 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) : (term852 A s t' f x') = (term937 A s t' f x').
Proof. exact (MK_COMB (@lem3774418 A s f t' x') (@lem3774357 A s t' f x')). Qed.
Lemma lem3774424 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774425 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774424 A Prop f x). Qed.
Lemma lem3774427 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3774425 A s x). Qed.
Lemma lem3774428 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774433 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774434 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774433 A Prop f x). Qed.
Lemma lem3774436 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3774434 A t x). Qed.
Lemma lem3774437 {A : Type'} (t : A -> Prop) (x : A) : (term639 A t x) = (term924 A t x).
Proof. exact (MK_COMB (@lem3774428) (@lem3774436 A t x)). Qed.
Lemma lem3774442 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774443 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3774442 (A -> Prop) Prop f x). Qed.
Lemma lem3774445 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3774443 A f t). Qed.
Lemma lem3774446 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774447 {A : Type'} (f : type686 A) (t : A -> Prop) : (term925 A f t) = (term926 A f t).
Proof. exact (MK_COMB (@lem3774446) (@lem3774445 A f t)). Qed.
Lemma lem3774448 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term623 A f t x) = (term927 A f t x).
Proof. exact (MK_COMB (@lem3774447 A f t) (@lem3774437 A t x)). Qed.
Lemma lem3774449 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774454 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774455 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774454 A Prop f x). Qed.
Lemma lem3774457 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3774455 A s x). Qed.
Lemma lem3774458 {A : Type'} (s : A -> Prop) (x : A) : (term639 A s x) = (term924 A s x).
Proof. exact (MK_COMB (@lem3774449) (@lem3774457 A s x)). Qed.
Lemma lem3774459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774460 {A : Type'} (s : A -> Prop) (x : A) : (term634 A s x) = (term928 A s x).
Proof. exact (MK_COMB (@lem3774459) (@lem3774458 A s x)). Qed.
Lemma lem3774461 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term738 A s f t x) = (term929 A s f t x).
Proof. exact (MK_COMB (@lem3774460 A s x) (@lem3774448 A f t x)). Qed.
Lemma lem3774462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774463 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term757 A s f t x) = (term930 A s f t x).
Proof. exact (MK_COMB (@lem3774462) (@lem3774461 A s f t x)). Qed.
Lemma lem3774464 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term759 A f t s x) = (term938 A f t s x).
Proof. exact (MK_COMB (@lem3774463 A s f t x) (@lem3774427 A s x)). Qed.
Lemma lem3774465 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774470 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774471 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774470 A Prop f x). Qed.
Lemma lem3774473 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3774471 A s x). Qed.
Lemma lem3774474 {A : Type'} (s : A -> Prop) (x : A) : (term639 A s x) = (term924 A s x).
Proof. exact (MK_COMB (@lem3774465) (@lem3774473 A s x)). Qed.
Lemma lem3774479 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774480 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774479 A Prop f x). Qed.
Lemma lem3774482 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3774480 A t x). Qed.
Lemma lem3774483 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774488 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774489 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3774488 (A -> Prop) Prop f x). Qed.
Lemma lem3774491 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3774489 A f t). Qed.
Lemma lem3774492 {A : Type'} (f : type686 A) (t : A -> Prop) : (term506 A f t) = (term919 A f t).
Proof. exact (MK_COMB (@lem3774483) (@lem3774491 A f t)). Qed.
Lemma lem3774493 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774494 {A : Type'} (f : type686 A) (t : A -> Prop) : (term561 A f t) = (term920 A f t).
Proof. exact (MK_COMB (@lem3774493) (@lem3774492 A f t)). Qed.
Lemma lem3774495 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term624 A f t x) = (term921 A f t x).
Proof. exact (MK_COMB (@lem3774494 A f t) (@lem3774482 A t x)). Qed.
Lemma lem3774496 {A : Type'} (f : type686 A) (x : A) : (term632 A f x) = (term922 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774495 A f t x)). Qed.
Lemma lem3774497 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3774498 {A : Type'} (f : type686 A) (x : A) : (term633 A f x) = (term923 A f x).
Proof. exact (MK_COMB (@lem3774497 A) (@lem3774496 A f x)). Qed.
Lemma lem3774503 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774504 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774503 A Prop f x). Qed.
Lemma lem3774506 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3774504 A s x). Qed.
Lemma lem3774507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774508 {A : Type'} (s : A -> Prop) (x : A) : (term520 A s x) = (term932 A s x).
Proof. exact (MK_COMB (@lem3774507) (@lem3774506 A s x)). Qed.
Lemma lem3774509 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term638 A s f x) = (term933 A s f x).
Proof. exact (MK_COMB (@lem3774508 A s x) (@lem3774498 A f x)). Qed.
Lemma lem3774510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774511 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term645 A s f x) = (term934 A s f x).
Proof. exact (MK_COMB (@lem3774510) (@lem3774509 A s f x)). Qed.
Lemma lem3774512 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term647 A f s x) = (term939 A f s x).
Proof. exact (MK_COMB (@lem3774511 A s f x) (@lem3774474 A s x)). Qed.
Lemma lem3774513 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774514 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term649 A f s x) = (term940 A f s x).
Proof. exact (MK_COMB (@lem3774513) (@lem3774512 A f s x)). Qed.
Lemma lem3774515 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term786 A f t s x) = (term941 A f t s x).
Proof. exact (MK_COMB (@lem3774514 A f s x) (@lem3774464 A f t s x)). Qed.
Lemma lem3774516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774517 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term883 A f t s x) = (term942 A f t s x).
Proof. exact (MK_COMB (@lem3774516) (@lem3774515 A f t s x)). Qed.
Lemma lem3774518 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) : (term909 A t x s t' f x') = (term943 A t x s t' f x').
Proof. exact (MK_COMB (@lem3774517 A f t s x) (@lem3774419 A s t' f x')). Qed.
Lemma lem3774519 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term909 A t x s t' f x') : term943 A t x s t' f x'.
Proof. exact (EQ_MP (@lem3774518 A t x s t' f x') (@lem3774295 A t x s t' f x' h1)). Qed.
Lemma lem3774524 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774525 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3774524 (A -> Prop) Prop f x). Qed.
Lemma lem3774527 {A : Type'} (f : type686 A) (x'' : A -> Prop) : (f x'') = (@I ((A -> Prop) -> Prop) f x'').
Proof. exact (@lem3774525 A f x''). Qed.
Lemma lem3774532 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774533 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774532 A Prop f x). Qed.
Lemma lem3774535 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3774533 A s x). Qed.
Lemma lem3774536 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774541 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774542 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774541 A Prop f x). Qed.
Lemma lem3774544 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3774542 A t x). Qed.
Lemma lem3774545 {A : Type'} (t : A -> Prop) (x : A) : (term639 A t x) = (term924 A t x).
Proof. exact (MK_COMB (@lem3774536) (@lem3774544 A t x)). Qed.
Lemma lem3774546 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774547 {A : Type'} (t : A -> Prop) (x : A) : (term634 A t x) = (term928 A t x).
Proof. exact (MK_COMB (@lem3774546) (@lem3774545 A t x)). Qed.
Lemma lem3774548 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term556 A t s x) = (term944 A t s x).
Proof. exact (MK_COMB (@lem3774547 A t x) (@lem3774535 A s x)). Qed.
Lemma lem3774549 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term557 A t s) = (term945 A t s).
Proof. exact (fun_ext (fun x : A => @lem3774548 A t s x)). Qed.
Lemma lem3774550 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3774551 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term558 A t s) = (term946 A t s).
Proof. exact (MK_COMB (@lem3774550 A) (@lem3774549 A t s)). Qed.
Lemma lem3774556 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774557 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774556 A Prop f x). Qed.
Lemma lem3774559 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3774557 A t x). Qed.
Lemma lem3774560 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774565 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774566 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774565 A Prop f x). Qed.
Lemma lem3774568 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3774566 A s x). Qed.
Lemma lem3774569 {A : Type'} (s : A -> Prop) (x : A) : (term639 A s x) = (term924 A s x).
Proof. exact (MK_COMB (@lem3774560) (@lem3774568 A s x)). Qed.
Lemma lem3774570 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774571 {A : Type'} (s : A -> Prop) (x : A) : (term634 A s x) = (term928 A s x).
Proof. exact (MK_COMB (@lem3774570) (@lem3774569 A s x)). Qed.
Lemma lem3774572 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term556 A s t x) = (term944 A s t x).
Proof. exact (MK_COMB (@lem3774571 A s x) (@lem3774559 A t x)). Qed.
Lemma lem3774573 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term557 A s t) = (term945 A s t).
Proof. exact (fun_ext (fun x : A => @lem3774572 A s t x)). Qed.
Lemma lem3774574 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3774575 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term558 A s t) = (term946 A s t).
Proof. exact (MK_COMB (@lem3774574 A) (@lem3774573 A s t)). Qed.
Lemma lem3774576 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774577 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term559 A s t) = (term947 A s t).
Proof. exact (MK_COMB (@lem3774576) (@lem3774575 A s t)). Qed.
Lemma lem3774578 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term560 A t s) = (term948 A t s).
Proof. exact (MK_COMB (@lem3774577 A s t) (@lem3774551 A t s)). Qed.
Lemma lem3774579 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774584 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774585 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3774584 (A -> Prop) Prop f x). Qed.
Lemma lem3774587 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3774585 A f t). Qed.
Lemma lem3774588 {A : Type'} (f : type686 A) (t : A -> Prop) : (term506 A f t) = (term919 A f t).
Proof. exact (MK_COMB (@lem3774579) (@lem3774587 A f t)). Qed.
Lemma lem3774589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774590 {A : Type'} (f : type686 A) (t : A -> Prop) : (term561 A f t) = (term920 A f t).
Proof. exact (MK_COMB (@lem3774589) (@lem3774588 A f t)). Qed.
Lemma lem3774591 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term563 A f t s) = (term949 A f t s).
Proof. exact (MK_COMB (@lem3774590 A f t) (@lem3774578 A t s)). Qed.
Lemma lem3774592 {A : Type'} (f : type686 A) (s : A -> Prop) : (term564 A f s) = (term950 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774591 A f t s)). Qed.
Lemma lem3774593 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3774594 {A : Type'} (f : type686 A) (s : A -> Prop) : (term565 A f s) = (term951 A f s).
Proof. exact (MK_COMB (@lem3774593 A) (@lem3774592 A f s)). Qed.
Lemma lem3774595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774596 {A : Type'} (f : type686 A) (s : A -> Prop) : (term583 A f s) = (term952 A f s).
Proof. exact (MK_COMB (@lem3774595) (@lem3774594 A f s)). Qed.
Lemma lem3774597 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) : (term599 A s f x'') = (term953 A s f x'').
Proof. exact (MK_COMB (@lem3774596 A f s) (@lem3774527 A f x'')). Qed.
Lemma lem3774602 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774603 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774602 A Prop f x). Qed.
Lemma lem3774605 {A : Type'} (s' : A -> Prop) (x : A) : (s' x) = (@I (A -> Prop) s' x).
Proof. exact (@lem3774603 A s' x). Qed.
Lemma lem3774606 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774611 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774612 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774611 A Prop f x). Qed.
Lemma lem3774614 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3774612 A s x). Qed.
Lemma lem3774615 {A : Type'} (s : A -> Prop) (x : A) : (term639 A s x) = (term924 A s x).
Proof. exact (MK_COMB (@lem3774606) (@lem3774614 A s x)). Qed.
Lemma lem3774616 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774617 {A : Type'} (s : A -> Prop) (x : A) : (term634 A s x) = (term928 A s x).
Proof. exact (MK_COMB (@lem3774616) (@lem3774615 A s x)). Qed.
Lemma lem3774618 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term556 A s s' x) = (term944 A s s' x).
Proof. exact (MK_COMB (@lem3774617 A s x) (@lem3774605 A s' x)). Qed.
Lemma lem3774619 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term557 A s s') = (term945 A s s').
Proof. exact (fun_ext (fun x : A => @lem3774618 A s s' x)). Qed.
Lemma lem3774620 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3774621 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term558 A s s') = (term946 A s s').
Proof. exact (MK_COMB (@lem3774620 A) (@lem3774619 A s s')). Qed.
Lemma lem3774626 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774627 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774626 A Prop f x). Qed.
Lemma lem3774629 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3774627 A s x). Qed.
Lemma lem3774630 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774635 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774636 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774635 A Prop f x). Qed.
Lemma lem3774638 {A : Type'} (s' : A -> Prop) (x : A) : (s' x) = (@I (A -> Prop) s' x).
Proof. exact (@lem3774636 A s' x). Qed.
Lemma lem3774639 {A : Type'} (s' : A -> Prop) (x : A) : (term639 A s' x) = (term924 A s' x).
Proof. exact (MK_COMB (@lem3774630) (@lem3774638 A s' x)). Qed.
Lemma lem3774640 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774641 {A : Type'} (s' : A -> Prop) (x : A) : (term634 A s' x) = (term928 A s' x).
Proof. exact (MK_COMB (@lem3774640) (@lem3774639 A s' x)). Qed.
Lemma lem3774642 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term556 A s' s x) = (term944 A s' s x).
Proof. exact (MK_COMB (@lem3774641 A s' x) (@lem3774629 A s x)). Qed.
Lemma lem3774643 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term557 A s' s) = (term945 A s' s).
Proof. exact (fun_ext (fun x : A => @lem3774642 A s' s x)). Qed.
Lemma lem3774644 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3774645 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term558 A s' s) = (term946 A s' s).
Proof. exact (MK_COMB (@lem3774644 A) (@lem3774643 A s' s)). Qed.
Lemma lem3774646 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774647 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term559 A s' s) = (term947 A s' s).
Proof. exact (MK_COMB (@lem3774646) (@lem3774645 A s' s)). Qed.
Lemma lem3774648 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term560 A s s') = (term948 A s s').
Proof. exact (MK_COMB (@lem3774647 A s' s) (@lem3774621 A s s')). Qed.
Lemma lem3774649 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774654 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774655 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3774654 (A -> Prop) Prop f x). Qed.
Lemma lem3774657 {A : Type'} (f : type686 A) (s' : A -> Prop) : (f s') = (@I ((A -> Prop) -> Prop) f s').
Proof. exact (@lem3774655 A f s'). Qed.
Lemma lem3774658 {A : Type'} (f : type686 A) (s' : A -> Prop) : (term506 A f s') = (term919 A f s').
Proof. exact (MK_COMB (@lem3774649) (@lem3774657 A f s')). Qed.
Lemma lem3774659 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774660 {A : Type'} (f : type686 A) (s' : A -> Prop) : (term561 A f s') = (term920 A f s').
Proof. exact (MK_COMB (@lem3774659) (@lem3774658 A f s')). Qed.
Lemma lem3774661 {A : Type'} (f : type686 A) (s : A -> Prop) (s' : A -> Prop) : (term571 A f s s') = (term954 A f s s').
Proof. exact (MK_COMB (@lem3774660 A f s') (@lem3774648 A s s')). Qed.
Lemma lem3774662 {A : Type'} (f : type686 A) (s : A -> Prop) : (term572 A f s) = (term955 A f s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3774661 A f s s')). Qed.
Lemma lem3774663 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3774664 {A : Type'} (f : type686 A) (s : A -> Prop) : (term573 A f s) = (term956 A f s).
Proof. exact (MK_COMB (@lem3774663 A) (@lem3774662 A f s)). Qed.
Lemma lem3774665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774666 {A : Type'} (f : type686 A) (s : A -> Prop) : (term585 A f s) = (term957 A f s).
Proof. exact (MK_COMB (@lem3774665) (@lem3774664 A f s)). Qed.
Lemma lem3774667 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) : (term605 A s f x'') = (term958 A s f x'').
Proof. exact (MK_COMB (@lem3774666 A f s) (@lem3774597 A s f x'')). Qed.
Lemma lem3774672 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774673 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774672 A Prop f x). Qed.
Lemma lem3774675 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3774673 A s x). Qed.
Lemma lem3774676 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774681 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774682 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774681 A Prop f x). Qed.
Lemma lem3774684 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3774682 A t x). Qed.
Lemma lem3774685 {A : Type'} (t : A -> Prop) (x : A) : (term639 A t x) = (term924 A t x).
Proof. exact (MK_COMB (@lem3774676) (@lem3774684 A t x)). Qed.
Lemma lem3774686 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774687 {A : Type'} (t : A -> Prop) (x : A) : (term634 A t x) = (term928 A t x).
Proof. exact (MK_COMB (@lem3774686) (@lem3774685 A t x)). Qed.
Lemma lem3774688 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term556 A t s x) = (term944 A t s x).
Proof. exact (MK_COMB (@lem3774687 A t x) (@lem3774675 A s x)). Qed.
Lemma lem3774689 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term557 A t s) = (term945 A t s).
Proof. exact (fun_ext (fun x : A => @lem3774688 A t s x)). Qed.
Lemma lem3774690 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3774691 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term558 A t s) = (term946 A t s).
Proof. exact (MK_COMB (@lem3774690 A) (@lem3774689 A t s)). Qed.
Lemma lem3774696 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774697 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774696 A Prop f x). Qed.
Lemma lem3774699 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3774697 A t x). Qed.
Lemma lem3774700 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774705 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774706 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3774705 A Prop f x). Qed.
Lemma lem3774708 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3774706 A s x). Qed.
Lemma lem3774709 {A : Type'} (s : A -> Prop) (x : A) : (term639 A s x) = (term924 A s x).
Proof. exact (MK_COMB (@lem3774700) (@lem3774708 A s x)). Qed.
Lemma lem3774710 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774711 {A : Type'} (s : A -> Prop) (x : A) : (term634 A s x) = (term928 A s x).
Proof. exact (MK_COMB (@lem3774710) (@lem3774709 A s x)). Qed.
Lemma lem3774712 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term556 A s t x) = (term944 A s t x).
Proof. exact (MK_COMB (@lem3774711 A s x) (@lem3774699 A t x)). Qed.
Lemma lem3774713 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term557 A s t) = (term945 A s t).
Proof. exact (fun_ext (fun x : A => @lem3774712 A s t x)). Qed.
Lemma lem3774714 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3774715 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term558 A s t) = (term946 A s t).
Proof. exact (MK_COMB (@lem3774714 A) (@lem3774713 A s t)). Qed.
Lemma lem3774716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774717 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term559 A s t) = (term947 A s t).
Proof. exact (MK_COMB (@lem3774716) (@lem3774715 A s t)). Qed.
Lemma lem3774718 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term560 A t s) = (term948 A t s).
Proof. exact (MK_COMB (@lem3774717 A s t) (@lem3774691 A t s)). Qed.
Lemma lem3774719 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774724 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774725 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3774724 (A -> Prop) Prop f x). Qed.
Lemma lem3774727 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3774725 A f t). Qed.
Lemma lem3774728 {A : Type'} (f : type686 A) (t : A -> Prop) : (term506 A f t) = (term919 A f t).
Proof. exact (MK_COMB (@lem3774719) (@lem3774727 A f t)). Qed.
Lemma lem3774729 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774730 {A : Type'} (f : type686 A) (t : A -> Prop) : (term561 A f t) = (term920 A f t).
Proof. exact (MK_COMB (@lem3774729) (@lem3774728 A f t)). Qed.
Lemma lem3774731 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term563 A f t s) = (term949 A f t s).
Proof. exact (MK_COMB (@lem3774730 A f t) (@lem3774718 A t s)). Qed.
Lemma lem3774732 {A : Type'} (f : type686 A) (s : A -> Prop) : (term564 A f s) = (term950 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3774731 A f t s)). Qed.
Lemma lem3774733 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3774734 {A : Type'} (f : type686 A) (s : A -> Prop) : (term565 A f s) = (term951 A f s).
Proof. exact (MK_COMB (@lem3774733 A) (@lem3774732 A f s)). Qed.
Lemma lem3774735 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3774740 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3774741 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3774740 (A -> Prop) Prop f x). Qed.
Lemma lem3774743 {A : Type'} (f : type686 A) (s : A -> Prop) : (f s) = (@I ((A -> Prop) -> Prop) f s).
Proof. exact (@lem3774741 A f s). Qed.
Lemma lem3774744 {A : Type'} (f : type686 A) (s : A -> Prop) : (term506 A f s) = (term919 A f s).
Proof. exact (MK_COMB (@lem3774735) (@lem3774743 A f s)). Qed.
Lemma lem3774745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3774746 {A : Type'} (f : type686 A) (s : A -> Prop) : (term561 A f s) = (term920 A f s).
Proof. exact (MK_COMB (@lem3774745) (@lem3774744 A f s)). Qed.
Lemma lem3774747 {A : Type'} (f : type686 A) (s : A -> Prop) : (term567 A f s) = (term959 A f s).
Proof. exact (MK_COMB (@lem3774746 A f s) (@lem3774734 A f s)). Qed.
Lemma lem3774748 {A : Type'} (f : type686 A) : (term568 A f) = (term960 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3774747 A f s)). Qed.
Lemma lem3774749 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3774750 {A : Type'} (f : type686 A) : (term569 A f) = (term961 A f).
Proof. exact (MK_COMB (@lem3774749 A) (@lem3774748 A f)). Qed.
Lemma lem3774751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3774752 {A : Type'} (f : type686 A) : (term587 A f) = (term962 A f).
Proof. exact (MK_COMB (@lem3774751) (@lem3774750 A f)). Qed.
Lemma lem3774753 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) : (term618 A s f x'') = (term963 A s f x'').
Proof. exact (MK_COMB (@lem3774752 A f) (@lem3774667 A s f x'')). Qed.
Lemma lem3774754 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term963 A s f x''.
Proof. exact (EQ_MP (@lem3774753 A s f x'') (@lem3774296 A s f x'' h1)). Qed.
Lemma lem3774755 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term958 A s f x''.
Proof. exact (proj2 (@lem3774754 A s f x'' h1)). Qed.
Lemma lem3774757 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term953 A s f x''.
Proof. exact (proj2 (@lem3774755 A s f x'' h1)). Qed.
Lemma lem3774760 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term951 A f s.
Proof. exact (proj1 (@lem3774757 A s f x'' h1)). Qed.
Lemma lem3774761 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term909 A t x s t' f x') : term937 A s t' f x'.
Proof. exact (proj2 (@lem3774519 A t x s t' f x' h1)). Qed.
Lemma lem3774762 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term909 A t x s t' f x') : term941 A f t s x.
Proof. exact (proj1 (@lem3774519 A t x s t' f x' h1)). Qed.
Lemma lem3774763 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term935 A s f t' x'.
Proof. exact (h1). Qed.
Lemma lem3774764 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term931 A s t' f x'.
Proof. exact (h1). Qed.
Lemma lem3774765 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term927 A f t' x'.
Proof. exact (proj2 (@lem3774763 A s f t' x' h1)). Qed.
Lemma lem3774766 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term933 A s f x'.
Proof. exact (proj1 (@lem3774763 A s f t' x' h1)). Qed.
Lemma lem3774769 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term923 A f x'.
Proof. exact (proj2 (@lem3774766 A s f t' x' h1)). Qed.
Lemma lem3774771 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term939 A f s x.
Proof. exact (h1). Qed.
Lemma lem3774772 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : term938 A f t s x.
Proof. exact (h1). Qed.
Lemma lem3774774 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term933 A s f x.
Proof. exact (proj1 (@lem3774771 A f s x h1)). Qed.
Lemma lem3774778 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : term929 A s f t x.
Proof. exact (proj1 (@lem3774772 A f t s x h1)). Qed.
Lemma lem3774783 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term923 A f x'.
Proof. exact (proj2 (@lem3774764 A s t' f x' h1)). Qed.
Lemma lem3774784 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term929 A s f t' x'.
Proof. exact (proj1 (@lem3774764 A s t' f x' h1)). Qed.
Lemma lem3774786 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term927 A f t' x') : term927 A f t' x'.
Proof. exact (h1). Qed.
Lemma lem3774787 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term939 A f s x.
Proof. exact (h1). Qed.
Lemma lem3774788 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : term938 A f t s x.
Proof. exact (h1). Qed.
Lemma lem3774790 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term933 A s f x.
Proof. exact (proj1 (@lem3774787 A f s x h1)). Qed.
Lemma lem3774794 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : term929 A s f t x.
Proof. exact (proj1 (@lem3774788 A f t s x h1)). Qed.
Lemma lem3774796 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term927 A f t x) : term927 A f t x.
Proof. exact (h1). Qed.
Lemma lem3774801 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term939 A f s x.
Proof. exact (h1). Qed.
Lemma lem3774802 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : term938 A f t s x.
Proof. exact (h1). Qed.
Lemma lem3774804 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term933 A s f x.
Proof. exact (proj1 (@lem3774801 A f s x h1)). Qed.
Lemma lem3774808 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : term929 A s f t x.
Proof. exact (proj1 (@lem3774802 A f t s x h1)). Qed.
Lemma lem3775869 {A : Type'} (s : A -> Prop) (x : A) (h1 : term924 A s x) : term924 A s x.
Proof. exact (h1). Qed.
Lemma lem3776378 {A : Type'} (f : type686 A) (t : A -> Prop) (x' : A) : (term921 A f t x') = (term921 A f t x').
Proof. exact (eq_refl (term921 A f t x')). Qed.
Lemma lem3776379 {A : Type'} (f : type686 A) (x' : A) : (term922 A f x') = (term922 A f x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3776378 A f t x')). Qed.
Lemma lem3776380 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3776382 {A : Type'} (f : type686 A) (x' : A) : (term923 A f x') = (term923 A f x').
Proof. exact (MK_COMB (@lem3776380 A) (@lem3776379 A f x')). Qed.
Lemma lem3776383 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term923 A f x'.
Proof. exact (EQ_MP (@lem3776382 A f x') (@lem3774769 A s f t' x' h1)). Qed.
Lemma lem3777436 {A : Type'} (s : A -> Prop) (x : A) (h1 : term924 A s x) : term924 A s x.
Proof. exact (h1). Qed.
Lemma lem3777789 {A : Type'} (P : A -> Prop) (Q : Prop) : (term964 A P Q) = (term965 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3777790 {A : Type'} (P : A -> Prop) (Q : Prop) : (term964 A P Q) = (term965 A P Q).
Proof. exact (@lem3777789 A P Q). Qed.
Lemma lem3777791 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term966 A t s) = (term967 A t s).
Proof. exact (@lem3777790 A (term945 A s t) (term946 A t s)). Qed.
Lemma lem3777792 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term968 A s t x) = (term944 A s t x).
Proof. exact (eq_refl (term968 A s t x)). Qed.
Lemma lem3777793 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term969 A s t) = (term945 A s t).
Proof. exact (fun_ext (fun x : A => @lem3777792 A s t x)). Qed.
Lemma lem3777794 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3777795 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term970 A s t) = (term946 A s t).
Proof. exact (MK_COMB (@lem3777794 A) (@lem3777793 A s t)). Qed.
Lemma lem3777796 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3777797 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term971 A s t) = (term947 A s t).
Proof. exact (MK_COMB (@lem3777796) (@lem3777795 A s t)). Qed.
Lemma lem3777798 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term946 A t s) = (term946 A t s).
Proof. exact (eq_refl (term946 A t s)). Qed.
Lemma lem3777799 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term966 A t s) = (term948 A t s).
Proof. exact (MK_COMB (@lem3777797 A s t) (@lem3777798 A t s)). Qed.
Lemma lem3777800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3777801 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term972 A t s) = (term973 A t s).
Proof. exact (MK_COMB (@lem3777800) (@lem3777799 A t s)). Qed.
Lemma lem3777802 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term968 A s t x) = (term944 A s t x).
Proof. exact (eq_refl (term968 A s t x)). Qed.
Lemma lem3777803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3777804 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term974 A s t x) = (term975 A s t x).
Proof. exact (MK_COMB (@lem3777803) (@lem3777802 A s t x)). Qed.
Lemma lem3777805 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term946 A t s) = (term946 A t s).
Proof. exact (eq_refl (term946 A t s)). Qed.
Lemma lem3777806 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term976 A x t s) = (term977 A x t s).
Proof. exact (MK_COMB (@lem3777804 A s t x) (@lem3777805 A t s)). Qed.
Lemma lem3777807 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term978 A t s) = (term979 A t s).
Proof. exact (fun_ext (fun x : A => @lem3777806 A x t s)). Qed.
Lemma lem3777808 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3777809 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term967 A t s) = (term980 A t s).
Proof. exact (MK_COMB (@lem3777808 A) (@lem3777807 A t s)). Qed.
Lemma lem3777810 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term966 A t s) = (term967 A t s)) = ((term948 A t s) = (term980 A t s)).
Proof. exact (MK_COMB (@lem3777801 A t s) (@lem3777809 A t s)). Qed.
Lemma lem3777811 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term948 A t s) = (term980 A t s).
Proof. exact (EQ_MP (@lem3777810 A t s) (@lem3777791 A t s)). Qed.
Lemma lem3777813 {A : Type'} (P : Prop) (Q : A -> Prop) : (term981 A P Q) = (term982 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3777814 {A : Type'} (P : Prop) (Q : A -> Prop) : (term981 A P Q) = (term982 A P Q).
Proof. exact (@lem3777813 A P Q). Qed.
Lemma lem3777815 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term983 A x t s) = (term984 A x t s).
Proof. exact (@lem3777814 A (term944 A s t x) (term945 A t s)). Qed.
Lemma lem3777816 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term968 A t s x) = (term944 A t s x).
Proof. exact (eq_refl (term968 A t s x)). Qed.
Lemma lem3777817 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term969 A t s) = (term945 A t s).
Proof. exact (fun_ext (fun x : A => @lem3777816 A t s x)). Qed.
Lemma lem3777818 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3777819 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term970 A t s) = (term946 A t s).
Proof. exact (MK_COMB (@lem3777818 A) (@lem3777817 A t s)). Qed.
Lemma lem3777820 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term975 A s t x) = (term975 A s t x).
Proof. exact (eq_refl (term975 A s t x)). Qed.
Lemma lem3777821 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term983 A x t s) = (term977 A x t s).
Proof. exact (MK_COMB (@lem3777820 A s t x) (@lem3777819 A t s)). Qed.
Lemma lem3777822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3777823 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term985 A x t s) = (term986 A x t s).
Proof. exact (MK_COMB (@lem3777822) (@lem3777821 A x t s)). Qed.
Lemma lem3777824 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) : (term968 A t s x') = (term944 A t s x').
Proof. exact (eq_refl (term968 A t s x')). Qed.
Lemma lem3777825 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term975 A s t x) = (term975 A s t x).
Proof. exact (eq_refl (term975 A s t x)). Qed.
Lemma lem3777826 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term987 A x t s x') = (term988 A x t s x').
Proof. exact (MK_COMB (@lem3777825 A s t x) (@lem3777824 A t s x')). Qed.
Lemma lem3777827 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term989 A x t s) = (term990 A x t s).
Proof. exact (fun_ext (fun x' : A => @lem3777826 A x t s x')). Qed.
Lemma lem3777828 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3777829 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term984 A x t s) = (term991 A x t s).
Proof. exact (MK_COMB (@lem3777828 A) (@lem3777827 A x t s)). Qed.
Lemma lem3777830 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : ((term983 A x t s) = (term984 A x t s)) = ((term977 A x t s) = (term991 A x t s)).
Proof. exact (MK_COMB (@lem3777823 A x t s) (@lem3777829 A x t s)). Qed.
Lemma lem3777831 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term977 A x t s) = (term991 A x t s).
Proof. exact (EQ_MP (@lem3777830 A x t s) (@lem3777815 A x t s)). Qed.
Lemma lem3777832 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term979 A t s) = (term992 A t s).
Proof. exact (fun_ext (fun x : A => @lem3777831 A x t s)). Qed.
Lemma lem3777833 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3777834 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term980 A t s) = (term993 A t s).
Proof. exact (MK_COMB (@lem3777833 A) (@lem3777832 A t s)). Qed.
Lemma lem3777835 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term948 A t s) = (term993 A t s).
Proof. exact (TRANS (@lem3777811 A t s) (@lem3777834 A t s)). Qed.
Lemma lem3777836 {A : Type'} (f : type686 A) (t : A -> Prop) : (term920 A f t) = (term920 A f t).
Proof. exact (eq_refl (term920 A f t)). Qed.
Lemma lem3777837 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term949 A f t s) = (term994 A f t s).
Proof. exact (MK_COMB (@lem3777836 A f t) (@lem3777835 A t s)). Qed.
Lemma lem3777839 {A : Type'} (P : Prop) (Q : A -> Prop) : (term981 A P Q) = (term982 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3777840 {A : Type'} (P : Prop) (Q : A -> Prop) : (term981 A P Q) = (term982 A P Q).
Proof. exact (@lem3777839 A P Q). Qed.
Lemma lem3777841 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term995 A f t s) = (term996 A f t s).
Proof. exact (@lem3777840 A (term919 A f t) (term992 A t s)). Qed.
Lemma lem3777842 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term997 A t s x) = (term991 A x t s).
Proof. exact (eq_refl (term997 A t s x)). Qed.
Lemma lem3777843 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term998 A t s) = (term992 A t s).
Proof. exact (fun_ext (fun x : A => @lem3777842 A x t s)). Qed.
Lemma lem3777844 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3777845 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term999 A t s) = (term993 A t s).
Proof. exact (MK_COMB (@lem3777844 A) (@lem3777843 A t s)). Qed.
Lemma lem3777846 {A : Type'} (f : type686 A) (t : A -> Prop) : (term920 A f t) = (term920 A f t).
Proof. exact (eq_refl (term920 A f t)). Qed.
Lemma lem3777847 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term995 A f t s) = (term994 A f t s).
Proof. exact (MK_COMB (@lem3777846 A f t) (@lem3777845 A t s)). Qed.
Lemma lem3777848 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3777849 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1000 A f t s) = (term1001 A f t s).
Proof. exact (MK_COMB (@lem3777848) (@lem3777847 A f t s)). Qed.
Lemma lem3777850 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term997 A t s x) = (term991 A x t s).
Proof. exact (eq_refl (term997 A t s x)). Qed.
Lemma lem3777851 {A : Type'} (f : type686 A) (t : A -> Prop) : (term920 A f t) = (term920 A f t).
Proof. exact (eq_refl (term920 A f t)). Qed.
Lemma lem3777852 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1002 A f t s x) = (term1003 A f x t s).
Proof. exact (MK_COMB (@lem3777851 A f t) (@lem3777850 A x t s)). Qed.
Lemma lem3777853 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1004 A f t s) = (term1005 A f t s).
Proof. exact (fun_ext (fun x : A => @lem3777852 A f x t s)). Qed.
Lemma lem3777854 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3777855 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term996 A f t s) = (term1006 A f t s).
Proof. exact (MK_COMB (@lem3777854 A) (@lem3777853 A f t s)). Qed.
Lemma lem3777856 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : ((term995 A f t s) = (term996 A f t s)) = ((term994 A f t s) = (term1006 A f t s)).
Proof. exact (MK_COMB (@lem3777849 A f t s) (@lem3777855 A f t s)). Qed.
Lemma lem3777857 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term994 A f t s) = (term1006 A f t s).
Proof. exact (EQ_MP (@lem3777856 A f t s) (@lem3777841 A f t s)). Qed.
Lemma lem3777859 {A : Type'} (P : Prop) (Q : A -> Prop) : (term981 A P Q) = (term982 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3777860 {A : Type'} (P : Prop) (Q : A -> Prop) : (term981 A P Q) = (term982 A P Q).
Proof. exact (@lem3777859 A P Q). Qed.
Lemma lem3777861 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1007 A f x t s) = (term1008 A f x t s).
Proof. exact (@lem3777860 A (term919 A f t) (term990 A x t s)). Qed.
Lemma lem3777862 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term1009 A x t s x') = (term988 A x t s x').
Proof. exact (eq_refl (term1009 A x t s x')). Qed.
Lemma lem3777863 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term1010 A x t s) = (term990 A x t s).
Proof. exact (fun_ext (fun x' : A => @lem3777862 A x t s x')). Qed.
Lemma lem3777864 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3777865 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term1011 A x t s) = (term991 A x t s).
Proof. exact (MK_COMB (@lem3777864 A) (@lem3777863 A x t s)). Qed.
Lemma lem3777866 {A : Type'} (f : type686 A) (t : A -> Prop) : (term920 A f t) = (term920 A f t).
Proof. exact (eq_refl (term920 A f t)). Qed.
Lemma lem3777867 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1007 A f x t s) = (term1003 A f x t s).
Proof. exact (MK_COMB (@lem3777866 A f t) (@lem3777865 A x t s)). Qed.
Lemma lem3777868 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3777869 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1012 A f x t s) = (term1013 A f x t s).
Proof. exact (MK_COMB (@lem3777868) (@lem3777867 A f x t s)). Qed.
Lemma lem3777870 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term1009 A x t s x') = (term988 A x t s x').
Proof. exact (eq_refl (term1009 A x t s x')). Qed.
Lemma lem3777871 {A : Type'} (f : type686 A) (t : A -> Prop) : (term920 A f t) = (term920 A f t).
Proof. exact (eq_refl (term920 A f t)). Qed.
Lemma lem3777872 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term1014 A f x t s x') = (term1015 A f x t s x').
Proof. exact (MK_COMB (@lem3777871 A f t) (@lem3777870 A x t s x')). Qed.
Lemma lem3777873 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1016 A f x t s) = (term1017 A f x t s).
Proof. exact (fun_ext (fun x' : A => @lem3777872 A f x t s x')). Qed.
Lemma lem3777874 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3777875 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1008 A f x t s) = (term1018 A f x t s).
Proof. exact (MK_COMB (@lem3777874 A) (@lem3777873 A f x t s)). Qed.
Lemma lem3777876 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : ((term1007 A f x t s) = (term1008 A f x t s)) = ((term1003 A f x t s) = (term1018 A f x t s)).
Proof. exact (MK_COMB (@lem3777869 A f x t s) (@lem3777875 A f x t s)). Qed.
Lemma lem3777877 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1003 A f x t s) = (term1018 A f x t s).
Proof. exact (EQ_MP (@lem3777876 A f x t s) (@lem3777861 A f x t s)). Qed.
Lemma lem3777878 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1005 A f t s) = (term1019 A f t s).
Proof. exact (fun_ext (fun x : A => @lem3777877 A f x t s)). Qed.
Lemma lem3777879 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3777880 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1006 A f t s) = (term1020 A f t s).
Proof. exact (MK_COMB (@lem3777879 A) (@lem3777878 A f t s)). Qed.
Lemma lem3777881 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term994 A f t s) = (term1020 A f t s).
Proof. exact (TRANS (@lem3777857 A f t s) (@lem3777880 A f t s)). Qed.
Lemma lem3777882 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term949 A f t s) = (term1020 A f t s).
Proof. exact (TRANS (@lem3777837 A f t s) (@lem3777881 A f t s)). Qed.
Lemma lem3777883 {A : Type'} (f : type686 A) (s : A -> Prop) : (term950 A f s) = (term1021 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3777882 A f t s)). Qed.
Lemma lem3777884 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3777885 {A : Type'} (f : type686 A) (s : A -> Prop) : (term951 A f s) = (term1022 A f s).
Proof. exact (MK_COMB (@lem3777884 A) (@lem3777883 A f s)). Qed.
Lemma lem3777910 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term1015 A f x t s x') = (term1015 A f x t s x').
Proof. exact (eq_refl (term1015 A f x t s x')). Qed.
Lemma lem3777911 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1017 A f x t s) = (term1017 A f x t s).
Proof. exact (fun_ext (fun x' : A => @lem3777910 A f x t s x')). Qed.
Lemma lem3777912 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3777913 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1018 A f x t s) = (term1018 A f x t s).
Proof. exact (MK_COMB (@lem3777912 A) (@lem3777911 A f x t s)). Qed.
Lemma lem3777914 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1019 A f t s) = (term1019 A f t s).
Proof. exact (fun_ext (fun x : A => @lem3777913 A f x t s)). Qed.
Lemma lem3777915 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3777916 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1020 A f t s) = (term1020 A f t s).
Proof. exact (MK_COMB (@lem3777915 A) (@lem3777914 A f t s)). Qed.
Lemma lem3777917 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1021 A f s) = (term1021 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3777916 A f t s)). Qed.
Lemma lem3777918 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3777919 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1022 A f s) = (term1022 A f s).
Proof. exact (MK_COMB (@lem3777918 A) (@lem3777917 A f s)). Qed.
Lemma lem3777920 {A : Type'} (f : type686 A) (s : A -> Prop) : (term951 A f s) = (term1022 A f s).
Proof. exact (TRANS (@lem3777885 A f s) (@lem3777919 A f s)). Qed.
Lemma lem3777921 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term1022 A f s.
Proof. exact (EQ_MP (@lem3777920 A f s) (@lem3774760 A s f x'' h1)). Qed.
Lemma lem3777933 {A : Type'} (f : type686 A) (t : A -> Prop) (x' : A) : (term921 A f t x') = (term921 A f t x').
Proof. exact (eq_refl (term921 A f t x')). Qed.
Lemma lem3777934 {A : Type'} (f : type686 A) (x' : A) : (term922 A f x') = (term922 A f x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3777933 A f t x')). Qed.
Lemma lem3777935 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3777937 {A : Type'} (f : type686 A) (x' : A) : (term923 A f x') = (term923 A f x').
Proof. exact (MK_COMB (@lem3777935 A) (@lem3777934 A f x')). Qed.
Lemma lem3777938 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term923 A f x'.
Proof. exact (EQ_MP (@lem3777937 A f x') (@lem3774783 A s t' f x' h1)). Qed.
Lemma lem3777942 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term924 A s x') : term924 A s x'.
Proof. exact (h1). Qed.
Lemma lem3779003 {A : Type'} (s : A -> Prop) (x : A) (h1 : term924 A s x) : term924 A s x.
Proof. exact (h1). Qed.
Lemma lem3779500 {A : Type'} (f : type686 A) (t : A -> Prop) (x' : A) : (term921 A f t x') = (term921 A f t x').
Proof. exact (eq_refl (term921 A f t x')). Qed.
Lemma lem3779501 {A : Type'} (f : type686 A) (x' : A) : (term922 A f x') = (term922 A f x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3779500 A f t x')). Qed.
Lemma lem3779502 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3779504 {A : Type'} (f : type686 A) (x' : A) : (term923 A f x') = (term923 A f x').
Proof. exact (MK_COMB (@lem3779502 A) (@lem3779501 A f x')). Qed.
Lemma lem3779505 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term923 A f x'.
Proof. exact (EQ_MP (@lem3779504 A f x') (@lem3774783 A s t' f x' h1)). Qed.
Lemma lem3779625 {A : Type'} (_43378 : A -> Prop) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term1023 A f x' _43378.
Proof. exact (@lem3776383 A s f t' x' h1 _43378). Qed.
Lemma lem3779626 {A : Type'} (f : type686 A) (_43378 : A -> Prop) (x' : A) : (term1023 A f x' _43378) = (term921 A f _43378 x').
Proof. exact (eq_refl (term1023 A f x' _43378)). Qed.
Lemma lem3779718 {A : Type'} (_43409 : A -> Prop) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term1024 A f s _43409.
Proof. exact (@lem3777921 A s f x'' h1 _43409). Qed.
Lemma lem3779719 {A : Type'} (f : type686 A) (_43409 : A -> Prop) (s : A -> Prop) : (term1024 A f s _43409) = (term1020 A f _43409 s).
Proof. exact (eq_refl (term1024 A f s _43409)). Qed.
Lemma lem3779720 {A : Type'} (_43409 : A -> Prop) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term1020 A f _43409 s.
Proof. exact (EQ_MP (@lem3779719 A f _43409 s) (@lem3779718 A _43409 s f x'' h1)). Qed.
Lemma lem3779721 {A : Type'} (_43409 : A -> Prop) (_43410 : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term1025 A f _43409 s _43410.
Proof. exact (@lem3779720 A _43409 s f x'' h1 _43410). Qed.
Lemma lem3779722 {A : Type'} (f : type686 A) (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) : (term1025 A f _43409 s _43410) = (term1018 A f _43410 _43409 s).
Proof. exact (eq_refl (term1025 A f _43409 s _43410)). Qed.
Lemma lem3779723 {A : Type'} (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term1018 A f _43410 _43409 s.
Proof. exact (EQ_MP (@lem3779722 A f _43410 _43409 s) (@lem3779721 A _43409 _43410 s f x'' h1)). Qed.
Lemma lem3779724 {A : Type'} (_43410 : A) (_43409 : A -> Prop) (_43411 : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term1026 A f _43410 _43409 s _43411.
Proof. exact (@lem3779723 A _43410 _43409 s f x'' h1 _43411). Qed.
Lemma lem3779725 {A : Type'} (f : type686 A) (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1026 A f _43410 _43409 s _43411) = (term1015 A f _43410 _43409 s _43411).
Proof. exact (eq_refl (term1026 A f _43410 _43409 s _43411)). Qed.
Lemma lem3779726 {A : Type'} (_43410 : A) (_43409 : A -> Prop) (_43411 : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term1015 A f _43410 _43409 s _43411.
Proof. exact (EQ_MP (@lem3779725 A f _43410 _43409 s _43411) (@lem3779724 A _43410 _43409 _43411 s f x'' h1)). Qed.
Lemma lem3779727 {A : Type'} (_43412 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term1023 A f x' _43412.
Proof. exact (@lem3777938 A s t' f x' h1 _43412). Qed.
Lemma lem3779728 {A : Type'} (f : type686 A) (_43412 : A -> Prop) (x' : A) : (term1023 A f x' _43412) = (term921 A f _43412 x').
Proof. exact (eq_refl (term1023 A f x' _43412)). Qed.
Lemma lem3779829 {A : Type'} (_43446 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term1023 A f x' _43446.
Proof. exact (@lem3779505 A s t' f x' h1 _43446). Qed.
Lemma lem3779830 {A : Type'} (f : type686 A) (_43446 : A -> Prop) (x' : A) : (term1023 A f x' _43446) = (term921 A f _43446 x').
Proof. exact (eq_refl (term1023 A f x' _43446)). Qed.
Lemma lem3779911 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term924 A s x.
Proof. exact (proj2 (@lem3774771 A f s x h1)). Qed.
Lemma lem3780001 {A : Type'} (s : A -> Prop) (x : A) (h1 : term924 A s x) : term924 A s x.
Proof. exact (h1). Qed.
Lemma lem3780071 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term924 A t' x'.
Proof. exact (proj2 (@lem3774765 A s f t' x' h1)). Qed.
Lemma lem3780079 {A : Type'} (_43378 : A -> Prop) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term921 A f _43378 x'.
Proof. exact (EQ_MP (@lem3779626 A f _43378 x') (@lem3779625 A _43378 s f t' x' h1)). Qed.
Lemma lem3780161 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term924 A s x.
Proof. exact (proj2 (@lem3774787 A f s x h1)). Qed.
Lemma lem3780247 {A : Type'} (s : A -> Prop) (x : A) (h1 : term924 A s x) : term924 A s x.
Proof. exact (h1). Qed.
Lemma lem3780306 {A : Type'} (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term988 A _43410 _43409 s _43411) = (term1027 A _43410 _43409 s _43411).
Proof. exact (@lem3771511 (term924 A s _43410) (@I (A -> Prop) _43409 _43410) (term944 A _43409 s _43411)). Qed.
Lemma lem3780307 {A : Type'} (f : type686 A) (_43409 : A -> Prop) : (term920 A f _43409) = (term920 A f _43409).
Proof. exact (eq_refl (term920 A f _43409)). Qed.
Lemma lem3780310 {A : Type'} (f : type686 A) (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1015 A f _43410 _43409 s _43411) = (term1028 A f _43410 _43409 s _43411).
Proof. exact (MK_COMB (@lem3780307 A f _43409) (@lem3780306 A _43410 _43409 s _43411)). Qed.
Lemma lem3780311 {A : Type'} (_43410 : A) (_43409 : A -> Prop) (_43411 : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term1028 A f _43410 _43409 s _43411.
Proof. exact (EQ_MP (@lem3780310 A f _43410 _43409 s _43411) (@lem3779726 A _43410 _43409 _43411 s f x'' h1)). Qed.
Lemma lem3780319 {A : Type'} (_43412 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term921 A f _43412 x'.
Proof. exact (EQ_MP (@lem3779728 A f _43412 x') (@lem3779727 A _43412 s t' f x' h1)). Qed.
Lemma lem3780321 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term924 A s x') : term924 A s x'.
Proof. exact (h1). Qed.
Lemma lem3780327 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term927 A f t x) : term924 A t x.
Proof. exact (proj2 (@lem3774796 A f t x h1)). Qed.
Lemma lem3780405 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term924 A s x.
Proof. exact (proj2 (@lem3774801 A f s x h1)). Qed.
Lemma lem3780493 {A : Type'} (s : A -> Prop) (x : A) (h1 : term924 A s x) : term924 A s x.
Proof. exact (h1). Qed.
Lemma lem3780565 {A : Type'} (_43446 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term921 A f _43446 x'.
Proof. exact (EQ_MP (@lem3779830 A f _43446 x') (@lem3779829 A _43446 s t' f x' h1)). Qed.
Lemma lem3780569 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term927 A f t' x') : term924 A t' x'.
Proof. exact (proj2 (@lem3774786 A f t' x' h1)). Qed.
Lemma lem3780577 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem3774774 A f s x h1)). Qed.
Lemma lem3780578 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term1029 A s x.
Proof. exact (fun h0 : term924 A s x => @lem3780577 A f s x h1). Qed.
Lemma lem3780580 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3780581 {A : Type'} (s : A -> Prop) (x : A) : (term1029 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3780580 (@I (A -> Prop) s x)). Qed.
Lemma lem3780582 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3780581 A s x) (@lem3780578 A f s x h1)). Qed.
Lemma lem3780585 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3780587 {A : Type'} (s : A -> Prop) (x : A) : (term924 A s x) = (term1030 A s x).
Proof. exact (@lem3780585 (@I (A -> Prop) s x)). Qed.
Lemma lem3780590 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term1030 A s x.
Proof. exact (EQ_MP (@lem3780587 A s x) (@lem3779911 A f s x h1)). Qed.
Lemma lem3780593 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : False.
Proof. exact (@lem3780590 A f s x h1 (@lem3780582 A f s x h1)). Qed.
Lemma lem3780594 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term32.
Proof. exact (fun h0 : ~ False => @lem3780593 A f s x h1). Qed.
Lemma lem3780596 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3780597 : term32 = False.
Proof. exact (@lem3780596 False). Qed.
Lemma lem3780598 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : False.
Proof. exact (EQ_MP (@lem3780597) (@lem3780594 A f s x h1)). Qed.
Lemma lem3780600 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem3774772 A f t s x h1)). Qed.
Lemma lem3780601 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : term1029 A s x.
Proof. exact (fun h0 : term924 A s x => @lem3780600 A f t s x h1). Qed.
Lemma lem3780603 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3780604 {A : Type'} (s : A -> Prop) (x : A) : (term1029 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3780603 (@I (A -> Prop) s x)). Qed.
Lemma lem3780605 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3780604 A s x) (@lem3780601 A f t s x h1)). Qed.
Lemma lem3780608 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3780610 {A : Type'} (s : A -> Prop) (x : A) : (term924 A s x) = (term1030 A s x).
Proof. exact (@lem3780608 (@I (A -> Prop) s x)). Qed.
Lemma lem3780613 {A : Type'} (s : A -> Prop) (x : A) (h1 : term924 A s x) : term1030 A s x.
Proof. exact (EQ_MP (@lem3780610 A s x) (@lem3780001 A s x h1)). Qed.
Lemma lem3780616 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : False.
Proof. exact (@lem3780613 A s x h1 (@lem3780605 A f t s x h2)). Qed.
Lemma lem3780617 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : term32.
Proof. exact (fun h0 : ~ False => @lem3780616 A f t s x h1 h2). Qed.
Lemma lem3780619 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3780620 : term32 = False.
Proof. exact (@lem3780619 False). Qed.
Lemma lem3780621 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : False.
Proof. exact (EQ_MP (@lem3780620) (@lem3780617 A f t s x h1 h2)). Qed.
Lemma lem3780623 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : @I ((A -> Prop) -> Prop) f t'.
Proof. exact (proj1 (@lem3774765 A s f t' x' h1)). Qed.
Lemma lem3780624 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term1031 A f t'.
Proof. exact (fun h0 : term919 A f t' => @lem3780623 A s f t' x' h1). Qed.
Lemma lem3780626 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3780627 {A : Type'} (f : type686 A) (t' : A -> Prop) : (term1031 A f t') = (@I ((A -> Prop) -> Prop) f t').
Proof. exact (@lem3780626 (@I ((A -> Prop) -> Prop) f t')). Qed.
Lemma lem3780628 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : @I ((A -> Prop) -> Prop) f t'.
Proof. exact (EQ_MP (@lem3780627 A f t') (@lem3780624 A s f t' x' h1)). Qed.
Lemma lem3780634 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3780635 {A : Type'} (x' : A) (f : type686 A) (_43378 : A -> Prop) : (term921 A f _43378 x') = (term1032 A x' f _43378).
Proof. exact (@lem3780634 (@I (A -> Prop) _43378 x') (term919 A f _43378)). Qed.
Lemma lem3780641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3780642 {A : Type'} (x' : A) (f : type686 A) (_43378 : A -> Prop) : (term1033 A f _43378 x') = (term1034 A x' f _43378).
Proof. exact (MK_COMB (@lem3780641) (@lem3780635 A x' f _43378)). Qed.
Lemma lem3780648 {A : Type'} (x' : A) (f : type686 A) (_43378 : A -> Prop) : (term1032 A x' f _43378) = (term1032 A x' f _43378).
Proof. exact (eq_refl (term1032 A x' f _43378)). Qed.
Lemma lem3780649 {A : Type'} (x' : A) (f : type686 A) (_43378 : A -> Prop) : ((term921 A f _43378 x') = (term1032 A x' f _43378)) = ((term1032 A x' f _43378) = (term1032 A x' f _43378)).
Proof. exact (MK_COMB (@lem3780642 A x' f _43378) (@lem3780648 A x' f _43378)). Qed.
Lemma lem3780651 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3780652 (x : Prop) : (x = x) = True.
Proof. exact (@lem3780651 Prop x). Qed.
Lemma lem3780653 {A : Type'} (x' : A) (f : type686 A) (_43378 : A -> Prop) : ((term1032 A x' f _43378) = (term1032 A x' f _43378)) = True.
Proof. exact (@lem3780652 (term1032 A x' f _43378)). Qed.
Lemma lem3780654 {A : Type'} (x' : A) (f : type686 A) (_43378 : A -> Prop) : ((term921 A f _43378 x') = (term1032 A x' f _43378)) = True.
Proof. exact (TRANS (@lem3780649 A x' f _43378) (@lem3780653 A x' f _43378)). Qed.
Lemma lem3780655 {A : Type'} (x' : A) (f : type686 A) (_43378 : A -> Prop) : True = ((term921 A f _43378 x') = (term1032 A x' f _43378)).
Proof. exact (SYM (@lem3780654 A x' f _43378)). Qed.
Lemma lem3780656 {A : Type'} (x' : A) (f : type686 A) (_43378 : A -> Prop) : (term921 A f _43378 x') = (term1032 A x' f _43378).
Proof. exact (EQ_MP (@lem3780655 A x' f _43378) (@lem0)). Qed.
Lemma lem3780657 {A : Type'} (_43378 : A -> Prop) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term1032 A x' f _43378.
Proof. exact (EQ_MP (@lem3780656 A x' f _43378) (@lem3780079 A _43378 s f t' x' h1)). Qed.
Lemma lem3780659 (b : Prop) (a : Prop) : (a \/ b) = (term55 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3780660 {A : Type'} (f : type686 A) (_43378 : A -> Prop) (x' : A) : (term1032 A x' f _43378) = (term1035 A f _43378 x').
Proof. exact (@lem3780659 (term919 A f _43378) (@I (A -> Prop) _43378 x')). Qed.
Lemma lem3780662 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3780663 {A : Type'} (f : type686 A) (_43378 : A -> Prop) : (term1036 A f _43378) = (@I ((A -> Prop) -> Prop) f _43378).
Proof. exact (@lem3780662 (@I ((A -> Prop) -> Prop) f _43378)). Qed.
Lemma lem3780664 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3780665 {A : Type'} (f : type686 A) (_43378 : A -> Prop) : (term1037 A f _43378) = (term1038 A f _43378).
Proof. exact (MK_COMB (@lem3780664) (@lem3780663 A f _43378)). Qed.
Lemma lem3780666 {A : Type'} (_43378 : A -> Prop) (x' : A) : (@I (A -> Prop) _43378 x') = (@I (A -> Prop) _43378 x').
Proof. exact (eq_refl (@I (A -> Prop) _43378 x')). Qed.
Lemma lem3780667 {A : Type'} (f : type686 A) (_43378 : A -> Prop) (x' : A) : (term1035 A f _43378 x') = (term1039 A f _43378 x').
Proof. exact (MK_COMB (@lem3780665 A f _43378) (@lem3780666 A _43378 x')). Qed.
Lemma lem3780668 {A : Type'} (f : type686 A) (_43378 : A -> Prop) (x' : A) : (term1032 A x' f _43378) = (term1039 A f _43378 x').
Proof. exact (TRANS (@lem3780660 A f _43378 x') (@lem3780667 A f _43378 x')). Qed.
Lemma lem3780671 {A : Type'} (_43378 : A -> Prop) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term1039 A f _43378 x'.
Proof. exact (EQ_MP (@lem3780668 A f _43378 x') (@lem3780657 A _43378 s f t' x' h1)). Qed.
Lemma lem3780672 {A : Type'} (_43378 : A -> Prop) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term1039 A f _43378 x'.
Proof. exact (@lem3780671 A _43378 s f t' x' h1). Qed.
Lemma lem3780673 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term1039 A f t' x'.
Proof. exact (@lem3780672 A t' s f t' x' h1). Qed.
Lemma lem3780676 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : @I (A -> Prop) t' x'.
Proof. exact (@lem3780673 A s f t' x' h1 (@lem3780628 A s f t' x' h1)). Qed.
Lemma lem3780677 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term1029 A t' x'.
Proof. exact (fun h0 : term924 A t' x' => @lem3780676 A s f t' x' h1). Qed.
Lemma lem3780679 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3780680 {A : Type'} (t' : A -> Prop) (x' : A) : (term1029 A t' x') = (@I (A -> Prop) t' x').
Proof. exact (@lem3780679 (@I (A -> Prop) t' x')). Qed.
Lemma lem3780681 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : @I (A -> Prop) t' x'.
Proof. exact (EQ_MP (@lem3780680 A t' x') (@lem3780677 A s f t' x' h1)). Qed.
Lemma lem3780684 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3780686 {A : Type'} (t' : A -> Prop) (x' : A) : (term924 A t' x') = (term1030 A t' x').
Proof. exact (@lem3780684 (@I (A -> Prop) t' x')). Qed.
Lemma lem3780689 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term1030 A t' x'.
Proof. exact (EQ_MP (@lem3780686 A t' x') (@lem3780071 A s f t' x' h1)). Qed.
Lemma lem3780692 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : False.
Proof. exact (@lem3780689 A s f t' x' h1 (@lem3780681 A s f t' x' h1)). Qed.
Lemma lem3780693 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term32.
Proof. exact (fun h0 : ~ False => @lem3780692 A s f t' x' h1). Qed.
Lemma lem3780695 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3780696 : term32 = False.
Proof. exact (@lem3780695 False). Qed.
Lemma lem3780697 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : False.
Proof. exact (EQ_MP (@lem3780696) (@lem3780693 A s f t' x' h1)). Qed.
Lemma lem3780699 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem3774790 A f s x h1)). Qed.
Lemma lem3780700 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term1029 A s x.
Proof. exact (fun h0 : term924 A s x => @lem3780699 A f s x h1). Qed.
Lemma lem3780702 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3780703 {A : Type'} (s : A -> Prop) (x : A) : (term1029 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3780702 (@I (A -> Prop) s x)). Qed.
Lemma lem3780704 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3780703 A s x) (@lem3780700 A f s x h1)). Qed.
Lemma lem3780707 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3780709 {A : Type'} (s : A -> Prop) (x : A) : (term924 A s x) = (term1030 A s x).
Proof. exact (@lem3780707 (@I (A -> Prop) s x)). Qed.
Lemma lem3780712 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term1030 A s x.
Proof. exact (EQ_MP (@lem3780709 A s x) (@lem3780161 A f s x h1)). Qed.
Lemma lem3780715 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : False.
Proof. exact (@lem3780712 A f s x h1 (@lem3780704 A f s x h1)). Qed.
Lemma lem3780716 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term32.
Proof. exact (fun h0 : ~ False => @lem3780715 A f s x h1). Qed.
Lemma lem3780718 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3780719 : term32 = False.
Proof. exact (@lem3780718 False). Qed.
Lemma lem3780720 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : False.
Proof. exact (EQ_MP (@lem3780719) (@lem3780716 A f s x h1)). Qed.
Lemma lem3780722 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem3774788 A f t s x h1)). Qed.
Lemma lem3780723 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : term1029 A s x.
Proof. exact (fun h0 : term924 A s x => @lem3780722 A f t s x h1). Qed.
Lemma lem3780725 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3780726 {A : Type'} (s : A -> Prop) (x : A) : (term1029 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3780725 (@I (A -> Prop) s x)). Qed.
Lemma lem3780727 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3780726 A s x) (@lem3780723 A f t s x h1)). Qed.
Lemma lem3780730 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3780732 {A : Type'} (s : A -> Prop) (x : A) : (term924 A s x) = (term1030 A s x).
Proof. exact (@lem3780730 (@I (A -> Prop) s x)). Qed.
Lemma lem3780735 {A : Type'} (s : A -> Prop) (x : A) (h1 : term924 A s x) : term1030 A s x.
Proof. exact (EQ_MP (@lem3780732 A s x) (@lem3780247 A s x h1)). Qed.
Lemma lem3780738 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : False.
Proof. exact (@lem3780735 A s x h1 (@lem3780727 A f t s x h2)). Qed.
Lemma lem3780739 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : term32.
Proof. exact (fun h0 : ~ False => @lem3780738 A f t s x h1 h2). Qed.
Lemma lem3780741 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3780742 : term32 = False.
Proof. exact (@lem3780741 False). Qed.
Lemma lem3780743 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : False.
Proof. exact (EQ_MP (@lem3780742) (@lem3780739 A f t s x h1 h2)). Qed.
Lemma lem3780745 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term927 A f t x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem3774796 A f t x h1)). Qed.
Lemma lem3780746 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term927 A f t x) : term1031 A f t.
Proof. exact (fun h0 : term919 A f t => @lem3780745 A f t x h1). Qed.
Lemma lem3780748 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3780749 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1031 A f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3780748 (@I ((A -> Prop) -> Prop) f t)). Qed.
Lemma lem3780750 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term927 A f t x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem3780749 A f t) (@lem3780746 A f t x h1)). Qed.
Lemma lem3780752 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem3774788 A f t s x h1)). Qed.
Lemma lem3780753 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : term1029 A s x.
Proof. exact (fun h0 : term924 A s x => @lem3780752 A f t s x h1). Qed.
Lemma lem3780755 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3780756 {A : Type'} (s : A -> Prop) (x : A) : (term1029 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3780755 (@I (A -> Prop) s x)). Qed.
Lemma lem3780757 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3780756 A s x) (@lem3780753 A f t s x h1)). Qed.
Lemma lem3780759 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term927 A f t x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem3774796 A f t x h1)). Qed.
Lemma lem3780760 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term927 A f t x) : term1031 A f t.
Proof. exact (fun h0 : term919 A f t => @lem3780759 A f t x h1). Qed.
Lemma lem3780762 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3780763 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1031 A f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3780762 (@I ((A -> Prop) -> Prop) f t)). Qed.
Lemma lem3780764 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term927 A f t x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem3780763 A f t) (@lem3780760 A f t x h1)). Qed.
Lemma lem3780770 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3780771 {A : Type'} (x' : A) (f : type686 A) (_43412 : A -> Prop) : (term921 A f _43412 x') = (term1032 A x' f _43412).
Proof. exact (@lem3780770 (@I (A -> Prop) _43412 x') (term919 A f _43412)). Qed.
Lemma lem3780777 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3780778 {A : Type'} (x' : A) (f : type686 A) (_43412 : A -> Prop) : (term1033 A f _43412 x') = (term1034 A x' f _43412).
Proof. exact (MK_COMB (@lem3780777) (@lem3780771 A x' f _43412)). Qed.
Lemma lem3780784 {A : Type'} (x' : A) (f : type686 A) (_43412 : A -> Prop) : (term1032 A x' f _43412) = (term1032 A x' f _43412).
Proof. exact (eq_refl (term1032 A x' f _43412)). Qed.
Lemma lem3780785 {A : Type'} (x' : A) (f : type686 A) (_43412 : A -> Prop) : ((term921 A f _43412 x') = (term1032 A x' f _43412)) = ((term1032 A x' f _43412) = (term1032 A x' f _43412)).
Proof. exact (MK_COMB (@lem3780778 A x' f _43412) (@lem3780784 A x' f _43412)). Qed.
Lemma lem3780787 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3780788 (x : Prop) : (x = x) = True.
Proof. exact (@lem3780787 Prop x). Qed.
Lemma lem3780789 {A : Type'} (x' : A) (f : type686 A) (_43412 : A -> Prop) : ((term1032 A x' f _43412) = (term1032 A x' f _43412)) = True.
Proof. exact (@lem3780788 (term1032 A x' f _43412)). Qed.
Lemma lem3780790 {A : Type'} (x' : A) (f : type686 A) (_43412 : A -> Prop) : ((term921 A f _43412 x') = (term1032 A x' f _43412)) = True.
Proof. exact (TRANS (@lem3780785 A x' f _43412) (@lem3780789 A x' f _43412)). Qed.
Lemma lem3780791 {A : Type'} (x' : A) (f : type686 A) (_43412 : A -> Prop) : True = ((term921 A f _43412 x') = (term1032 A x' f _43412)).
Proof. exact (SYM (@lem3780790 A x' f _43412)). Qed.
Lemma lem3780792 {A : Type'} (x' : A) (f : type686 A) (_43412 : A -> Prop) : (term921 A f _43412 x') = (term1032 A x' f _43412).
Proof. exact (EQ_MP (@lem3780791 A x' f _43412) (@lem0)). Qed.
Lemma lem3780793 {A : Type'} (_43412 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term1032 A x' f _43412.
Proof. exact (EQ_MP (@lem3780792 A x' f _43412) (@lem3780319 A _43412 s t' f x' h1)). Qed.
Lemma lem3780795 (b : Prop) (a : Prop) : (a \/ b) = (term55 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3780796 {A : Type'} (f : type686 A) (_43412 : A -> Prop) (x' : A) : (term1032 A x' f _43412) = (term1035 A f _43412 x').
Proof. exact (@lem3780795 (term919 A f _43412) (@I (A -> Prop) _43412 x')). Qed.
Lemma lem3780798 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3780799 {A : Type'} (f : type686 A) (_43412 : A -> Prop) : (term1036 A f _43412) = (@I ((A -> Prop) -> Prop) f _43412).
Proof. exact (@lem3780798 (@I ((A -> Prop) -> Prop) f _43412)). Qed.
Lemma lem3780800 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3780801 {A : Type'} (f : type686 A) (_43412 : A -> Prop) : (term1037 A f _43412) = (term1038 A f _43412).
Proof. exact (MK_COMB (@lem3780800) (@lem3780799 A f _43412)). Qed.
Lemma lem3780802 {A : Type'} (_43412 : A -> Prop) (x' : A) : (@I (A -> Prop) _43412 x') = (@I (A -> Prop) _43412 x').
Proof. exact (eq_refl (@I (A -> Prop) _43412 x')). Qed.
Lemma lem3780803 {A : Type'} (f : type686 A) (_43412 : A -> Prop) (x' : A) : (term1035 A f _43412 x') = (term1039 A f _43412 x').
Proof. exact (MK_COMB (@lem3780801 A f _43412) (@lem3780802 A _43412 x')). Qed.
Lemma lem3780804 {A : Type'} (f : type686 A) (_43412 : A -> Prop) (x' : A) : (term1032 A x' f _43412) = (term1039 A f _43412 x').
Proof. exact (TRANS (@lem3780796 A f _43412 x') (@lem3780803 A f _43412 x')). Qed.
Lemma lem3780807 {A : Type'} (_43412 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term1039 A f _43412 x'.
Proof. exact (EQ_MP (@lem3780804 A f _43412 x') (@lem3780793 A _43412 s t' f x' h1)). Qed.
Lemma lem3780808 {A : Type'} (_43412 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term1039 A f _43412 x'.
Proof. exact (@lem3780807 A _43412 s t' f x' h1). Qed.
Lemma lem3780809 {A : Type'} (t : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term1039 A f t x'.
Proof. exact (@lem3780808 A t s t' f x' h1). Qed.
Lemma lem3780812 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term927 A f t x) (h2 : term931 A s t' f x') : @I (A -> Prop) t x'.
Proof. exact (@lem3780809 A t s t' f x' h2 (@lem3780764 A f t x h1)). Qed.
Lemma lem3780813 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term927 A f t x) (h2 : term931 A s t' f x') : term1029 A t x'.
Proof. exact (fun h0 : term924 A t x' => @lem3780812 A t x s t' f x' h1 h2). Qed.
Lemma lem3780815 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3780816 {A : Type'} (t : A -> Prop) (x' : A) : (term1029 A t x') = (@I (A -> Prop) t x').
Proof. exact (@lem3780815 (@I (A -> Prop) t x')). Qed.
Lemma lem3780817 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term927 A f t x) (h2 : term931 A s t' f x') : @I (A -> Prop) t x'.
Proof. exact (EQ_MP (@lem3780816 A t x') (@lem3780813 A t x s t' f x' h1 h2)). Qed.
Lemma lem3780819 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term924 A s x') : term924 A s x'.
Proof. exact (h1). Qed.
Lemma lem3780820 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term924 A s x') : term1040 A s x'.
Proof. exact (fun h0 : @I (A -> Prop) s x' => @lem3780819 A s x' h1). Qed.
Lemma lem3780822 (p : Prop) : (term1041 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3780823 {A : Type'} (s : A -> Prop) (x' : A) : (term1040 A s x') = (term924 A s x').
Proof. exact (@lem3780822 (@I (A -> Prop) s x')). Qed.
Lemma lem3780824 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term924 A s x') : term924 A s x'.
Proof. exact (EQ_MP (@lem3780823 A s x') (@lem3780820 A s x' h1)). Qed.
Lemma lem3780830 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3780831 {A : Type'} (f : type686 A) (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1028 A f _43410 _43409 s _43411) = (term1042 A f _43410 _43409 s _43411).
Proof. exact (@lem3780830 (term924 A s _43410) (term919 A f _43409) (term1043 A _43410 _43409 s _43411)). Qed.
Lemma lem3780845 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3780846 {A : Type'} (_43410 : A) (f : type686 A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1044 A f _43410 _43409 s _43411) = (term1045 A _43410 f _43409 s _43411).
Proof. exact (@lem3780845 (@I (A -> Prop) _43409 _43410) (term919 A f _43409) (term944 A _43409 s _43411)). Qed.
Lemma lem3780860 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3780861 {A : Type'} (f : type686 A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1046 A f _43409 s _43411) = (term1047 A f _43409 s _43411).
Proof. exact (@lem3780860 (term924 A _43409 _43411) (term919 A f _43409) (@I (A -> Prop) s _43411)). Qed.
Lemma lem3780875 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3780876 {A : Type'} (s : A -> Prop) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1048 A f _43409 s _43411) = (term1049 A s _43411 f _43409).
Proof. exact (@lem3780875 (@I (A -> Prop) s _43411) (term919 A f _43409)). Qed.
Lemma lem3780882 {A : Type'} (_43409 : A -> Prop) (_43411 : A) : (term928 A _43409 _43411) = (term928 A _43409 _43411).
Proof. exact (eq_refl (term928 A _43409 _43411)). Qed.
Lemma lem3780883 {A : Type'} (s : A -> Prop) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1047 A f _43409 s _43411) = (term1050 A s _43411 f _43409).
Proof. exact (MK_COMB (@lem3780882 A _43409 _43411) (@lem3780876 A s _43411 f _43409)). Qed.
Lemma lem3780887 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3780888 {A : Type'} (s : A -> Prop) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1050 A s _43411 f _43409) = (term1051 A s _43411 f _43409).
Proof. exact (@lem3780887 (@I (A -> Prop) s _43411) (term924 A _43409 _43411) (term919 A f _43409)). Qed.
Lemma lem3780904 {A : Type'} (s : A -> Prop) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1047 A f _43409 s _43411) = (term1051 A s _43411 f _43409).
Proof. exact (TRANS (@lem3780883 A s _43411 f _43409) (@lem3780888 A s _43411 f _43409)). Qed.
Lemma lem3780905 {A : Type'} (s : A -> Prop) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1046 A f _43409 s _43411) = (term1051 A s _43411 f _43409).
Proof. exact (TRANS (@lem3780861 A f _43409 s _43411) (@lem3780904 A s _43411 f _43409)). Qed.
Lemma lem3780906 {A : Type'} (_43409 : A -> Prop) (_43410 : A) : (term1052 A _43409 _43410) = (term1052 A _43409 _43410).
Proof. exact (eq_refl (term1052 A _43409 _43410)). Qed.
Lemma lem3780907 {A : Type'} (_43410 : A) (s : A -> Prop) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1045 A _43410 f _43409 s _43411) = (term1053 A _43410 s _43411 f _43409).
Proof. exact (MK_COMB (@lem3780906 A _43409 _43410) (@lem3780905 A s _43411 f _43409)). Qed.
Lemma lem3780918 {A : Type'} (_43410 : A) (s : A -> Prop) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1044 A f _43410 _43409 s _43411) = (term1053 A _43410 s _43411 f _43409).
Proof. exact (TRANS (@lem3780846 A _43410 f _43409 s _43411) (@lem3780907 A _43410 s _43411 f _43409)). Qed.
Lemma lem3780919 {A : Type'} (s : A -> Prop) (_43410 : A) : (term928 A s _43410) = (term928 A s _43410).
Proof. exact (eq_refl (term928 A s _43410)). Qed.
Lemma lem3780920 {A : Type'} (_43410 : A) (s : A -> Prop) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1042 A f _43410 _43409 s _43411) = (term1054 A _43410 s _43411 f _43409).
Proof. exact (MK_COMB (@lem3780919 A s _43410) (@lem3780918 A _43410 s _43411 f _43409)). Qed.
Lemma lem3780924 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3780925 {A : Type'} (_43410 : A) (s : A -> Prop) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1054 A _43410 s _43411 f _43409) = (term1055 A _43410 s _43411 f _43409).
Proof. exact (@lem3780924 (@I (A -> Prop) _43409 _43410) (term924 A s _43410) (term1051 A s _43411 f _43409)). Qed.
Lemma lem3780939 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3780940 {A : Type'} (s : A -> Prop) (_43410 : A) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1056 A _43410 s _43411 f _43409) = (term1057 A s _43410 _43411 f _43409).
Proof. exact (@lem3780939 (@I (A -> Prop) s _43411) (term924 A s _43410) (term1058 A _43411 f _43409)). Qed.
Lemma lem3780954 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3780955 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : (term1059 A s _43410 _43411 f _43409) = (term1060 A _43411 s _43410 f _43409).
Proof. exact (@lem3780954 (term924 A _43409 _43411) (term924 A s _43410) (term919 A f _43409)). Qed.
Lemma lem3780971 {A : Type'} (s : A -> Prop) (_43411 : A) : (term1052 A s _43411) = (term1052 A s _43411).
Proof. exact (eq_refl (term1052 A s _43411)). Qed.
Lemma lem3780972 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : (term1057 A s _43410 _43411 f _43409) = (term1061 A _43411 s _43410 f _43409).
Proof. exact (MK_COMB (@lem3780971 A s _43411) (@lem3780955 A _43411 s _43410 f _43409)). Qed.
Lemma lem3780983 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : (term1056 A _43410 s _43411 f _43409) = (term1061 A _43411 s _43410 f _43409).
Proof. exact (TRANS (@lem3780940 A s _43410 _43411 f _43409) (@lem3780972 A _43411 s _43410 f _43409)). Qed.
Lemma lem3780984 {A : Type'} (_43409 : A -> Prop) (_43410 : A) : (term1052 A _43409 _43410) = (term1052 A _43409 _43410).
Proof. exact (eq_refl (term1052 A _43409 _43410)). Qed.
Lemma lem3780985 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : (term1055 A _43410 s _43411 f _43409) = (term1062 A _43411 s _43410 f _43409).
Proof. exact (MK_COMB (@lem3780984 A _43409 _43410) (@lem3780983 A _43411 s _43410 f _43409)). Qed.
Lemma lem3780996 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : (term1054 A _43410 s _43411 f _43409) = (term1062 A _43411 s _43410 f _43409).
Proof. exact (TRANS (@lem3780925 A _43410 s _43411 f _43409) (@lem3780985 A _43411 s _43410 f _43409)). Qed.
Lemma lem3780997 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : (term1042 A f _43410 _43409 s _43411) = (term1062 A _43411 s _43410 f _43409).
Proof. exact (TRANS (@lem3780920 A _43410 s _43411 f _43409) (@lem3780996 A _43411 s _43410 f _43409)). Qed.
Lemma lem3780998 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : (term1028 A f _43410 _43409 s _43411) = (term1062 A _43411 s _43410 f _43409).
Proof. exact (TRANS (@lem3780831 A f _43410 _43409 s _43411) (@lem3780997 A _43411 s _43410 f _43409)). Qed.
Lemma lem3780999 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3781000 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : (term1063 A f _43410 _43409 s _43411) = (term1064 A _43411 s _43410 f _43409).
Proof. exact (MK_COMB (@lem3780999) (@lem3780998 A _43411 s _43410 f _43409)). Qed.
Lemma lem3781014 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3781015 {A : Type'} (_43410 : A) (f : type686 A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1065 A f _43410 _43409 s _43411) = (term1066 A _43410 f _43409 s _43411).
Proof. exact (@lem3781014 (term924 A s _43410) (term919 A f _43409) (term944 A _43409 s _43411)). Qed.
Lemma lem3781029 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3781030 {A : Type'} (f : type686 A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1046 A f _43409 s _43411) = (term1047 A f _43409 s _43411).
Proof. exact (@lem3781029 (term924 A _43409 _43411) (term919 A f _43409) (@I (A -> Prop) s _43411)). Qed.
Lemma lem3781044 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3781045 {A : Type'} (s : A -> Prop) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1048 A f _43409 s _43411) = (term1049 A s _43411 f _43409).
Proof. exact (@lem3781044 (@I (A -> Prop) s _43411) (term919 A f _43409)). Qed.
Lemma lem3781051 {A : Type'} (_43409 : A -> Prop) (_43411 : A) : (term928 A _43409 _43411) = (term928 A _43409 _43411).
Proof. exact (eq_refl (term928 A _43409 _43411)). Qed.
Lemma lem3781052 {A : Type'} (s : A -> Prop) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1047 A f _43409 s _43411) = (term1050 A s _43411 f _43409).
Proof. exact (MK_COMB (@lem3781051 A _43409 _43411) (@lem3781045 A s _43411 f _43409)). Qed.
Lemma lem3781056 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3781057 {A : Type'} (s : A -> Prop) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1050 A s _43411 f _43409) = (term1051 A s _43411 f _43409).
Proof. exact (@lem3781056 (@I (A -> Prop) s _43411) (term924 A _43409 _43411) (term919 A f _43409)). Qed.
Lemma lem3781073 {A : Type'} (s : A -> Prop) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1047 A f _43409 s _43411) = (term1051 A s _43411 f _43409).
Proof. exact (TRANS (@lem3781052 A s _43411 f _43409) (@lem3781057 A s _43411 f _43409)). Qed.
Lemma lem3781074 {A : Type'} (s : A -> Prop) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1046 A f _43409 s _43411) = (term1051 A s _43411 f _43409).
Proof. exact (TRANS (@lem3781030 A f _43409 s _43411) (@lem3781073 A s _43411 f _43409)). Qed.
Lemma lem3781075 {A : Type'} (s : A -> Prop) (_43410 : A) : (term928 A s _43410) = (term928 A s _43410).
Proof. exact (eq_refl (term928 A s _43410)). Qed.
Lemma lem3781076 {A : Type'} (_43410 : A) (s : A -> Prop) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1066 A _43410 f _43409 s _43411) = (term1056 A _43410 s _43411 f _43409).
Proof. exact (MK_COMB (@lem3781075 A s _43410) (@lem3781074 A s _43411 f _43409)). Qed.
Lemma lem3781080 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3781081 {A : Type'} (s : A -> Prop) (_43410 : A) (_43411 : A) (f : type686 A) (_43409 : A -> Prop) : (term1056 A _43410 s _43411 f _43409) = (term1057 A s _43410 _43411 f _43409).
Proof. exact (@lem3781080 (@I (A -> Prop) s _43411) (term924 A s _43410) (term1058 A _43411 f _43409)). Qed.
Lemma lem3781095 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3781096 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : (term1059 A s _43410 _43411 f _43409) = (term1060 A _43411 s _43410 f _43409).
Proof. exact (@lem3781095 (term924 A _43409 _43411) (term924 A s _43410) (term919 A f _43409)). Qed.
Lemma lem3781112 {A : Type'} (s : A -> Prop) (_43411 : A) : (term1052 A s _43411) = (term1052 A s _43411).
Proof. exact (eq_refl (term1052 A s _43411)). Qed.
Lemma lem3781113 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : (term1057 A s _43410 _43411 f _43409) = (term1061 A _43411 s _43410 f _43409).
Proof. exact (MK_COMB (@lem3781112 A s _43411) (@lem3781096 A _43411 s _43410 f _43409)). Qed.
Lemma lem3781124 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : (term1056 A _43410 s _43411 f _43409) = (term1061 A _43411 s _43410 f _43409).
Proof. exact (TRANS (@lem3781081 A s _43410 _43411 f _43409) (@lem3781113 A _43411 s _43410 f _43409)). Qed.
Lemma lem3781125 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : (term1066 A _43410 f _43409 s _43411) = (term1061 A _43411 s _43410 f _43409).
Proof. exact (TRANS (@lem3781076 A _43410 s _43411 f _43409) (@lem3781124 A _43411 s _43410 f _43409)). Qed.
Lemma lem3781126 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : (term1065 A f _43410 _43409 s _43411) = (term1061 A _43411 s _43410 f _43409).
Proof. exact (TRANS (@lem3781015 A _43410 f _43409 s _43411) (@lem3781125 A _43411 s _43410 f _43409)). Qed.
Lemma lem3781127 {A : Type'} (_43409 : A -> Prop) (_43410 : A) : (term1052 A _43409 _43410) = (term1052 A _43409 _43410).
Proof. exact (eq_refl (term1052 A _43409 _43410)). Qed.
Lemma lem3781128 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : (term1067 A f _43410 _43409 s _43411) = (term1062 A _43411 s _43410 f _43409).
Proof. exact (MK_COMB (@lem3781127 A _43409 _43410) (@lem3781126 A _43411 s _43410 f _43409)). Qed.
Lemma lem3781139 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : ((term1028 A f _43410 _43409 s _43411) = (term1067 A f _43410 _43409 s _43411)) = ((term1062 A _43411 s _43410 f _43409) = (term1062 A _43411 s _43410 f _43409)).
Proof. exact (MK_COMB (@lem3781000 A _43411 s _43410 f _43409) (@lem3781128 A _43411 s _43410 f _43409)). Qed.
Lemma lem3781141 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3781142 (x : Prop) : (x = x) = True.
Proof. exact (@lem3781141 Prop x). Qed.
Lemma lem3781143 {A : Type'} (_43411 : A) (s : A -> Prop) (_43410 : A) (f : type686 A) (_43409 : A -> Prop) : ((term1062 A _43411 s _43410 f _43409) = (term1062 A _43411 s _43410 f _43409)) = True.
Proof. exact (@lem3781142 (term1062 A _43411 s _43410 f _43409)). Qed.
Lemma lem3781144 {A : Type'} (f : type686 A) (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : ((term1028 A f _43410 _43409 s _43411) = (term1067 A f _43410 _43409 s _43411)) = True.
Proof. exact (TRANS (@lem3781139 A _43411 s _43410 f _43409) (@lem3781143 A _43411 s _43410 f _43409)). Qed.
Lemma lem3781145 {A : Type'} (f : type686 A) (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : True = ((term1028 A f _43410 _43409 s _43411) = (term1067 A f _43410 _43409 s _43411)).
Proof. exact (SYM (@lem3781144 A f _43410 _43409 s _43411)). Qed.
Lemma lem3781146 {A : Type'} (f : type686 A) (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1028 A f _43410 _43409 s _43411) = (term1067 A f _43410 _43409 s _43411).
Proof. exact (EQ_MP (@lem3781145 A f _43410 _43409 s _43411) (@lem0)). Qed.
Lemma lem3781147 {A : Type'} (_43410 : A) (_43409 : A -> Prop) (_43411 : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term1067 A f _43410 _43409 s _43411.
Proof. exact (EQ_MP (@lem3781146 A f _43410 _43409 s _43411) (@lem3780311 A _43410 _43409 _43411 s f x'' h1)). Qed.
Lemma lem3781149 (b : Prop) (a : Prop) : (a \/ b) = (term55 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3781150 {A : Type'} (f : type686 A) (s : A -> Prop) (_43411 : A) (_43409 : A -> Prop) (_43410 : A) : (term1067 A f _43410 _43409 s _43411) = (term1068 A f s _43411 _43409 _43410).
Proof. exact (@lem3781149 (term1065 A f _43410 _43409 s _43411) (@I (A -> Prop) _43409 _43410)). Qed.
Lemma lem3781152 (a : Prop) (b : Prop) : (term58 a b) = (term59 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3781153 {A : Type'} (f : type686 A) (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1069 A f _43410 _43409 s _43411) = (term1070 A f _43410 _43409 s _43411).
Proof. exact (@lem3781152 (term919 A f _43409) (term1071 A _43410 _43409 s _43411)). Qed.
Lemma lem3781155 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3781156 {A : Type'} (f : type686 A) (_43409 : A -> Prop) : (term1036 A f _43409) = (@I ((A -> Prop) -> Prop) f _43409).
Proof. exact (@lem3781155 (@I ((A -> Prop) -> Prop) f _43409)). Qed.
Lemma lem3781157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3781158 {A : Type'} (f : type686 A) (_43409 : A -> Prop) : (term1072 A f _43409) = (term926 A f _43409).
Proof. exact (MK_COMB (@lem3781157) (@lem3781156 A f _43409)). Qed.
Lemma lem3781160 (a : Prop) (b : Prop) : (term58 a b) = (term59 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3781161 {A : Type'} (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1073 A _43410 _43409 s _43411) = (term1074 A _43410 _43409 s _43411).
Proof. exact (@lem3781160 (term924 A s _43410) (term944 A _43409 s _43411)). Qed.
Lemma lem3781163 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3781164 {A : Type'} (s : A -> Prop) (_43410 : A) : (term1075 A s _43410) = (@I (A -> Prop) s _43410).
Proof. exact (@lem3781163 (@I (A -> Prop) s _43410)). Qed.
Lemma lem3781165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3781166 {A : Type'} (s : A -> Prop) (_43410 : A) : (term1076 A s _43410) = (term932 A s _43410).
Proof. exact (MK_COMB (@lem3781165) (@lem3781164 A s _43410)). Qed.
Lemma lem3781168 (a : Prop) (b : Prop) : (term58 a b) = (term59 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3781169 {A : Type'} (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1077 A _43409 s _43411) = (term1078 A _43409 s _43411).
Proof. exact (@lem3781168 (term924 A _43409 _43411) (@I (A -> Prop) s _43411)). Qed.
Lemma lem3781171 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3781172 {A : Type'} (_43409 : A -> Prop) (_43411 : A) : (term1075 A _43409 _43411) = (@I (A -> Prop) _43409 _43411).
Proof. exact (@lem3781171 (@I (A -> Prop) _43409 _43411)). Qed.
Lemma lem3781173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3781174 {A : Type'} (_43409 : A -> Prop) (_43411 : A) : (term1076 A _43409 _43411) = (term932 A _43409 _43411).
Proof. exact (MK_COMB (@lem3781173) (@lem3781172 A _43409 _43411)). Qed.
Lemma lem3781175 {A : Type'} (s : A -> Prop) (_43411 : A) : (term924 A s _43411) = (term924 A s _43411).
Proof. exact (eq_refl (term924 A s _43411)). Qed.
Lemma lem3781176 {A : Type'} (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1078 A _43409 s _43411) = (term1079 A _43409 s _43411).
Proof. exact (MK_COMB (@lem3781174 A _43409 _43411) (@lem3781175 A s _43411)). Qed.
Lemma lem3781177 {A : Type'} (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1077 A _43409 s _43411) = (term1079 A _43409 s _43411).
Proof. exact (TRANS (@lem3781169 A _43409 s _43411) (@lem3781176 A _43409 s _43411)). Qed.
Lemma lem3781178 {A : Type'} (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1074 A _43410 _43409 s _43411) = (term1080 A _43410 _43409 s _43411).
Proof. exact (MK_COMB (@lem3781166 A s _43410) (@lem3781177 A _43409 s _43411)). Qed.
Lemma lem3781179 {A : Type'} (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1073 A _43410 _43409 s _43411) = (term1080 A _43410 _43409 s _43411).
Proof. exact (TRANS (@lem3781161 A _43410 _43409 s _43411) (@lem3781178 A _43410 _43409 s _43411)). Qed.
Lemma lem3781180 {A : Type'} (f : type686 A) (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1070 A f _43410 _43409 s _43411) = (term1081 A f _43410 _43409 s _43411).
Proof. exact (MK_COMB (@lem3781158 A f _43409) (@lem3781179 A _43410 _43409 s _43411)). Qed.
Lemma lem3781181 {A : Type'} (f : type686 A) (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1069 A f _43410 _43409 s _43411) = (term1081 A f _43410 _43409 s _43411).
Proof. exact (TRANS (@lem3781153 A f _43410 _43409 s _43411) (@lem3781180 A f _43410 _43409 s _43411)). Qed.
Lemma lem3781182 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3781183 {A : Type'} (f : type686 A) (_43410 : A) (_43409 : A -> Prop) (s : A -> Prop) (_43411 : A) : (term1082 A f _43410 _43409 s _43411) = (term1083 A f _43410 _43409 s _43411).
Proof. exact (MK_COMB (@lem3781182) (@lem3781181 A f _43410 _43409 s _43411)). Qed.
Lemma lem3781184 {A : Type'} (_43409 : A -> Prop) (_43410 : A) : (@I (A -> Prop) _43409 _43410) = (@I (A -> Prop) _43409 _43410).
Proof. exact (eq_refl (@I (A -> Prop) _43409 _43410)). Qed.
Lemma lem3781185 {A : Type'} (f : type686 A) (s : A -> Prop) (_43411 : A) (_43409 : A -> Prop) (_43410 : A) : (term1068 A f s _43411 _43409 _43410) = (term1084 A f s _43411 _43409 _43410).
Proof. exact (MK_COMB (@lem3781183 A f _43410 _43409 s _43411) (@lem3781184 A _43409 _43410)). Qed.
Lemma lem3781186 {A : Type'} (f : type686 A) (s : A -> Prop) (_43411 : A) (_43409 : A -> Prop) (_43410 : A) : (term1067 A f _43410 _43409 s _43411) = (term1084 A f s _43411 _43409 _43410).
Proof. exact (TRANS (@lem3781150 A f s _43411 _43409 _43410) (@lem3781185 A f s _43411 _43409 _43410)). Qed.
Lemma lem3781188 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term927 A f t x) (h3 : term931 A s t' f x') : term1079 A t s x'.
Proof. exact (conj (@lem3780817 A t x s t' f x' h2 h3) (@lem3780824 A s x' h1)). Qed.
Lemma lem3781189 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term927 A f t x) (h3 : term938 A f t s x) (h4 : term931 A s t' f x') : term1080 A x t s x'.
Proof. exact (conj (@lem3780757 A f t s x h3) (@lem3781188 A t x s t' f x' h1 h2 h4)). Qed.
Lemma lem3781190 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term927 A f t x) (h3 : term938 A f t s x) (h4 : term931 A s t' f x') : term1081 A f x t s x'.
Proof. exact (conj (@lem3780750 A f t x h2) (@lem3781189 A t x s t' f x' h1 h2 h3 h4)). Qed.
Lemma lem3781192 {A : Type'} (_43411 : A) (_43409 : A -> Prop) (_43410 : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term1084 A f s _43411 _43409 _43410.
Proof. exact (EQ_MP (@lem3781186 A f s _43411 _43409 _43410) (@lem3781147 A _43410 _43409 _43411 s f x'' h1)). Qed.
Lemma lem3781193 {A : Type'} (_43411 : A) (_43409 : A -> Prop) (_43410 : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term1084 A f s _43411 _43409 _43410.
Proof. exact (@lem3781192 A _43411 _43409 _43410 s f x'' h1). Qed.
Lemma lem3781194 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term618 A s f x'') : term1084 A f s x' t x.
Proof. exact (@lem3781193 A x' t x s f x'' h1). Qed.
Lemma lem3781197 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term618 A s f x'') (h3 : term927 A f t x) (h4 : term938 A f t s x) (h5 : term931 A s t' f x') : @I (A -> Prop) t x.
Proof. exact (@lem3781194 A x' t x s f x'' h2 (@lem3781190 A t x s t' f x' h1 h3 h4 h5)). Qed.
Lemma lem3781198 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term618 A s f x'') (h3 : term927 A f t x) (h4 : term938 A f t s x) (h5 : term931 A s t' f x') : term1029 A t x.
Proof. exact (fun h0 : term924 A t x => @lem3781197 A x'' t x s t' f x' h1 h2 h3 h4 h5). Qed.
Lemma lem3781200 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3781201 {A : Type'} (t : A -> Prop) (x : A) : (term1029 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3781200 (@I (A -> Prop) t x)). Qed.
Lemma lem3781202 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term618 A s f x'') (h3 : term927 A f t x) (h4 : term938 A f t s x) (h5 : term931 A s t' f x') : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem3781201 A t x) (@lem3781198 A x'' t x s t' f x' h1 h2 h3 h4 h5)). Qed.
Lemma lem3781205 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3781207 {A : Type'} (t : A -> Prop) (x : A) : (term924 A t x) = (term1030 A t x).
Proof. exact (@lem3781205 (@I (A -> Prop) t x)). Qed.
Lemma lem3781210 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term927 A f t x) : term1030 A t x.
Proof. exact (EQ_MP (@lem3781207 A t x) (@lem3780327 A f t x h1)). Qed.
Lemma lem3781213 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term618 A s f x'') (h3 : term927 A f t x) (h4 : term938 A f t s x) (h5 : term931 A s t' f x') : False.
Proof. exact (@lem3781210 A f t x h3 (@lem3781202 A x'' t x s t' f x' h1 h2 h3 h4 h5)). Qed.
Lemma lem3781214 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term618 A s f x'') (h3 : term927 A f t x) (h4 : term938 A f t s x) (h5 : term931 A s t' f x') : term32.
Proof. exact (fun h0 : ~ False => @lem3781213 A x'' t x s t' f x' h1 h2 h3 h4 h5). Qed.
Lemma lem3781216 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3781217 : term32 = False.
Proof. exact (@lem3781216 False). Qed.
Lemma lem3781218 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term618 A s f x'') (h3 : term927 A f t x) (h4 : term938 A f t s x) (h5 : term931 A s t' f x') : False.
Proof. exact (EQ_MP (@lem3781217) (@lem3781214 A x'' t x s t' f x' h1 h2 h3 h4 h5)). Qed.
Lemma lem3781220 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem3774804 A f s x h1)). Qed.
Lemma lem3781221 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term1029 A s x.
Proof. exact (fun h0 : term924 A s x => @lem3781220 A f s x h1). Qed.
Lemma lem3781223 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3781224 {A : Type'} (s : A -> Prop) (x : A) : (term1029 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3781223 (@I (A -> Prop) s x)). Qed.
Lemma lem3781225 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3781224 A s x) (@lem3781221 A f s x h1)). Qed.
Lemma lem3781228 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3781230 {A : Type'} (s : A -> Prop) (x : A) : (term924 A s x) = (term1030 A s x).
Proof. exact (@lem3781228 (@I (A -> Prop) s x)). Qed.
Lemma lem3781233 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term1030 A s x.
Proof. exact (EQ_MP (@lem3781230 A s x) (@lem3780405 A f s x h1)). Qed.
Lemma lem3781236 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : False.
Proof. exact (@lem3781233 A f s x h1 (@lem3781225 A f s x h1)). Qed.
Lemma lem3781237 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : term32.
Proof. exact (fun h0 : ~ False => @lem3781236 A f s x h1). Qed.
Lemma lem3781239 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3781240 : term32 = False.
Proof. exact (@lem3781239 False). Qed.
Lemma lem3781241 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term939 A f s x) : False.
Proof. exact (EQ_MP (@lem3781240) (@lem3781237 A f s x h1)). Qed.
Lemma lem3781243 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem3774802 A f t s x h1)). Qed.
Lemma lem3781244 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : term1029 A s x.
Proof. exact (fun h0 : term924 A s x => @lem3781243 A f t s x h1). Qed.
Lemma lem3781246 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3781247 {A : Type'} (s : A -> Prop) (x : A) : (term1029 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3781246 (@I (A -> Prop) s x)). Qed.
Lemma lem3781248 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term938 A f t s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3781247 A s x) (@lem3781244 A f t s x h1)). Qed.
Lemma lem3781251 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3781253 {A : Type'} (s : A -> Prop) (x : A) : (term924 A s x) = (term1030 A s x).
Proof. exact (@lem3781251 (@I (A -> Prop) s x)). Qed.
Lemma lem3781256 {A : Type'} (s : A -> Prop) (x : A) (h1 : term924 A s x) : term1030 A s x.
Proof. exact (EQ_MP (@lem3781253 A s x) (@lem3780493 A s x h1)). Qed.
Lemma lem3781259 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : False.
Proof. exact (@lem3781256 A s x h1 (@lem3781248 A f t s x h2)). Qed.
Lemma lem3781260 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : term32.
Proof. exact (fun h0 : ~ False => @lem3781259 A f t s x h1 h2). Qed.
Lemma lem3781262 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3781263 : term32 = False.
Proof. exact (@lem3781262 False). Qed.
Lemma lem3781264 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : False.
Proof. exact (EQ_MP (@lem3781263) (@lem3781260 A f t s x h1 h2)). Qed.
Lemma lem3781266 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term927 A f t' x') : @I ((A -> Prop) -> Prop) f t'.
Proof. exact (proj1 (@lem3774786 A f t' x' h1)). Qed.
Lemma lem3781267 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term927 A f t' x') : term1031 A f t'.
Proof. exact (fun h0 : term919 A f t' => @lem3781266 A f t' x' h1). Qed.
Lemma lem3781269 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3781270 {A : Type'} (f : type686 A) (t' : A -> Prop) : (term1031 A f t') = (@I ((A -> Prop) -> Prop) f t').
Proof. exact (@lem3781269 (@I ((A -> Prop) -> Prop) f t')). Qed.
Lemma lem3781271 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term927 A f t' x') : @I ((A -> Prop) -> Prop) f t'.
Proof. exact (EQ_MP (@lem3781270 A f t') (@lem3781267 A f t' x' h1)). Qed.
Lemma lem3781277 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3781278 {A : Type'} (x' : A) (f : type686 A) (_43446 : A -> Prop) : (term921 A f _43446 x') = (term1032 A x' f _43446).
Proof. exact (@lem3781277 (@I (A -> Prop) _43446 x') (term919 A f _43446)). Qed.
Lemma lem3781284 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3781285 {A : Type'} (x' : A) (f : type686 A) (_43446 : A -> Prop) : (term1033 A f _43446 x') = (term1034 A x' f _43446).
Proof. exact (MK_COMB (@lem3781284) (@lem3781278 A x' f _43446)). Qed.
Lemma lem3781291 {A : Type'} (x' : A) (f : type686 A) (_43446 : A -> Prop) : (term1032 A x' f _43446) = (term1032 A x' f _43446).
Proof. exact (eq_refl (term1032 A x' f _43446)). Qed.
Lemma lem3781292 {A : Type'} (x' : A) (f : type686 A) (_43446 : A -> Prop) : ((term921 A f _43446 x') = (term1032 A x' f _43446)) = ((term1032 A x' f _43446) = (term1032 A x' f _43446)).
Proof. exact (MK_COMB (@lem3781285 A x' f _43446) (@lem3781291 A x' f _43446)). Qed.
Lemma lem3781294 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3781295 (x : Prop) : (x = x) = True.
Proof. exact (@lem3781294 Prop x). Qed.
Lemma lem3781296 {A : Type'} (x' : A) (f : type686 A) (_43446 : A -> Prop) : ((term1032 A x' f _43446) = (term1032 A x' f _43446)) = True.
Proof. exact (@lem3781295 (term1032 A x' f _43446)). Qed.
Lemma lem3781297 {A : Type'} (x' : A) (f : type686 A) (_43446 : A -> Prop) : ((term921 A f _43446 x') = (term1032 A x' f _43446)) = True.
Proof. exact (TRANS (@lem3781292 A x' f _43446) (@lem3781296 A x' f _43446)). Qed.
Lemma lem3781298 {A : Type'} (x' : A) (f : type686 A) (_43446 : A -> Prop) : True = ((term921 A f _43446 x') = (term1032 A x' f _43446)).
Proof. exact (SYM (@lem3781297 A x' f _43446)). Qed.
Lemma lem3781299 {A : Type'} (x' : A) (f : type686 A) (_43446 : A -> Prop) : (term921 A f _43446 x') = (term1032 A x' f _43446).
Proof. exact (EQ_MP (@lem3781298 A x' f _43446) (@lem0)). Qed.
Lemma lem3781300 {A : Type'} (_43446 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term1032 A x' f _43446.
Proof. exact (EQ_MP (@lem3781299 A x' f _43446) (@lem3780565 A _43446 s t' f x' h1)). Qed.
Lemma lem3781302 (b : Prop) (a : Prop) : (a \/ b) = (term55 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3781303 {A : Type'} (f : type686 A) (_43446 : A -> Prop) (x' : A) : (term1032 A x' f _43446) = (term1035 A f _43446 x').
Proof. exact (@lem3781302 (term919 A f _43446) (@I (A -> Prop) _43446 x')). Qed.
Lemma lem3781305 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3781306 {A : Type'} (f : type686 A) (_43446 : A -> Prop) : (term1036 A f _43446) = (@I ((A -> Prop) -> Prop) f _43446).
Proof. exact (@lem3781305 (@I ((A -> Prop) -> Prop) f _43446)). Qed.
Lemma lem3781307 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3781308 {A : Type'} (f : type686 A) (_43446 : A -> Prop) : (term1037 A f _43446) = (term1038 A f _43446).
Proof. exact (MK_COMB (@lem3781307) (@lem3781306 A f _43446)). Qed.
Lemma lem3781309 {A : Type'} (_43446 : A -> Prop) (x' : A) : (@I (A -> Prop) _43446 x') = (@I (A -> Prop) _43446 x').
Proof. exact (eq_refl (@I (A -> Prop) _43446 x')). Qed.
Lemma lem3781310 {A : Type'} (f : type686 A) (_43446 : A -> Prop) (x' : A) : (term1035 A f _43446 x') = (term1039 A f _43446 x').
Proof. exact (MK_COMB (@lem3781308 A f _43446) (@lem3781309 A _43446 x')). Qed.
Lemma lem3781311 {A : Type'} (f : type686 A) (_43446 : A -> Prop) (x' : A) : (term1032 A x' f _43446) = (term1039 A f _43446 x').
Proof. exact (TRANS (@lem3781303 A f _43446 x') (@lem3781310 A f _43446 x')). Qed.
Lemma lem3781314 {A : Type'} (_43446 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term1039 A f _43446 x'.
Proof. exact (EQ_MP (@lem3781311 A f _43446 x') (@lem3781300 A _43446 s t' f x' h1)). Qed.
Lemma lem3781315 {A : Type'} (_43446 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term1039 A f _43446 x'.
Proof. exact (@lem3781314 A _43446 s t' f x' h1). Qed.
Lemma lem3781316 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term931 A s t' f x') : term1039 A f t' x'.
Proof. exact (@lem3781315 A t' s t' f x' h1). Qed.
Lemma lem3781319 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term927 A f t' x') (h2 : term931 A s t' f x') : @I (A -> Prop) t' x'.
Proof. exact (@lem3781316 A s t' f x' h2 (@lem3781271 A f t' x' h1)). Qed.
Lemma lem3781320 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term927 A f t' x') (h2 : term931 A s t' f x') : term1029 A t' x'.
Proof. exact (fun h0 : term924 A t' x' => @lem3781319 A s t' f x' h1 h2). Qed.
Lemma lem3781322 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3781323 {A : Type'} (t' : A -> Prop) (x' : A) : (term1029 A t' x') = (@I (A -> Prop) t' x').
Proof. exact (@lem3781322 (@I (A -> Prop) t' x')). Qed.
Lemma lem3781324 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term927 A f t' x') (h2 : term931 A s t' f x') : @I (A -> Prop) t' x'.
Proof. exact (EQ_MP (@lem3781323 A t' x') (@lem3781320 A s t' f x' h1 h2)). Qed.
Lemma lem3781327 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3781329 {A : Type'} (t' : A -> Prop) (x' : A) : (term924 A t' x') = (term1030 A t' x').
Proof. exact (@lem3781327 (@I (A -> Prop) t' x')). Qed.
Lemma lem3781332 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term927 A f t' x') : term1030 A t' x'.
Proof. exact (EQ_MP (@lem3781329 A t' x') (@lem3780569 A f t' x' h1)). Qed.
Lemma lem3781335 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term927 A f t' x') (h2 : term931 A s t' f x') : False.
Proof. exact (@lem3781332 A f t' x' h1 (@lem3781324 A s t' f x' h1 h2)). Qed.
Lemma lem3781336 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term927 A f t' x') (h2 : term931 A s t' f x') : term32.
Proof. exact (fun h0 : ~ False => @lem3781335 A s t' f x' h1 h2). Qed.
Lemma lem3781338 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3781339 : term32 = False.
Proof. exact (@lem3781338 False). Qed.
Lemma lem3781340 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term927 A f t' x') (h2 : term931 A s t' f x') : False.
Proof. exact (EQ_MP (@lem3781339) (@lem3781336 A s t' f x' h1 h2)). Qed.
Lemma lem3781341 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : (term924 A s x) = False.
Proof. exact (prop_ext (fun h3 : term924 A s x => @lem3781264 A f t s x h1 h2) (fun h3 : False => @lem3780493 A s x h1)). Qed.
Lemma lem3781342 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : False.
Proof. exact (EQ_MP (@lem3781341 A f t s x h1 h2) (@lem3780493 A s x h1)). Qed.
Lemma lem3781343 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term618 A s f x'') (h3 : term927 A f t x) (h4 : term938 A f t s x) (h5 : term931 A s t' f x') : (term924 A s x') = False.
Proof. exact (prop_ext (fun h6 : term924 A s x' => @lem3781218 A x'' t x s t' f x' h1 h2 h3 h4 h5) (fun h6 : False => @lem3780321 A s x' h1)). Qed.
Lemma lem3781344 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term618 A s f x'') (h3 : term927 A f t x) (h4 : term938 A f t s x) (h5 : term931 A s t' f x') : False.
Proof. exact (EQ_MP (@lem3781343 A x'' t x s t' f x' h1 h2 h3 h4 h5) (@lem3780321 A s x' h1)). Qed.
Lemma lem3781345 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : (term924 A s x) = False.
Proof. exact (prop_ext (fun h3 : term924 A s x => @lem3780743 A f t s x h1 h2) (fun h3 : False => @lem3780247 A s x h1)). Qed.
Lemma lem3781346 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : False.
Proof. exact (EQ_MP (@lem3781345 A f t s x h1 h2) (@lem3780247 A s x h1)). Qed.
Lemma lem3781347 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : (term924 A s x) = False.
Proof. exact (prop_ext (fun h3 : term924 A s x => @lem3780621 A f t s x h1 h2) (fun h3 : False => @lem3780001 A s x h1)). Qed.
Lemma lem3781348 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : False.
Proof. exact (EQ_MP (@lem3781347 A f t s x h1 h2) (@lem3780001 A s x h1)). Qed.
Lemma lem3781349 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : (term924 A s x) = False.
Proof. exact (prop_ext (fun h3 : term924 A s x => @lem3781342 A f t s x h1 h2) (fun h3 : False => @lem3779003 A s x h1)). Qed.
Lemma lem3781350 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : False.
Proof. exact (EQ_MP (@lem3781349 A f t s x h1 h2) (@lem3779003 A s x h1)). Qed.
Lemma lem3781351 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term618 A s f x'') (h3 : term927 A f t x) (h4 : term938 A f t s x) (h5 : term931 A s t' f x') : (term924 A s x') = False.
Proof. exact (prop_ext (fun h6 : term924 A s x' => @lem3781344 A x'' t x s t' f x' h1 h2 h3 h4 h5) (fun h6 : False => @lem3777942 A s x' h1)). Qed.
Lemma lem3781352 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term618 A s f x'') (h3 : term927 A f t x) (h4 : term938 A f t s x) (h5 : term931 A s t' f x') : False.
Proof. exact (EQ_MP (@lem3781351 A x'' t x s t' f x' h1 h2 h3 h4 h5) (@lem3777942 A s x' h1)). Qed.
Lemma lem3781353 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : (term924 A s x) = False.
Proof. exact (prop_ext (fun h3 : term924 A s x => @lem3781346 A f t s x h1 h2) (fun h3 : False => @lem3777436 A s x h1)). Qed.
Lemma lem3781354 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : False.
Proof. exact (EQ_MP (@lem3781353 A f t s x h1 h2) (@lem3777436 A s x h1)). Qed.
Lemma lem3781355 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : (term924 A s x) = False.
Proof. exact (prop_ext (fun h3 : term924 A s x => @lem3781348 A f t s x h1 h2) (fun h3 : False => @lem3775869 A s x h1)). Qed.
Lemma lem3781356 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : False.
Proof. exact (EQ_MP (@lem3781355 A f t s x h1 h2) (@lem3775869 A s x h1)). Qed.
Lemma lem3781357 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : (term924 A s x) = False.
Proof. exact (prop_ext (fun h3 : term924 A s x => @lem3781350 A f t s x h1 h2) (fun h3 : False => @lem3779003 A s x h1)). Qed.
Lemma lem3781358 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : False.
Proof. exact (EQ_MP (@lem3781357 A f t s x h1 h2) (@lem3779003 A s x h1)). Qed.
Lemma lem3781359 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term618 A s f x'') (h3 : term927 A f t x) (h4 : term938 A f t s x) (h5 : term931 A s t' f x') : (term924 A s x') = False.
Proof. exact (prop_ext (fun h6 : term924 A s x' => @lem3781352 A x'' t x s t' f x' h1 h2 h3 h4 h5) (fun h6 : False => @lem3777942 A s x' h1)). Qed.
Lemma lem3781360 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term618 A s f x'') (h3 : term927 A f t x) (h4 : term938 A f t s x) (h5 : term931 A s t' f x') : False.
Proof. exact (EQ_MP (@lem3781359 A x'' t x s t' f x' h1 h2 h3 h4 h5) (@lem3777942 A s x' h1)). Qed.
Lemma lem3781361 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : (term924 A s x) = False.
Proof. exact (prop_ext (fun h3 : term924 A s x => @lem3781354 A f t s x h1 h2) (fun h3 : False => @lem3777436 A s x h1)). Qed.
Lemma lem3781362 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : False.
Proof. exact (EQ_MP (@lem3781361 A f t s x h1 h2) (@lem3777436 A s x h1)). Qed.
Lemma lem3781363 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : (term924 A s x) = False.
Proof. exact (prop_ext (fun h3 : term924 A s x => @lem3781356 A f t s x h1 h2) (fun h3 : False => @lem3775869 A s x h1)). Qed.
Lemma lem3781364 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term924 A s x) (h2 : term938 A f t s x) : False.
Proof. exact (EQ_MP (@lem3781363 A f t s x h1 h2) (@lem3775869 A s x h1)). Qed.
Lemma lem3781365 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term927 A f t' x') (h2 : term938 A f t s x) (h3 : term931 A s t' f x') : False.
Proof. exact (or_elim (@lem3774808 A f t s x h2) (fun h0 : term924 A s x => @lem3781358 A f t s x h0 h2) (fun h0 : term927 A f t x => @lem3781340 A s t' f x' h1 h3)). Qed.
Lemma lem3781366 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term927 A f t' x') (h2 : term931 A s t' f x') (h3 : term909 A t x s t' f x') : False.
Proof. exact (or_elim (@lem3774762 A t x s t' f x' h3) (fun h0 : term939 A f s x => @lem3781241 A f s x h0) (fun h0 : term938 A f t s x => @lem3781365 A t x s t' f x' h1 h0 h2)). Qed.
Lemma lem3781367 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term618 A s f x'') (h3 : term938 A f t s x) (h4 : term931 A s t' f x') : False.
Proof. exact (or_elim (@lem3774794 A f t s x h3) (fun h0 : term924 A s x => @lem3781362 A f t s x h0 h3) (fun h0 : term927 A f t x => @lem3781360 A x'' t x s t' f x' h1 h2 h0 h3 h4)). Qed.
Lemma lem3781368 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term924 A s x') (h2 : term618 A s f x'') (h3 : term931 A s t' f x') (h4 : term909 A t x s t' f x') : False.
Proof. exact (or_elim (@lem3774762 A t x s t' f x' h4) (fun h0 : term939 A f s x => @lem3780720 A f s x h0) (fun h0 : term938 A f t s x => @lem3781367 A x'' t x s t' f x' h1 h2 h0 h3)). Qed.
Lemma lem3781369 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term618 A s f x'') (h2 : term931 A s t' f x') (h3 : term909 A t x s t' f x') : False.
Proof. exact (or_elim (@lem3774784 A s t' f x' h2) (fun h0 : term924 A s x' => @lem3781368 A x'' t x s t' f x' h0 h1 h2 h3) (fun h0 : term927 A f t' x' => @lem3781366 A t x s t' f x' h0 h2 h3)). Qed.
Lemma lem3781370 {A : Type'} (t' : A -> Prop) (x' : A) (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term935 A s f t' x') (h2 : term938 A f t s x) : False.
Proof. exact (or_elim (@lem3774778 A f t s x h2) (fun h0 : term924 A s x => @lem3781364 A f t s x h0 h2) (fun h0 : term927 A f t x => @lem3780697 A s f t' x' h1)). Qed.
Lemma lem3781371 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term935 A s f t' x') (h2 : term909 A t x s t' f x') : False.
Proof. exact (or_elim (@lem3774762 A t x s t' f x' h2) (fun h0 : term939 A f s x => @lem3780598 A f s x h0) (fun h0 : term938 A f t s x => @lem3781370 A t' x' f t s x h1 h0)). Qed.
Lemma lem3781372 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term618 A s f x'') (h2 : term909 A t x s t' f x') : False.
Proof. exact (or_elim (@lem3774761 A t x s t' f x' h2) (fun h0 : term935 A s f t' x' => @lem3781371 A t x s t' f x' h0 h2) (fun h0 : term931 A s t' f x' => @lem3781369 A x'' t x s t' f x' h1 h0 h2)). Qed.
Lemma lem3781373 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term513 A s f) (h2 : term909 A t x s t' f x') : False.
Proof. exact (ex_elim (@lem3773330 A s f h1) (fun x'' : A -> Prop => fun h0 : term620 A s f x'' => @lem3781372 A x'' t x s t' f x' h0 h2)). Qed.
Lemma lem3781374 {A : Type'} (t : A -> Prop) (x : A) (x' : A) (s : A -> Prop) (f : type686 A) (h1 : term912 A t x s f x') (h2 : term513 A s f) : False.
Proof. exact (ex_elim (@lem3774294 A t x s f x' h1) (fun t' : A -> Prop => fun h0 : term911 A t x s f x' t' => @lem3781373 A t x s t' f x' h2 h0)). Qed.
Lemma lem3781375 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (h1 : term914 A t x s f) (h2 : term513 A s f) : False.
Proof. exact (ex_elim (@lem3774293 A t x s f h1) (fun x' : A => fun h0 : term913 A t x s f x' => @lem3781374 A t x x' s f h0 h2)). Qed.
Lemma lem3781376 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) (h1 : term916 A x s f) (h2 : term513 A s f) : False.
Proof. exact (ex_elim (@lem3774292 A x s f h1) (fun t : A -> Prop => fun h0 : term915 A x s f t => @lem3781375 A t x s f h0 h2)). Qed.
Lemma lem3781377 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term555 A s f) (h2 : term513 A s f) : False.
Proof. exact (ex_elim (@lem3774291 A s f h1) (fun x : A => fun h0 : term917 A s f x => @lem3781376 A x s f h0 h2)). Qed.
Lemma lem3781378 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term555 A s f) (h2 : term513 A s f) : (term555 A s f) = False.
Proof. exact (prop_ext (fun h3 : term555 A s f => @lem3781377 A s f h1 h2) (fun h3 : False => @lem3772761 A s f h1)). Qed.
Lemma lem3781379 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term555 A s f) (h2 : term513 A s f) : False.
Proof. exact (EQ_MP (@lem3781378 A s f h1 h2) (@lem3772761 A s f h1)). Qed.
Lemma lem3781380 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term513 A s f) : term554 A s f.
Proof. exact (fun h0 : term555 A s f => @lem3781379 A s f h0 h1). Qed.
Lemma lem3781381 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term513 A s f) : term538 A s f.
Proof. exact (EQ_MP (@lem3772760 A s f) (@lem3781380 A s f h1)). Qed.
Lemma lem3781382 {A : Type'} (s : A -> Prop) (f : type686 A) : term539 A s f.
Proof. exact (fun h0 : term513 A s f => @lem3781381 A s f h0). Qed.
Lemma lem3781387 {A : Type'} (f : type686 A) : term549 A f.
Proof. exact (fun s : A -> Prop => @lem3781382 A s f). Qed.
Lemma lem3781392 {A : Type'} : term553 A.
Proof. exact (fun f : type686 A => @lem3781387 A f). Qed.
Lemma lem3781393 {A : Type'} : term552 A.
Proof. exact (EQ_MP (@lem3772755 A) (@lem3781392 A)). Qed.
Lemma lem3781394 {A : Type'} (f : type686 A) : term1085 A f.
Proof. exact (@lem3781393 A f). Qed.
Lemma lem3781395 {A : Type'} (f : type686 A) : (term1085 A f) = (term548 A f).
Proof. exact (eq_refl (term1085 A f)). Qed.
Lemma lem3781396 {A : Type'} (f : type686 A) : term548 A f.
Proof. exact (EQ_MP (@lem3781395 A f) (@lem3781394 A f)). Qed.
Lemma lem3781397 {A : Type'} (f : type686 A) (s : A -> Prop) : term1086 A f s.
Proof. exact (@lem3781396 A f s). Qed.
Lemma lem3781398 {A : Type'} (s : A -> Prop) (f : type686 A) : (term1086 A f s) = (term540 A s f).
Proof. exact (eq_refl (term1086 A f s)). Qed.
Lemma lem3781399 {A : Type'} (s : A -> Prop) (f : type686 A) : term540 A s f.
Proof. exact (EQ_MP (@lem3781398 A s f) (@lem3781397 A f s)). Qed.
Lemma lem3781401 {A : Type'} (s : A -> Prop) (f : type686 A) : term540 A s f.
Proof. exact (@lem3772295 A s f (@lem3781399 A s f)). Qed.
Lemma lem3781402 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term541 A s f) : False.
Proof. exact (@lem3781401 A s f (@lem3772279 A s f h1)). Qed.
Lemma lem3781403 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term541 A s f) : (term541 A s f) = False.
Proof. exact (prop_ext (fun h2 : term541 A s f => @lem3781402 A s f h1) (fun h2 : False => @lem3772279 A s f h1)). Qed.
Lemma lem3781404 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term541 A s f) : False.
Proof. exact (EQ_MP (@lem3781403 A s f h1) (@lem3772279 A s f h1)). Qed.
Lemma lem3781405 {A : Type'} (s : A -> Prop) (f : type686 A) : term540 A s f.
Proof. exact (fun h0 : term541 A s f => @lem3781404 A s f h0). Qed.
Lemma lem3781406 {A : Type'} (s : A -> Prop) (f : type686 A) : term539 A s f.
Proof. exact (EQ_MP (@lem3772278 A s f) (@lem3781405 A s f)). Qed.
Lemma lem3781407 {A : Type'} (s : A -> Prop) (f : type686 A) : term481 A s f.
Proof. exact (EQ_MP (@lem3772274 A s f) (@lem3781406 A s f)). Qed.
Lemma lem3781408 {A : Type'} (s : A -> Prop) (f : type686 A) : term480 A s f.
Proof. exact (EQ_MP (@lem3771779 A s f) (@lem3781407 A s f)). Qed.
Lemma lem3781409 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : @SUBSET A s s) : term478 A s f.
Proof. exact (@lem3781408 A s f (@lem3771515 A f s h1 h2 h3 h4 h5)). Qed.
Lemma lem3781410 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : @SUBSET A s s) : term430 A s f.
Proof. exact (@lem3771501 A s f (@lem3781409 A f s h1 h2 h3 h4 h5)). Qed.
Lemma lem3781411 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : @SUBSET A s s) : term429 A s f.
Proof. exact (EQ_MP (@lem3771497 A s f h1) (@lem3781410 A f s h1 h2 h3 h4 h5)). Qed.
Lemma lem3781412 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : term270 A f) (h6 : @SUBSET A s s) : term412 A s f.
Proof. exact (@lem3781411 A f s h1 h2 h3 h4 h6 (@lem3771422 A f h5)). Qed.
Lemma lem3781413 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term381 A s f) : term380 A s f.
Proof. exact (proj2 (@lem3771423 A s f h1)). Qed.
Lemma lem3781414 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term381 A s f) : term334 A f s.
Proof. exact (proj1 (@lem3771423 A s f h1)). Qed.
Lemma lem3781415 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term380 A s f) : term268 A f.
Proof. exact (proj2 (@lem3771424 A s f h1)). Qed.
Lemma lem3781416 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term380 A s f) : term375 A f s.
Proof. exact (proj1 (@lem3771424 A s f h1)). Qed.
Lemma lem3781417 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : term270 A f) (h6 : @SUBSET A s s) : (term268 A f) = (term412 A s f).
Proof. exact (prop_ext (fun h7 : term268 A f => @lem3781412 A f s h1 h2 h3 h4 h5 h6) (fun h7 : term412 A s f => @lem3771428 A f h1)). Qed.
Lemma lem3781418 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : term270 A f) (h6 : @SUBSET A s s) : term412 A s f.
Proof. exact (EQ_MP (@lem3781417 A f s h1 h2 h3 h4 h5 h6) (@lem3771428 A f h1)). Qed.
Lemma lem3781419 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : term270 A f) (h6 : @SUBSET A s s) : (term375 A f s) = (term412 A s f).
Proof. exact (prop_ext (fun h7 : term375 A f s => @lem3781418 A f s h1 h2 h3 h4 h5 h6) (fun h7 : term412 A s f => @lem3771429 A f s h2)). Qed.
Lemma lem3781420 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : term270 A f) (h6 : @SUBSET A s s) : term412 A s f.
Proof. exact (EQ_MP (@lem3781419 A f s h1 h2 h3 h4 h5 h6) (@lem3771429 A f s h2)). Qed.
Lemma lem3781421 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term375 A f s) (h2 : term265 A f s) (h3 : term112 A f) (h4 : term380 A s f) (h5 : term270 A f) (h6 : @SUBSET A s s) : (term268 A f) = (term412 A s f).
Proof. exact (prop_ext (fun h7 : term268 A f => @lem3781420 A f s h7 h1 h2 h3 h5 h6) (fun h7 : term412 A s f => @lem3781415 A s f h4)). Qed.
Lemma lem3781422 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term375 A f s) (h2 : term265 A f s) (h3 : term112 A f) (h4 : term380 A s f) (h5 : term270 A f) (h6 : @SUBSET A s s) : term412 A s f.
Proof. exact (EQ_MP (@lem3781421 A f s h1 h2 h3 h4 h5 h6) (@lem3781415 A s f h4)). Qed.
Lemma lem3781423 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) (h2 : term112 A f) (h3 : term380 A s f) (h4 : term270 A f) (h5 : @SUBSET A s s) : (term375 A f s) = (term412 A s f).
Proof. exact (prop_ext (fun h6 : term375 A f s => @lem3781422 A f s h6 h1 h2 h3 h4 h5) (fun h6 : term412 A s f => @lem3781416 A s f h3)). Qed.
Lemma lem3781424 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) (h2 : term112 A f) (h3 : term380 A s f) (h4 : term270 A f) (h5 : @SUBSET A s s) : term412 A s f.
Proof. exact (EQ_MP (@lem3781423 A f s h1 h2 h3 h4 h5) (@lem3781416 A s f h3)). Qed.
Lemma lem3781425 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term334 A f s) : term265 A f s.
Proof. exact (proj2 (@lem3771425 A f s h1)). Qed.
Lemma lem3781426 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term334 A f s) : @SUBSET A s s.
Proof. exact (proj1 (@lem3771425 A f s h1)). Qed.
Lemma lem3781427 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) (h2 : term112 A f) (h3 : term380 A s f) (h4 : term270 A f) (h5 : @SUBSET A s s) : (term265 A f s) = (term412 A s f).
Proof. exact (prop_ext (fun h6 : term265 A f s => @lem3781424 A f s h1 h2 h3 h4 h5) (fun h6 : term412 A s f => @lem3771426 A f s h1)). Qed.
Lemma lem3781428 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) (h2 : term112 A f) (h3 : term380 A s f) (h4 : term270 A f) (h5 : @SUBSET A s s) : term412 A s f.
Proof. exact (EQ_MP (@lem3781427 A f s h1 h2 h3 h4 h5) (@lem3771426 A f s h1)). Qed.
Lemma lem3781429 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) (h2 : term112 A f) (h3 : term380 A s f) (h4 : term270 A f) (h5 : @SUBSET A s s) : (@SUBSET A s s) = (term412 A s f).
Proof. exact (prop_ext (fun h6 : @SUBSET A s s => @lem3781428 A f s h1 h2 h3 h4 h5) (fun h6 : term412 A s f => @lem3771427 A s h5)). Qed.
Lemma lem3781430 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) (h2 : term112 A f) (h3 : term380 A s f) (h4 : term270 A f) (h5 : @SUBSET A s s) : term412 A s f.
Proof. exact (EQ_MP (@lem3781429 A f s h1 h2 h3 h4 h5) (@lem3771427 A s h5)). Qed.
Lemma lem3781431 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term112 A f) (h2 : term380 A s f) (h3 : term334 A f s) (h4 : term270 A f) (h5 : @SUBSET A s s) : (term265 A f s) = (term412 A s f).
Proof. exact (prop_ext (fun h6 : term265 A f s => @lem3781430 A f s h6 h1 h2 h4 h5) (fun h6 : term412 A s f => @lem3781425 A f s h3)). Qed.
Lemma lem3781432 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term112 A f) (h2 : term380 A s f) (h3 : term334 A f s) (h4 : term270 A f) (h5 : @SUBSET A s s) : term412 A s f.
Proof. exact (EQ_MP (@lem3781431 A f s h1 h2 h3 h4 h5) (@lem3781425 A f s h3)). Qed.
Lemma lem3781433 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) (h2 : term380 A s f) (h3 : term334 A f s) (h4 : term270 A f) : (@SUBSET A s s) = (term412 A s f).
Proof. exact (prop_ext (fun h5 : @SUBSET A s s => @lem3781432 A f s h1 h2 h3 h4 h5) (fun h5 : term412 A s f => @lem3781426 A f s h3)). Qed.
Lemma lem3781434 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) (h2 : term380 A s f) (h3 : term334 A f s) (h4 : term270 A f) : term412 A s f.
Proof. exact (EQ_MP (@lem3781433 A s f h1 h2 h3 h4) (@lem3781426 A f s h3)). Qed.
Lemma lem3781435 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) (h2 : term381 A s f) (h3 : term334 A f s) (h4 : term270 A f) : (term380 A s f) = (term412 A s f).
Proof. exact (prop_ext (fun h5 : term380 A s f => @lem3781434 A s f h1 h5 h3 h4) (fun h5 : term412 A s f => @lem3781413 A s f h2)). Qed.
Lemma lem3781436 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) (h2 : term381 A s f) (h3 : term334 A f s) (h4 : term270 A f) : term412 A s f.
Proof. exact (EQ_MP (@lem3781435 A s f h1 h2 h3 h4) (@lem3781413 A s f h2)). Qed.
Lemma lem3781437 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) (h2 : term381 A s f) (h3 : term270 A f) : (term334 A f s) = (term412 A s f).
Proof. exact (prop_ext (fun h4 : term334 A f s => @lem3781436 A s f h1 h2 h4 h3) (fun h4 : term412 A s f => @lem3781414 A s f h2)). Qed.
Lemma lem3781438 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) (h2 : term381 A s f) (h3 : term270 A f) : term412 A s f.
Proof. exact (EQ_MP (@lem3781437 A s f h1 h2 h3) (@lem3781414 A s f h2)). Qed.
Lemma lem3781439 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) (h2 : term270 A f) : term421 A s f.
Proof. exact (fun h0 : term381 A s f => @lem3781438 A s f h1 h0 h2). Qed.
Lemma lem3781440 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) : term422 A s f.
Proof. exact (fun h0 : term270 A f => @lem3781439 A s f h1 h0). Qed.
Lemma lem3781441 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) : term385 A s f.
Proof. exact (EQ_MP (@lem3771421 A s f h1) (@lem3781440 A s f h1)). Qed.
Lemma lem3781442 {A : Type'} (s : A -> Prop) (f : type686 A) : term385 A s f.
Proof. exact (or_elim (@lem3769777 A f) (fun h0 : f = (@EMPTY (A -> Prop)) => @lem3771284 A s f h0) (fun h0 : term112 A f => @lem3781441 A s f h0)). Qed.
Lemma lem3781447 {A : Type'} (s : A -> Prop) : term387 A s.
Proof. exact (fun f : type686 A => @lem3781442 A s f). Qed.
Lemma lem3781452 {A : Type'} : term389 A.
Proof. exact (fun s : A -> Prop => @lem3781447 A s). Qed.
Lemma lem3781453 {A : Type'} : term353 A.
Proof. exact (EQ_MP (@lem3770981 A) (@lem3781452 A)). Qed.
Lemma lem3781454 {A : Type'} : term215 A.
Proof. exact (EQ_MP (@lem3770775 A) (@lem3781453 A)). Qed.
Lemma lem3781455 {A : Type'} : term191 A.
Proof. exact (@lem3770060 A (@lem3781454 A)). Qed.
Lemma lem3781456 {A : Type'} : term190 A.
Proof. exact (EQ_MP (@lem3770031 A) (@lem3781455 A)). Qed.
