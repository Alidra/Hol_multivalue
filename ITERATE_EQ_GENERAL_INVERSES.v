Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_EQ_GENERAL_INVERSES_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import ITERATE_EQ_GENERAL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18393_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Lemma lem5997014 {A B C : Type'} (op : type1400 C) : term0 A B C op.
Proof. exact (@lem5997003 A B C op). Qed.
Lemma lem5997015 {A B C : Type'} (op : type1400 C) : (term0 A B C op) = (term1 A B C op).
Proof. exact (eq_refl (term0 A B C op)). Qed.
Lemma lem5997017 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem5997018 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term2 A B C s t k g h f) : term2 A B C s t k g h f.
Proof. exact (h1). Qed.
Lemma lem5997019 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term3 A B C s t k g h f.
Proof. exact (h1). Qed.
Lemma lem5997020 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term4 A B t s h k.
Proof. exact (h1). Qed.
Lemma lem5997026 {A B C : Type'} (op : type1400 C) : term1 A B C op.
Proof. exact (EQ_MP (@lem5997015 A B C op) (@lem5997014 A B C op)). Qed.
Lemma lem5997027 {A B C : Type'} (op : type1400 C) : term1 A B C op.
Proof. exact (@lem5997026 A B C op). Qed.
Lemma lem5997028 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term5 A B C op.
Proof. exact (@lem5997027 A B C op (@lem5997017 C op h1)). Qed.
Lemma lem5997029 {A B C : Type'} (op : type1400 C) (h1 : term5 A B C op) : term5 A B C op.
Proof. exact (h1). Qed.
Lemma lem5997030 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (h1 : term5 A B C op) : term6 A B C op s.
Proof. exact (@lem5997029 A B C op h1 s). Qed.
Lemma lem5997031 {A B C : Type'} (s : A -> Prop) (op : type1400 C) : (term6 A B C op s) = (term7 A B C s op).
Proof. exact (eq_refl (term6 A B C op s)). Qed.
Lemma lem5997032 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (h1 : term5 A B C op) : term7 A B C s op.
Proof. exact (EQ_MP (@lem5997031 A B C s op) (@lem5997030 A B C s op h1)). Qed.
Lemma lem5997033 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (op : type1400 C) (h1 : term5 A B C op) : term8 A B C s op t.
Proof. exact (@lem5997032 A B C s op h1 t). Qed.
Lemma lem5997034 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (t : B -> Prop) : (term8 A B C s op t) = (term9 A B C s op t).
Proof. exact (eq_refl (term8 A B C s op t)). Qed.
Lemma lem5997035 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (op : type1400 C) (h1 : term5 A B C op) : term9 A B C s op t.
Proof. exact (EQ_MP (@lem5997034 A B C s op t) (@lem5997033 A B C s t op h1)). Qed.
Lemma lem5997036 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> C) (op : type1400 C) (h1 : term5 A B C op) : term10 A B C s op t f.
Proof. exact (@lem5997035 A B C s t op h1 f). Qed.
Lemma lem5997037 {A B C : Type'} (s : A -> Prop) (f : A -> C) (op : type1400 C) (t : B -> Prop) : (term10 A B C s op t f) = (term11 A B C s f op t).
Proof. exact (eq_refl (term10 A B C s op t f)). Qed.
Lemma lem5997038 {A B C : Type'} (s : A -> Prop) (f : A -> C) (t : B -> Prop) (op : type1400 C) (h1 : term5 A B C op) : term11 A B C s f op t.
Proof. exact (EQ_MP (@lem5997037 A B C s f op t) (@lem5997036 A B C s t f op h1)). Qed.
Lemma lem5997039 {A B C : Type'} (s : A -> Prop) (f : A -> C) (t : B -> Prop) (g : B -> C) (op : type1400 C) (h1 : term5 A B C op) : term12 A B C s f op t g.
Proof. exact (@lem5997038 A B C s f t op h1 g). Qed.
Lemma lem5997040 {A B C : Type'} (s : A -> Prop) (f : A -> C) (op : type1400 C) (t : B -> Prop) (g : B -> C) : (term12 A B C s f op t g) = (term13 A B C s f op t g).
Proof. exact (eq_refl (term12 A B C s f op t g)). Qed.
Lemma lem5997041 {A B C : Type'} (s : A -> Prop) (f : A -> C) (t : B -> Prop) (g : B -> C) (op : type1400 C) (h1 : term5 A B C op) : term13 A B C s f op t g.
Proof. exact (EQ_MP (@lem5997040 A B C s f op t g) (@lem5997039 A B C s f t g op h1)). Qed.
Lemma lem5997042 {A B C : Type'} (s : A -> Prop) (f : A -> C) (t : B -> Prop) (g : B -> C) (h : A -> B) (op : type1400 C) (h1 : term5 A B C op) : term14 A B C s f op t g h.
Proof. exact (@lem5997041 A B C s f t g op h1 h). Qed.
Lemma lem5997043 {A B C : Type'} (h : A -> B) (s : A -> Prop) (f : A -> C) (op : type1400 C) (t : B -> Prop) (g : B -> C) : (term14 A B C s f op t g h) = (term15 A B C h s f op t g).
Proof. exact (eq_refl (term14 A B C s f op t g h)). Qed.
Lemma lem5997044 {A B C : Type'} (h : A -> B) (s : A -> Prop) (f : A -> C) (t : B -> Prop) (g : B -> C) (op : type1400 C) (h1 : term5 A B C op) : term15 A B C h s f op t g.
Proof. exact (EQ_MP (@lem5997043 A B C h s f op t g) (@lem5997042 A B C s f t g h op h1)). Qed.
Lemma lem5997045 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term16 A B C s t g h f) : term16 A B C s t g h f.
Proof. exact (h1). Qed.
Lemma lem5997046 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term5 A B C op) (h2 : term16 A B C s t g h f) : (@iterate C A op s f) = (@iterate C B op t g).
Proof. exact (@lem5997044 A B C h s f t g op h1 (@lem5997045 A B C s t g h f h2)). Qed.
Lemma lem5997047 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term16 A B C s t g h f) : term17 A B C s f op t g.
Proof. exact (fun h0 : term5 A B C op => @lem5997046 A B C op s t g h f h0 h1). Qed.
Lemma lem5997048 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> C) (h1 : term18 A B C s t g f) : term18 A B C s t g f.
Proof. exact (h1). Qed.
Lemma lem5997049 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> C) (h1 : term18 A B C s t g f) : term17 A B C s f op t g.
Proof. exact (ex_elim (@lem5997048 A B C s t g f h1) (fun h : A -> B => fun h0 : term19 A B C s t g f h => @lem5997047 A B C op s t g h f h0)). Qed.
Lemma lem5997050 {A B C : Type'} (op : type1400 C) (h1 : term5 A B C op) : term5 A B C op.
Proof. exact (h1). Qed.
Lemma lem5997051 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> C) (h1 : term5 A B C op) (h2 : term18 A B C s t g f) : (@iterate C A op s f) = (@iterate C B op t g).
Proof. exact (@lem5997049 A B C op s t g f h2 (@lem5997050 A B C op h1)). Qed.
Lemma lem5997052 {A B C : Type'} (s : A -> Prop) (f : A -> C) (t : B -> Prop) (g : B -> C) (op : type1400 C) (h1 : term5 A B C op) : term20 A B C s f op t g.
Proof. exact (fun h0 : term18 A B C s t g f => @lem5997051 A B C op s t g f h1 h0). Qed.
Lemma lem5997053 {A B C : Type'} (s : A -> Prop) (f : A -> C) (t : B -> Prop) (op : type1400 C) (h1 : term5 A B C op) : term21 A B C s f op t.
Proof. exact (fun g : B -> C => @lem5997052 A B C s f t g op h1). Qed.
Lemma lem5997054 {A B C : Type'} (s : A -> Prop) (f : A -> C) (op : type1400 C) (h1 : term5 A B C op) : term22 A B C s f op.
Proof. exact (fun t : B -> Prop => @lem5997053 A B C s f t op h1). Qed.
Lemma lem5997055 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (h1 : term5 A B C op) : term23 A B C s op.
Proof. exact (fun f : A -> C => @lem5997054 A B C s f op h1). Qed.
Lemma lem5997056 {A B C : Type'} (op : type1400 C) (h1 : term5 A B C op) : term24 A B C op.
Proof. exact (fun s : A -> Prop => @lem5997055 A B C s op h1). Qed.
Lemma lem5997057 {A B C : Type'} (op : type1400 C) : term25 A B C op.
Proof. exact (fun h0 : term5 A B C op => @lem5997056 A B C op h0). Qed.
Lemma lem5997058 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term24 A B C op.
Proof. exact (@lem5997057 A B C op (@lem5997028 A B C op h1)). Qed.
Lemma lem5997059 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term26 A B C op s.
Proof. exact (@lem5997058 A B C op h1 s). Qed.
Lemma lem5997060 {A B C : Type'} (s : A -> Prop) (op : type1400 C) : (term26 A B C op s) = (term23 A B C s op).
Proof. exact (eq_refl (term26 A B C op s)). Qed.
Lemma lem5997061 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term23 A B C s op.
Proof. exact (EQ_MP (@lem5997060 A B C s op) (@lem5997059 A B C s op h1)). Qed.
Lemma lem5997062 {A B C : Type'} (s : A -> Prop) (f : A -> C) (op : type1400 C) (h1 : @monoidal C op) : term27 A B C s op f.
Proof. exact (@lem5997061 A B C s op h1 f). Qed.
Lemma lem5997063 {A B C : Type'} (s : A -> Prop) (f : A -> C) (op : type1400 C) : (term27 A B C s op f) = (term22 A B C s f op).
Proof. exact (eq_refl (term27 A B C s op f)). Qed.
Lemma lem5997064 {A B C : Type'} (s : A -> Prop) (f : A -> C) (op : type1400 C) (h1 : @monoidal C op) : term22 A B C s f op.
Proof. exact (EQ_MP (@lem5997063 A B C s f op) (@lem5997062 A B C s f op h1)). Qed.
Lemma lem5997065 {A B C : Type'} (s : A -> Prop) (f : A -> C) (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term28 A B C s f op t.
Proof. exact (@lem5997064 A B C s f op h1 t). Qed.
Lemma lem5997066 {A B C : Type'} (s : A -> Prop) (f : A -> C) (op : type1400 C) (t : B -> Prop) : (term28 A B C s f op t) = (term21 A B C s f op t).
Proof. exact (eq_refl (term28 A B C s f op t)). Qed.
Lemma lem5997067 {A B C : Type'} (s : A -> Prop) (f : A -> C) (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term21 A B C s f op t.
Proof. exact (EQ_MP (@lem5997066 A B C s f op t) (@lem5997065 A B C s f t op h1)). Qed.
Lemma lem5997068 {A B C : Type'} (s : A -> Prop) (f : A -> C) (t : B -> Prop) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : term29 A B C s f op t g.
Proof. exact (@lem5997067 A B C s f t op h1 g). Qed.
Lemma lem5997069 {A B C : Type'} (s : A -> Prop) (f : A -> C) (op : type1400 C) (t : B -> Prop) (g : B -> C) : (term29 A B C s f op t g) = (term20 A B C s f op t g).
Proof. exact (eq_refl (term29 A B C s f op t g)). Qed.
Lemma lem5997072 {A B C : Type'} (s : A -> Prop) (f : A -> C) (t : B -> Prop) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : term20 A B C s f op t g.
Proof. exact (EQ_MP (@lem5997069 A B C s f op t g) (@lem5997068 A B C s f t g op h1)). Qed.
Lemma lem5997073 {A B C : Type'} (s : A -> Prop) (f : A -> C) (t : B -> Prop) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : term20 A B C s f op t g.
Proof. exact (@lem5997072 A B C s f t g op h1). Qed.
Lemma lem5997075 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5997076 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term16 A B C s t g h f) = (term31 A B C s t g h f).
Proof. exact (@lem5997075 (term16 A B C s t g h f)). Qed.
Lemma lem5997077 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term31 A B C s t g h f) = (term16 A B C s t g h f).
Proof. exact (SYM (@lem5997076 A B C s t g h f)). Qed.
Lemma lem5997078 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term32 A B C s t g h f) : term32 A B C s t g h f.
Proof. exact (h1). Qed.
Lemma lem5997081 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term33 A B C k s t g h f) : term33 A B C k s t g h f.
Proof. exact (h1). Qed.
Lemma lem5997082 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : term34 A B C k s t g h f.
Proof. exact (fun h0 : term33 A B C k s t g h f => @lem5997081 A B C k s t g h f h0). Qed.
Lemma lem5997083 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term34 A B C k s t g h f) : term34 A B C k s t g h f.
Proof. exact (h1). Qed.
Lemma lem5997084 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term33 A B C k s t g h f) : term33 A B C k s t g h f.
Proof. exact (h1). Qed.
Lemma lem5997085 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term33 A B C k s t g h f) (h2 : term34 A B C k s t g h f) : term33 A B C k s t g h f.
Proof. exact (@lem5997083 A B C k s t g h f h2 (@lem5997084 A B C k s t g h f h1)). Qed.
Lemma lem5997086 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term33 A B C k s t g h f) : term35 A B C k s t g h f.
Proof. exact (fun h0 : term34 A B C k s t g h f => @lem5997085 A B C k s t g h f h1 h0). Qed.
Lemma lem5997087 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term34 A B C k s t g h f) : term34 A B C k s t g h f.
Proof. exact (h1). Qed.
Lemma lem5997088 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term33 A B C k s t g h f) (h2 : term34 A B C k s t g h f) : term33 A B C k s t g h f.
Proof. exact (@lem5997086 A B C k s t g h f h1 (@lem5997087 A B C k s t g h f h2)). Qed.
Lemma lem5997089 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term34 A B C k s t g h f) : term34 A B C k s t g h f.
Proof. exact (fun h0 : term33 A B C k s t g h f => @lem5997088 A B C k s t g h f h0 h1). Qed.
Lemma lem5997090 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : term36 A B C k s t g h f.
Proof. exact (fun h0 : term34 A B C k s t g h f => @lem5997089 A B C k s t g h f h0). Qed.
Lemma lem5997093 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : term34 A B C k s t g h f.
Proof. exact (@lem5997090 A B C k s t g h f (@lem5997082 A B C k s t g h f)). Qed.
Lemma lem5997094 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : term34 A B C k s t g h f.
Proof. exact (@lem5997093 A B C k s t g h f). Qed.
Lemma lem5997142 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5997143 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term31 A B C s t g h f) = (term37 A B C s t g h f).
Proof. exact (@lem5997142 (term32 A B C s t g h f)). Qed.
Lemma lem5997145 (t : Prop) : (term38 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5997146 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term37 A B C s t g h f) = (term16 A B C s t g h f).
Proof. exact (@lem5997145 (term16 A B C s t g h f)). Qed.
Lemma lem5997149 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term31 A B C s t g h f) = (term16 A B C s t g h f).
Proof. exact (TRANS (@lem5997143 A B C s t g h f) (@lem5997146 A B C s t g h f)). Qed.
Lemma lem5997166 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) : (term39 A B C s t k g h f) = (term39 A B C s t k g h f).
Proof. exact (eq_refl (term39 A B C s t k g h f)). Qed.
Lemma lem5997167 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term40 A B C k s t g h f) = (term41 A B C k s t g h f).
Proof. exact (MK_COMB (@lem5997166 A B C s t k g h f) (@lem5997149 A B C s t g h f)). Qed.
Lemma lem5997170 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) : (term42 A B t s h k) = (term42 A B t s h k).
Proof. exact (eq_refl (term42 A B t s h k)). Qed.
Lemma lem5997171 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term33 A B C k s t g h f) = (term43 A B C k s t g h f).
Proof. exact (MK_COMB (@lem5997170 A B t s h k) (@lem5997167 A B C k s t g h f)). Qed.
Lemma lem5997174 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term44 A B C s t g h f) = (term45 A B C s t g h f).
Proof. exact (fun_ext (fun k : B -> A => @lem5997171 A B C k s t g h f)). Qed.
Lemma lem5997175 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5997176 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term46 A B C s t g h f) = (term47 A B C s t g h f).
Proof. exact (MK_COMB (@lem5997175 A B) (@lem5997174 A B C s t g h f)). Qed.
Lemma lem5997181 {A B C : Type'} (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term48 A B C t g h f) = (term49 A B C t g h f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5997176 A B C s t g h f)). Qed.
Lemma lem5997182 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5997183 {A B C : Type'} (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term50 A B C t g h f) = (term51 A B C t g h f).
Proof. exact (MK_COMB (@lem5997182 A) (@lem5997181 A B C t g h f)). Qed.
Lemma lem5997188 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) : (term52 A B C g h f) = (term53 A B C g h f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5997183 A B C t g h f)). Qed.
Lemma lem5997189 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5997190 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) : (term54 A B C g h f) = (term55 A B C g h f).
Proof. exact (MK_COMB (@lem5997189 B) (@lem5997188 A B C g h f)). Qed.
Lemma lem5997195 {A B C : Type'} (h : A -> B) (f : A -> C) : (term56 A B C h f) = (term57 A B C h f).
Proof. exact (fun_ext (fun g : B -> C => @lem5997190 A B C g h f)). Qed.
Lemma lem5997196 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem5997197 {A B C : Type'} (h : A -> B) (f : A -> C) : (term58 A B C h f) = (term59 A B C h f).
Proof. exact (MK_COMB (@lem5997196 B C) (@lem5997195 A B C h f)). Qed.
Lemma lem5997202 {A B C : Type'} (f : A -> C) : (term60 A B C f) = (term61 A B C f).
Proof. exact (fun_ext (fun h : A -> B => @lem5997197 A B C h f)). Qed.
Lemma lem5997203 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5997204 {A B C : Type'} (f : A -> C) : (term62 A B C f) = (term63 A B C f).
Proof. exact (MK_COMB (@lem5997203 A B) (@lem5997202 A B C f)). Qed.
Lemma lem5997209 {A B C : Type'} : (term64 A B C) = (term65 A B C).
Proof. exact (fun_ext (fun f : A -> C => @lem5997204 A B C f)). Qed.
Lemma lem5997210 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5997219 {A B C : Type'} : (term66 A B C) = (term67 A B C).
Proof. exact (MK_COMB (@lem5997210 A C) (@lem5997209 A B C)). Qed.
Lemma lem5997228 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term68 A B C s t g h f x) = (term68 A B C s t g h f x).
Proof. exact (eq_refl (term68 A B C s t g h f x)). Qed.
Lemma lem5997229 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term69 A B C s t g h f) = (term69 A B C s t g h f).
Proof. exact (fun_ext (fun x : A => @lem5997228 A B C s t g h f x)). Qed.
Lemma lem5997230 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5997231 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term70 A B C s t g h f) = (term70 A B C s t g h f).
Proof. exact (MK_COMB (@lem5997230 A) (@lem5997229 A B C s t g h f)). Qed.
Lemma lem5997236 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term71 A B s h x y) = (term71 A B s h x y).
Proof. exact (eq_refl (term71 A B s h x y)). Qed.
Lemma lem5997237 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term72 A B s h y) = (term72 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5997236 A B s h x y)). Qed.
Lemma lem5997238 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem5997239 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term73 A B s h y) = (term73 A B s h y).
Proof. exact (MK_COMB (@lem5997238 A) (@lem5997237 A B s h y)). Qed.
Lemma lem5997242 {B : Type'} (y : B) (t : B -> Prop) : (term74 B y t) = (term74 B y t).
Proof. exact (eq_refl (term74 B y t)). Qed.
Lemma lem5997243 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term75 A B t s h y) = (term75 A B t s h y).
Proof. exact (MK_COMB (@lem5997242 B y t) (@lem5997239 A B s h y)). Qed.
Lemma lem5997244 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term76 A B t s h) = (term76 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5997243 A B t s h y)). Qed.
Lemma lem5997245 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5997246 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term77 A B t s h) = (term77 A B t s h).
Proof. exact (MK_COMB (@lem5997245 B) (@lem5997244 A B t s h)). Qed.
Lemma lem5997247 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5997248 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term78 A B t s h) = (term78 A B t s h).
Proof. exact (MK_COMB (@lem5997247) (@lem5997246 A B t s h)). Qed.
Lemma lem5997249 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term16 A B C s t g h f) = (term16 A B C s t g h f).
Proof. exact (MK_COMB (@lem5997248 A B t s h) (@lem5997231 A B C s t g h f)). Qed.
Lemma lem5997262 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term79 A B C s t k g h f x) = (term79 A B C s t k g h f x).
Proof. exact (eq_refl (term79 A B C s t k g h f x)). Qed.
Lemma lem5997263 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) : (term80 A B C s t k g h f) = (term80 A B C s t k g h f).
Proof. exact (fun_ext (fun x : A => @lem5997262 A B C s t k g h f x)). Qed.
Lemma lem5997264 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5997265 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) : (term3 A B C s t k g h f) = (term3 A B C s t k g h f).
Proof. exact (MK_COMB (@lem5997264 A) (@lem5997263 A B C s t k g h f)). Qed.
Lemma lem5997266 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5997267 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) : (term39 A B C s t k g h f) = (term39 A B C s t k g h f).
Proof. exact (MK_COMB (@lem5997266) (@lem5997265 A B C s t k g h f)). Qed.
Lemma lem5997268 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term41 A B C k s t g h f) = (term41 A B C k s t g h f).
Proof. exact (MK_COMB (@lem5997267 A B C s t k g h f) (@lem5997249 A B C s t g h f)). Qed.
Lemma lem5997277 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (y : B) : (term81 A B t s h k y) = (term81 A B t s h k y).
Proof. exact (eq_refl (term81 A B t s h k y)). Qed.
Lemma lem5997278 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) : (term82 A B t s h k) = (term82 A B t s h k).
Proof. exact (fun_ext (fun y : B => @lem5997277 A B t s h k y)). Qed.
Lemma lem5997279 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5997280 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) : (term4 A B t s h k) = (term4 A B t s h k).
Proof. exact (MK_COMB (@lem5997279 B) (@lem5997278 A B t s h k)). Qed.
Lemma lem5997281 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5997282 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) : (term42 A B t s h k) = (term42 A B t s h k).
Proof. exact (MK_COMB (@lem5997281) (@lem5997280 A B t s h k)). Qed.
Lemma lem5997283 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term43 A B C k s t g h f) = (term43 A B C k s t g h f).
Proof. exact (MK_COMB (@lem5997282 A B t s h k) (@lem5997268 A B C k s t g h f)). Qed.
Lemma lem5997284 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term45 A B C s t g h f) = (term45 A B C s t g h f).
Proof. exact (fun_ext (fun k : B -> A => @lem5997283 A B C k s t g h f)). Qed.
Lemma lem5997285 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5997286 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term47 A B C s t g h f) = (term47 A B C s t g h f).
Proof. exact (MK_COMB (@lem5997285 A B) (@lem5997284 A B C s t g h f)). Qed.
Lemma lem5997287 {A B C : Type'} (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term49 A B C t g h f) = (term49 A B C t g h f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5997286 A B C s t g h f)). Qed.
Lemma lem5997288 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5997289 {A B C : Type'} (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term51 A B C t g h f) = (term51 A B C t g h f).
Proof. exact (MK_COMB (@lem5997288 A) (@lem5997287 A B C t g h f)). Qed.
Lemma lem5997290 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) : (term53 A B C g h f) = (term53 A B C g h f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5997289 A B C t g h f)). Qed.
Lemma lem5997291 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5997292 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) : (term55 A B C g h f) = (term55 A B C g h f).
Proof. exact (MK_COMB (@lem5997291 B) (@lem5997290 A B C g h f)). Qed.
Lemma lem5997293 {A B C : Type'} (h : A -> B) (f : A -> C) : (term57 A B C h f) = (term57 A B C h f).
Proof. exact (fun_ext (fun g : B -> C => @lem5997292 A B C g h f)). Qed.
Lemma lem5997294 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem5997295 {A B C : Type'} (h : A -> B) (f : A -> C) : (term59 A B C h f) = (term59 A B C h f).
Proof. exact (MK_COMB (@lem5997294 B C) (@lem5997293 A B C h f)). Qed.
Lemma lem5997296 {A B C : Type'} (f : A -> C) : (term61 A B C f) = (term61 A B C f).
Proof. exact (fun_ext (fun h : A -> B => @lem5997295 A B C h f)). Qed.
Lemma lem5997297 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5997298 {A B C : Type'} (f : A -> C) : (term63 A B C f) = (term63 A B C f).
Proof. exact (MK_COMB (@lem5997297 A B) (@lem5997296 A B C f)). Qed.
Lemma lem5997299 {A B C : Type'} : (term65 A B C) = (term65 A B C).
Proof. exact (fun_ext (fun f : A -> C => @lem5997298 A B C f)). Qed.
Lemma lem5997300 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5997301 {A B C : Type'} : (term67 A B C) = (term67 A B C).
Proof. exact (MK_COMB (@lem5997300 A C) (@lem5997299 A B C)). Qed.
Lemma lem5997388 {A B C : Type'} : (term66 A B C) = (term67 A B C).
Proof. exact (TRANS (@lem5997219 A B C) (@lem5997301 A B C)). Qed.
Lemma lem5997389 {A B C : Type'} : (term67 A B C) = (term66 A B C).
Proof. exact (SYM (@lem5997388 A B C)). Qed.
Lemma lem5997390 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term4 A B t s h k.
Proof. exact (h1). Qed.
Lemma lem5997391 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term3 A B C s t k g h f.
Proof. exact (h1). Qed.
Lemma lem5997393 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5997394 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term16 A B C s t g h f) = (term31 A B C s t g h f).
Proof. exact (@lem5997393 (term16 A B C s t g h f)). Qed.
Lemma lem5997395 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term31 A B C s t g h f) = (term16 A B C s t g h f).
Proof. exact (SYM (@lem5997394 A B C s t g h f)). Qed.
Lemma lem5997396 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term32 A B C s t g h f) : term32 A B C s t g h f.
Proof. exact (h1). Qed.
Lemma lem5997407 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (y : B) : (term81 A B t s h k y) = (term83 A B t s h k y).
Proof. exact (@lem17265 (@IN B y t) (term84 A B s h k y)). Qed.
Lemma lem5997408 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) : (term82 A B t s h k) = (term85 A B t s h k).
Proof. exact (fun_ext (fun y : B => @lem5997407 A B t s h k y)). Qed.
Lemma lem5997409 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5997462 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) : (term4 A B t s h k) = (term86 A B t s h k).
Proof. exact (MK_COMB (@lem5997409 B) (@lem5997408 A B t s h k)). Qed.
Lemma lem5997463 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term86 A B t s h k.
Proof. exact (EQ_MP (@lem5997462 A B t s h k) (@lem5997390 A B t s h k h1)). Qed.
Lemma lem5997478 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term79 A B C s t k g h f x) = (term87 A B C s t k g h f x).
Proof. exact (@lem17265 (@IN A x s) (term88 A B C t k g h f x)). Qed.
Lemma lem5997479 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) : (term80 A B C s t k g h f) = (term89 A B C s t k g h f).
Proof. exact (fun_ext (fun x : A => @lem5997478 A B C s t k g h f x)). Qed.
Lemma lem5997480 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5997533 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) : (term3 A B C s t k g h f) = (term90 A B C s t k g h f).
Proof. exact (MK_COMB (@lem5997480 A) (@lem5997479 A B C s t k g h f)). Qed.
Lemma lem5997534 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term90 A B C s t k g h f.
Proof. exact (EQ_MP (@lem5997533 A B C s t k g h f) (@lem5997391 A B C s t k g h f h1)). Qed.
Lemma lem5997544 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term91 A B s h x y) = (term92 A B s h x y).
Proof. exact (@lem17045 (@IN A x s) ((h x) = y)). Qed.
Lemma lem5997547 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term71 A B s h x y) = (term71 A B s h x y).
Proof. exact (eq_refl (term71 A B s h x y)). Qed.
Lemma lem5997548 {A : Type'} (x' : A) (x : A) : (term93 A x' x) = (term93 A x' x).
Proof. exact (eq_refl (term93 A x' x)). Qed.
Lemma lem5997550 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term94 A B s h y x) = (term71 A B s h x y).
Proof. exact (eq_refl (term94 A B s h y x)). Qed.
Lemma lem5997551 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term94 A B s h y x') = (term71 A B s h x' y).
Proof. exact (eq_refl (term94 A B s h y x')). Qed.
Lemma lem5997552 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term71 A B s h x' y) = (term71 A B s h x' y).
Proof. exact (@lem5997547 A B s h x' y). Qed.
Lemma lem5997553 {A : Type'} (P : A -> Prop) : (term95 A P) = (term96 A P).
Proof. exact (@lem18393 A P). Qed.
Lemma lem5997554 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term97 A B s h y) = (term98 A B s h y).
Proof. exact (@lem5997553 A (term72 A B s h y)). Qed.
Lemma lem5997555 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term94 A B s h y x') = (term71 A B s h x' y).
Proof. exact (TRANS (@lem5997551 A B s h x' y) (@lem5997552 A B s h x' y)). Qed.
Lemma lem5997556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5997557 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term99 A B s h y x') = (term100 A B s h x' y).
Proof. exact (MK_COMB (@lem5997556) (@lem5997555 A B s h x' y)). Qed.
Lemma lem5997558 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term101 A B s h y x' x) = (term102 A B s h y x' x).
Proof. exact (MK_COMB (@lem5997557 A B s h x' y) (@lem5997548 A x' x)). Qed.
Lemma lem5997559 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term94 A B s h y x) = (term71 A B s h x y).
Proof. exact (eq_refl (term94 A B s h y x)). Qed.
Lemma lem5997560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5997561 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term99 A B s h y x) = (term100 A B s h x y).
Proof. exact (MK_COMB (@lem5997560) (@lem5997559 A B s h x y)). Qed.
Lemma lem5997562 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term103 A B s h y x' x) = (term104 A B s h y x' x).
Proof. exact (MK_COMB (@lem5997561 A B s h x y) (@lem5997558 A B s h y x' x)). Qed.
Lemma lem5997563 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term105 A B s h y x) = (term106 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5997562 A B s h y x' x)). Qed.
Lemma lem5997564 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5997565 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term107 A B s h y x) = (term108 A B s h y x).
Proof. exact (MK_COMB (@lem5997564 A) (@lem5997563 A B s h y x)). Qed.
Lemma lem5997566 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term109 A B s h y) = (term110 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5997565 A B s h y x)). Qed.
Lemma lem5997567 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5997568 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term111 A B s h y) = (term112 A B s h y).
Proof. exact (MK_COMB (@lem5997567 A) (@lem5997566 A B s h y)). Qed.
Lemma lem5997569 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5997570 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term113 A B s h y x) = (term91 A B s h x y).
Proof. exact (MK_COMB (@lem5997569) (@lem5997550 A B s h x y)). Qed.
Lemma lem5997571 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term113 A B s h y x) = (term92 A B s h x y).
Proof. exact (TRANS (@lem5997570 A B s h x y) (@lem5997544 A B s h x y)). Qed.
Lemma lem5997572 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term114 A B s h y) = (term115 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5997571 A B s h x y)). Qed.
Lemma lem5997573 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5997574 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term116 A B s h y) = (term117 A B s h y).
Proof. exact (MK_COMB (@lem5997573 A) (@lem5997572 A B s h y)). Qed.
Lemma lem5997575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5997576 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term118 A B s h y) = (term119 A B s h y).
Proof. exact (MK_COMB (@lem5997575) (@lem5997574 A B s h y)). Qed.
Lemma lem5997577 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term98 A B s h y) = (term120 A B s h y).
Proof. exact (MK_COMB (@lem5997576 A B s h y) (@lem5997568 A B s h y)). Qed.
Lemma lem5997578 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term97 A B s h y) = (term120 A B s h y).
Proof. exact (TRANS (@lem5997554 A B s h y) (@lem5997577 A B s h y)). Qed.
Lemma lem5997580 {B : Type'} (y : B) (t : B -> Prop) : (term121 B y t) = (term121 B y t).
Proof. exact (eq_refl (term121 B y t)). Qed.
Lemma lem5997581 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term122 A B t s h y) = (term123 A B t s h y).
Proof. exact (MK_COMB (@lem5997580 B y t) (@lem5997578 A B s h y)). Qed.
Lemma lem5997582 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term124 A B t s h y) = (term122 A B t s h y).
Proof. exact (@lem17362 (@IN B y t) (term73 A B s h y)). Qed.
Lemma lem5997583 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term124 A B t s h y) = (term123 A B t s h y).
Proof. exact (TRANS (@lem5997582 A B t s h y) (@lem5997581 A B t s h y)). Qed.
Lemma lem5997584 {B : Type'} (P : B -> Prop) : (term125 B P) = (term126 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5997585 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term127 A B t s h) = (term128 A B t s h).
Proof. exact (@lem5997584 B (term76 A B t s h)). Qed.
Lemma lem5997586 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term129 A B t s h y) = (term75 A B t s h y).
Proof. exact (eq_refl (term129 A B t s h y)). Qed.
Lemma lem5997587 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5997588 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term130 A B t s h y) = (term124 A B t s h y).
Proof. exact (MK_COMB (@lem5997587) (@lem5997586 A B t s h y)). Qed.
Lemma lem5997589 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term130 A B t s h y) = (term123 A B t s h y).
Proof. exact (TRANS (@lem5997588 A B t s h y) (@lem5997583 A B t s h y)). Qed.
Lemma lem5997590 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term131 A B t s h) = (term132 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5997589 A B t s h y)). Qed.
Lemma lem5997591 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5997592 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term128 A B t s h) = (term133 A B t s h).
Proof. exact (MK_COMB (@lem5997591 B) (@lem5997590 A B t s h)). Qed.
Lemma lem5997593 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term127 A B t s h) = (term133 A B t s h).
Proof. exact (TRANS (@lem5997585 A B t s h) (@lem5997592 A B t s h)). Qed.
Lemma lem5997601 {A B C : Type'} (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term134 A B C t g h f x) = (term135 A B C t g h f x).
Proof. exact (@lem17045 (term136 A B h x t) ((term137 A B C g h x) = (f x))). Qed.
Lemma lem5997603 {A : Type'} (x : A) (s : A -> Prop) : (term121 A x s) = (term121 A x s).
Proof. exact (eq_refl (term121 A x s)). Qed.
Lemma lem5997604 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term138 A B C s t g h f x) = (term139 A B C s t g h f x).
Proof. exact (MK_COMB (@lem5997603 A x s) (@lem5997601 A B C t g h f x)). Qed.
Lemma lem5997605 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term140 A B C s t g h f x) = (term138 A B C s t g h f x).
Proof. exact (@lem17362 (@IN A x s) (term141 A B C t g h f x)). Qed.
Lemma lem5997606 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term140 A B C s t g h f x) = (term139 A B C s t g h f x).
Proof. exact (TRANS (@lem5997605 A B C s t g h f x) (@lem5997604 A B C s t g h f x)). Qed.
Lemma lem5997607 {A : Type'} (P : A -> Prop) : (term125 A P) = (term126 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5997608 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term142 A B C s t g h f) = (term143 A B C s t g h f).
Proof. exact (@lem5997607 A (term69 A B C s t g h f)). Qed.
Lemma lem5997609 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term144 A B C s t g h f x) = (term68 A B C s t g h f x).
Proof. exact (eq_refl (term144 A B C s t g h f x)). Qed.
Lemma lem5997610 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5997611 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term145 A B C s t g h f x) = (term140 A B C s t g h f x).
Proof. exact (MK_COMB (@lem5997610) (@lem5997609 A B C s t g h f x)). Qed.
Lemma lem5997612 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term145 A B C s t g h f x) = (term139 A B C s t g h f x).
Proof. exact (TRANS (@lem5997611 A B C s t g h f x) (@lem5997606 A B C s t g h f x)). Qed.
Lemma lem5997613 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term146 A B C s t g h f) = (term147 A B C s t g h f).
Proof. exact (fun_ext (fun x : A => @lem5997612 A B C s t g h f x)). Qed.
Lemma lem5997614 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5997615 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term143 A B C s t g h f) = (term148 A B C s t g h f).
Proof. exact (MK_COMB (@lem5997614 A) (@lem5997613 A B C s t g h f)). Qed.
Lemma lem5997616 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term142 A B C s t g h f) = (term148 A B C s t g h f).
Proof. exact (TRANS (@lem5997608 A B C s t g h f) (@lem5997615 A B C s t g h f)). Qed.
Lemma lem5997617 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5997618 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term149 A B t s h) = (term150 A B t s h).
Proof. exact (MK_COMB (@lem5997617) (@lem5997593 A B t s h)). Qed.
Lemma lem5997619 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term151 A B C s t g h f) = (term152 A B C s t g h f).
Proof. exact (MK_COMB (@lem5997618 A B t s h) (@lem5997616 A B C s t g h f)). Qed.
Lemma lem5997620 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term32 A B C s t g h f) = (term151 A B C s t g h f).
Proof. exact (@lem17045 (term77 A B t s h) (term70 A B C s t g h f)). Qed.
Lemma lem5997621 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term32 A B C s t g h f) = (term152 A B C s t g h f).
Proof. exact (TRANS (@lem5997620 A B C s t g h f) (@lem5997619 A B C s t g h f)). Qed.
Lemma lem5997723 {A : Type'} (P : Prop) (Q : A -> Prop) : (term153 A P Q) = (term154 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem5997724 {A : Type'} (P : Prop) (Q : A -> Prop) : (term153 A P Q) = (term154 A P Q).
Proof. exact (@lem5997723 A P Q). Qed.
Lemma lem5997725 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term155 A B s h y x) = (term156 A B s h y x).
Proof. exact (@lem5997724 A (term71 A B s h x y) (term157 A B s h y x)). Qed.
Lemma lem5997726 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term158 A B s h y x x') = (term102 A B s h y x' x).
Proof. exact (eq_refl (term158 A B s h y x x')). Qed.
Lemma lem5997727 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term100 A B s h x y) = (term100 A B s h x y).
Proof. exact (eq_refl (term100 A B s h x y)). Qed.
Lemma lem5997728 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term159 A B s h y x x') = (term104 A B s h y x' x).
Proof. exact (MK_COMB (@lem5997727 A B s h x y) (@lem5997726 A B s h y x' x)). Qed.
Lemma lem5997729 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term160 A B s h y x) = (term106 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5997728 A B s h y x' x)). Qed.
Lemma lem5997730 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5997731 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term155 A B s h y x) = (term108 A B s h y x).
Proof. exact (MK_COMB (@lem5997730 A) (@lem5997729 A B s h y x)). Qed.
Lemma lem5997732 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5997733 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term161 A B s h y x) = (term162 A B s h y x).
Proof. exact (MK_COMB (@lem5997732) (@lem5997731 A B s h y x)). Qed.
Lemma lem5997734 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term158 A B s h y x x') = (term102 A B s h y x' x).
Proof. exact (eq_refl (term158 A B s h y x x')). Qed.
Lemma lem5997735 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term163 A B s h y x) = (term157 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5997734 A B s h y x' x)). Qed.
Lemma lem5997736 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5997737 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term164 A B s h y x) = (term165 A B s h y x).
Proof. exact (MK_COMB (@lem5997736 A) (@lem5997735 A B s h y x)). Qed.
Lemma lem5997738 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term100 A B s h x y) = (term100 A B s h x y).
Proof. exact (eq_refl (term100 A B s h x y)). Qed.
Lemma lem5997739 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term156 A B s h y x) = (term166 A B s h y x).
Proof. exact (MK_COMB (@lem5997738 A B s h x y) (@lem5997737 A B s h y x)). Qed.
Lemma lem5997740 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : ((term155 A B s h y x) = (term156 A B s h y x)) = ((term108 A B s h y x) = (term166 A B s h y x)).
Proof. exact (MK_COMB (@lem5997733 A B s h y x) (@lem5997739 A B s h y x)). Qed.
Lemma lem5997741 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term108 A B s h y x) = (term166 A B s h y x).
Proof. exact (EQ_MP (@lem5997740 A B s h y x) (@lem5997725 A B s h y x)). Qed.
Lemma lem5997790 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term110 A B s h y) = (term167 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5997741 A B s h y x)). Qed.
Lemma lem5997791 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5997792 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term112 A B s h y) = (term168 A B s h y).
Proof. exact (MK_COMB (@lem5997791 A) (@lem5997790 A B s h y)). Qed.
Lemma lem5997841 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term119 A B s h y) = (term119 A B s h y).
Proof. exact (eq_refl (term119 A B s h y)). Qed.
Lemma lem5997842 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term120 A B s h y) = (term169 A B s h y).
Proof. exact (MK_COMB (@lem5997841 A B s h y) (@lem5997792 A B s h y)). Qed.
Lemma lem5997843 {B : Type'} (y : B) (t : B -> Prop) : (term121 B y t) = (term121 B y t).
Proof. exact (eq_refl (term121 B y t)). Qed.
Lemma lem5997844 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term123 A B t s h y) = (term170 A B t s h y).
Proof. exact (MK_COMB (@lem5997843 B y t) (@lem5997842 A B s h y)). Qed.
Lemma lem5997845 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term132 A B t s h) = (term171 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5997844 A B t s h y)). Qed.
Lemma lem5997846 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5997847 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term133 A B t s h) = (term172 A B t s h).
Proof. exact (MK_COMB (@lem5997846 B) (@lem5997845 A B t s h)). Qed.
Lemma lem5997896 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5997897 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term150 A B t s h) = (term173 A B t s h).
Proof. exact (MK_COMB (@lem5997896) (@lem5997847 A B t s h)). Qed.
Lemma lem5997946 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term148 A B C s t g h f) = (term148 A B C s t g h f).
Proof. exact (eq_refl (term148 A B C s t g h f)). Qed.
Lemma lem5997947 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term152 A B C s t g h f) = (term174 A B C s t g h f).
Proof. exact (MK_COMB (@lem5997897 A B t s h) (@lem5997946 A B C s t g h f)). Qed.
Lemma lem5997949 {A : Type'} (P : Prop) (Q : A -> Prop) : (term154 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5997950 {A : Type'} (P : Prop) (Q : A -> Prop) : (term154 A P Q) = (term153 A P Q).
Proof. exact (@lem5997949 A P Q). Qed.
Lemma lem5997951 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term156 A B s h y x) = (term155 A B s h y x).
Proof. exact (@lem5997950 A (term71 A B s h x y) (term157 A B s h y x)). Qed.
Lemma lem5997952 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term158 A B s h y x x') = (term102 A B s h y x' x).
Proof. exact (eq_refl (term158 A B s h y x x')). Qed.
Lemma lem5997953 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term163 A B s h y x) = (term157 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5997952 A B s h y x' x)). Qed.
Lemma lem5997954 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5997955 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term164 A B s h y x) = (term165 A B s h y x).
Proof. exact (MK_COMB (@lem5997954 A) (@lem5997953 A B s h y x)). Qed.
Lemma lem5997956 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term100 A B s h x y) = (term100 A B s h x y).
Proof. exact (eq_refl (term100 A B s h x y)). Qed.
Lemma lem5997957 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term156 A B s h y x) = (term166 A B s h y x).
Proof. exact (MK_COMB (@lem5997956 A B s h x y) (@lem5997955 A B s h y x)). Qed.
Lemma lem5997958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5997959 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term175 A B s h y x) = (term176 A B s h y x).
Proof. exact (MK_COMB (@lem5997958) (@lem5997957 A B s h y x)). Qed.
Lemma lem5997960 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term158 A B s h y x x') = (term102 A B s h y x' x).
Proof. exact (eq_refl (term158 A B s h y x x')). Qed.
Lemma lem5997961 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term100 A B s h x y) = (term100 A B s h x y).
Proof. exact (eq_refl (term100 A B s h x y)). Qed.
Lemma lem5997962 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term159 A B s h y x x') = (term104 A B s h y x' x).
Proof. exact (MK_COMB (@lem5997961 A B s h x y) (@lem5997960 A B s h y x' x)). Qed.
Lemma lem5997963 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term160 A B s h y x) = (term106 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5997962 A B s h y x' x)). Qed.
Lemma lem5997964 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5997965 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term155 A B s h y x) = (term108 A B s h y x).
Proof. exact (MK_COMB (@lem5997964 A) (@lem5997963 A B s h y x)). Qed.
Lemma lem5997966 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : ((term156 A B s h y x) = (term155 A B s h y x)) = ((term166 A B s h y x) = (term108 A B s h y x)).
Proof. exact (MK_COMB (@lem5997959 A B s h y x) (@lem5997965 A B s h y x)). Qed.
Lemma lem5997967 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term166 A B s h y x) = (term108 A B s h y x).
Proof. exact (EQ_MP (@lem5997966 A B s h y x) (@lem5997951 A B s h y x)). Qed.
Lemma lem5997968 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term167 A B s h y) = (term110 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5997967 A B s h y x)). Qed.
Lemma lem5997969 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5997970 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term168 A B s h y) = (term112 A B s h y).
Proof. exact (MK_COMB (@lem5997969 A) (@lem5997968 A B s h y)). Qed.
Lemma lem5997971 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term119 A B s h y) = (term119 A B s h y).
Proof. exact (eq_refl (term119 A B s h y)). Qed.
Lemma lem5997972 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term169 A B s h y) = (term120 A B s h y).
Proof. exact (MK_COMB (@lem5997971 A B s h y) (@lem5997970 A B s h y)). Qed.
Lemma lem5997974 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5997975 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (@lem5997974 A P Q). Qed.
Lemma lem5997976 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term179 A B s h y) = (term180 A B s h y).
Proof. exact (@lem5997975 A (term117 A B s h y) (term110 A B s h y)). Qed.
Lemma lem5997977 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term181 A B s h y x) = (term108 A B s h y x).
Proof. exact (eq_refl (term181 A B s h y x)). Qed.
Lemma lem5997978 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term182 A B s h y) = (term110 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5997977 A B s h y x)). Qed.
Lemma lem5997979 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5997980 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term183 A B s h y) = (term112 A B s h y).
Proof. exact (MK_COMB (@lem5997979 A) (@lem5997978 A B s h y)). Qed.
Lemma lem5997981 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term119 A B s h y) = (term119 A B s h y).
Proof. exact (eq_refl (term119 A B s h y)). Qed.
Lemma lem5997982 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term179 A B s h y) = (term120 A B s h y).
Proof. exact (MK_COMB (@lem5997981 A B s h y) (@lem5997980 A B s h y)). Qed.
Lemma lem5997983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5997984 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term184 A B s h y) = (term185 A B s h y).
Proof. exact (MK_COMB (@lem5997983) (@lem5997982 A B s h y)). Qed.
Lemma lem5997985 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term181 A B s h y x) = (term108 A B s h y x).
Proof. exact (eq_refl (term181 A B s h y x)). Qed.
Lemma lem5997986 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term119 A B s h y) = (term119 A B s h y).
Proof. exact (eq_refl (term119 A B s h y)). Qed.
Lemma lem5997987 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term186 A B s h y x) = (term187 A B s h y x).
Proof. exact (MK_COMB (@lem5997986 A B s h y) (@lem5997985 A B s h y x)). Qed.
Lemma lem5997988 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term188 A B s h y) = (term189 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5997987 A B s h y x)). Qed.
Lemma lem5997989 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5997990 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term180 A B s h y) = (term190 A B s h y).
Proof. exact (MK_COMB (@lem5997989 A) (@lem5997988 A B s h y)). Qed.
Lemma lem5997991 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : ((term179 A B s h y) = (term180 A B s h y)) = ((term120 A B s h y) = (term190 A B s h y)).
Proof. exact (MK_COMB (@lem5997984 A B s h y) (@lem5997990 A B s h y)). Qed.
Lemma lem5997992 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term120 A B s h y) = (term190 A B s h y).
Proof. exact (EQ_MP (@lem5997991 A B s h y) (@lem5997976 A B s h y)). Qed.
Lemma lem5997994 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5997995 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (@lem5997994 A P Q). Qed.
Lemma lem5997996 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term191 A B s h y x) = (term192 A B s h y x).
Proof. exact (@lem5997995 A (term117 A B s h y) (term106 A B s h y x)). Qed.
Lemma lem5997997 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term193 A B s h y x x') = (term104 A B s h y x' x).
Proof. exact (eq_refl (term193 A B s h y x x')). Qed.
Lemma lem5997998 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term194 A B s h y x) = (term106 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5997997 A B s h y x' x)). Qed.
Lemma lem5997999 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5998000 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term195 A B s h y x) = (term108 A B s h y x).
Proof. exact (MK_COMB (@lem5997999 A) (@lem5997998 A B s h y x)). Qed.
Lemma lem5998001 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term119 A B s h y) = (term119 A B s h y).
Proof. exact (eq_refl (term119 A B s h y)). Qed.
Lemma lem5998002 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term191 A B s h y x) = (term187 A B s h y x).
Proof. exact (MK_COMB (@lem5998001 A B s h y) (@lem5998000 A B s h y x)). Qed.
Lemma lem5998003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5998004 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term196 A B s h y x) = (term197 A B s h y x).
Proof. exact (MK_COMB (@lem5998003) (@lem5998002 A B s h y x)). Qed.
Lemma lem5998005 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term193 A B s h y x x') = (term104 A B s h y x' x).
Proof. exact (eq_refl (term193 A B s h y x x')). Qed.
Lemma lem5998006 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term119 A B s h y) = (term119 A B s h y).
Proof. exact (eq_refl (term119 A B s h y)). Qed.
Lemma lem5998007 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term198 A B s h y x x') = (term199 A B s h y x' x).
Proof. exact (MK_COMB (@lem5998006 A B s h y) (@lem5998005 A B s h y x' x)). Qed.
Lemma lem5998008 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term200 A B s h y x) = (term201 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5998007 A B s h y x' x)). Qed.
Lemma lem5998009 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5998010 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term192 A B s h y x) = (term202 A B s h y x).
Proof. exact (MK_COMB (@lem5998009 A) (@lem5998008 A B s h y x)). Qed.
Lemma lem5998011 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : ((term191 A B s h y x) = (term192 A B s h y x)) = ((term187 A B s h y x) = (term202 A B s h y x)).
Proof. exact (MK_COMB (@lem5998004 A B s h y x) (@lem5998010 A B s h y x)). Qed.
Lemma lem5998012 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term187 A B s h y x) = (term202 A B s h y x).
Proof. exact (EQ_MP (@lem5998011 A B s h y x) (@lem5997996 A B s h y x)). Qed.
Lemma lem5998013 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term189 A B s h y) = (term203 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5998012 A B s h y x)). Qed.
Lemma lem5998014 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5998015 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term190 A B s h y) = (term204 A B s h y).
Proof. exact (MK_COMB (@lem5998014 A) (@lem5998013 A B s h y)). Qed.
Lemma lem5998016 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term120 A B s h y) = (term204 A B s h y).
Proof. exact (TRANS (@lem5997992 A B s h y) (@lem5998015 A B s h y)). Qed.
Lemma lem5998017 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term169 A B s h y) = (term204 A B s h y).
Proof. exact (TRANS (@lem5997972 A B s h y) (@lem5998016 A B s h y)). Qed.
Lemma lem5998018 {B : Type'} (y : B) (t : B -> Prop) : (term121 B y t) = (term121 B y t).
Proof. exact (eq_refl (term121 B y t)). Qed.
Lemma lem5998019 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term170 A B t s h y) = (term205 A B t s h y).
Proof. exact (MK_COMB (@lem5998018 B y t) (@lem5998017 A B s h y)). Qed.
Lemma lem5998021 {A : Type'} (P : Prop) (Q : A -> Prop) : (term154 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5998022 {A : Type'} (P : Prop) (Q : A -> Prop) : (term154 A P Q) = (term153 A P Q).
Proof. exact (@lem5998021 A P Q). Qed.
Lemma lem5998023 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term206 A B t s h y) = (term207 A B t s h y).
Proof. exact (@lem5998022 A (@IN B y t) (term203 A B s h y)). Qed.
Lemma lem5998024 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term208 A B s h y x) = (term202 A B s h y x).
Proof. exact (eq_refl (term208 A B s h y x)). Qed.
Lemma lem5998025 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term209 A B s h y) = (term203 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5998024 A B s h y x)). Qed.
Lemma lem5998026 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5998027 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term210 A B s h y) = (term204 A B s h y).
Proof. exact (MK_COMB (@lem5998026 A) (@lem5998025 A B s h y)). Qed.
Lemma lem5998028 {B : Type'} (y : B) (t : B -> Prop) : (term121 B y t) = (term121 B y t).
Proof. exact (eq_refl (term121 B y t)). Qed.
Lemma lem5998029 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term206 A B t s h y) = (term205 A B t s h y).
Proof. exact (MK_COMB (@lem5998028 B y t) (@lem5998027 A B s h y)). Qed.
Lemma lem5998030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5998031 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term211 A B t s h y) = (term212 A B t s h y).
Proof. exact (MK_COMB (@lem5998030) (@lem5998029 A B t s h y)). Qed.
Lemma lem5998032 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term208 A B s h y x) = (term202 A B s h y x).
Proof. exact (eq_refl (term208 A B s h y x)). Qed.
Lemma lem5998033 {B : Type'} (y : B) (t : B -> Prop) : (term121 B y t) = (term121 B y t).
Proof. exact (eq_refl (term121 B y t)). Qed.
Lemma lem5998034 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term213 A B t s h y x) = (term214 A B t s h y x).
Proof. exact (MK_COMB (@lem5998033 B y t) (@lem5998032 A B s h y x)). Qed.
Lemma lem5998035 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term215 A B t s h y) = (term216 A B t s h y).
Proof. exact (fun_ext (fun x : A => @lem5998034 A B t s h y x)). Qed.
Lemma lem5998036 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5998037 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term207 A B t s h y) = (term217 A B t s h y).
Proof. exact (MK_COMB (@lem5998036 A) (@lem5998035 A B t s h y)). Qed.
Lemma lem5998038 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : ((term206 A B t s h y) = (term207 A B t s h y)) = ((term205 A B t s h y) = (term217 A B t s h y)).
Proof. exact (MK_COMB (@lem5998031 A B t s h y) (@lem5998037 A B t s h y)). Qed.
Lemma lem5998039 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term205 A B t s h y) = (term217 A B t s h y).
Proof. exact (EQ_MP (@lem5998038 A B t s h y) (@lem5998023 A B t s h y)). Qed.
Lemma lem5998041 {A : Type'} (P : Prop) (Q : A -> Prop) : (term154 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5998042 {A : Type'} (P : Prop) (Q : A -> Prop) : (term154 A P Q) = (term153 A P Q).
Proof. exact (@lem5998041 A P Q). Qed.
Lemma lem5998043 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term218 A B t s h y x) = (term219 A B t s h y x).
Proof. exact (@lem5998042 A (@IN B y t) (term201 A B s h y x)). Qed.
Lemma lem5998044 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term220 A B s h y x x') = (term199 A B s h y x' x).
Proof. exact (eq_refl (term220 A B s h y x x')). Qed.
Lemma lem5998045 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term221 A B s h y x) = (term201 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5998044 A B s h y x' x)). Qed.
Lemma lem5998046 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5998047 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term222 A B s h y x) = (term202 A B s h y x).
Proof. exact (MK_COMB (@lem5998046 A) (@lem5998045 A B s h y x)). Qed.
Lemma lem5998048 {B : Type'} (y : B) (t : B -> Prop) : (term121 B y t) = (term121 B y t).
Proof. exact (eq_refl (term121 B y t)). Qed.
Lemma lem5998049 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term218 A B t s h y x) = (term214 A B t s h y x).
Proof. exact (MK_COMB (@lem5998048 B y t) (@lem5998047 A B s h y x)). Qed.
Lemma lem5998050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5998051 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term223 A B t s h y x) = (term224 A B t s h y x).
Proof. exact (MK_COMB (@lem5998050) (@lem5998049 A B t s h y x)). Qed.
Lemma lem5998052 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term220 A B s h y x x') = (term199 A B s h y x' x).
Proof. exact (eq_refl (term220 A B s h y x x')). Qed.
Lemma lem5998053 {B : Type'} (y : B) (t : B -> Prop) : (term121 B y t) = (term121 B y t).
Proof. exact (eq_refl (term121 B y t)). Qed.
Lemma lem5998054 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term225 A B t s h y x x') = (term226 A B t s h y x' x).
Proof. exact (MK_COMB (@lem5998053 B y t) (@lem5998052 A B s h y x' x)). Qed.
Lemma lem5998055 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term227 A B t s h y x) = (term228 A B t s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5998054 A B t s h y x' x)). Qed.
Lemma lem5998056 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5998057 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term219 A B t s h y x) = (term229 A B t s h y x).
Proof. exact (MK_COMB (@lem5998056 A) (@lem5998055 A B t s h y x)). Qed.
Lemma lem5998058 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : ((term218 A B t s h y x) = (term219 A B t s h y x)) = ((term214 A B t s h y x) = (term229 A B t s h y x)).
Proof. exact (MK_COMB (@lem5998051 A B t s h y x) (@lem5998057 A B t s h y x)). Qed.
Lemma lem5998059 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term214 A B t s h y x) = (term229 A B t s h y x).
Proof. exact (EQ_MP (@lem5998058 A B t s h y x) (@lem5998043 A B t s h y x)). Qed.
Lemma lem5998060 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term216 A B t s h y) = (term230 A B t s h y).
Proof. exact (fun_ext (fun x : A => @lem5998059 A B t s h y x)). Qed.
Lemma lem5998061 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5998062 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term217 A B t s h y) = (term231 A B t s h y).
Proof. exact (MK_COMB (@lem5998061 A) (@lem5998060 A B t s h y)). Qed.
Lemma lem5998063 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term205 A B t s h y) = (term231 A B t s h y).
Proof. exact (TRANS (@lem5998039 A B t s h y) (@lem5998062 A B t s h y)). Qed.
Lemma lem5998064 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term170 A B t s h y) = (term231 A B t s h y).
Proof. exact (TRANS (@lem5998019 A B t s h y) (@lem5998063 A B t s h y)). Qed.
Lemma lem5998065 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term171 A B t s h) = (term232 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5998064 A B t s h y)). Qed.
Lemma lem5998066 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5998067 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term172 A B t s h) = (term233 A B t s h).
Proof. exact (MK_COMB (@lem5998066 B) (@lem5998065 A B t s h)). Qed.
Lemma lem5998068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5998069 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term173 A B t s h) = (term234 A B t s h).
Proof. exact (MK_COMB (@lem5998068) (@lem5998067 A B t s h)). Qed.
Lemma lem5998070 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term148 A B C s t g h f) = (term148 A B C s t g h f).
Proof. exact (eq_refl (term148 A B C s t g h f)). Qed.
Lemma lem5998071 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term174 A B C s t g h f) = (term235 A B C s t g h f).
Proof. exact (MK_COMB (@lem5998069 A B t s h) (@lem5998070 A B C s t g h f)). Qed.
Lemma lem5998075 {A : Type'} (P : A -> Prop) (Q : Prop) : (term236 A P Q) = (term237 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5998076 {B : Type'} (P : B -> Prop) (Q : Prop) : (term236 B P Q) = (term237 B P Q).
Proof. exact (@lem5998075 B P Q). Qed.
Lemma lem5998077 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term238 A B C s t g h f) = (term239 A B C s t g h f).
Proof. exact (@lem5998076 B (term232 A B t s h) (term148 A B C s t g h f)). Qed.
Lemma lem5998078 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term240 A B t s h y) = (term231 A B t s h y).
Proof. exact (eq_refl (term240 A B t s h y)). Qed.
Lemma lem5998079 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term241 A B t s h) = (term232 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5998078 A B t s h y)). Qed.
Lemma lem5998080 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5998081 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term242 A B t s h) = (term233 A B t s h).
Proof. exact (MK_COMB (@lem5998080 B) (@lem5998079 A B t s h)). Qed.
Lemma lem5998082 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5998083 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term243 A B t s h) = (term234 A B t s h).
Proof. exact (MK_COMB (@lem5998082) (@lem5998081 A B t s h)). Qed.
Lemma lem5998084 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term148 A B C s t g h f) = (term148 A B C s t g h f).
Proof. exact (eq_refl (term148 A B C s t g h f)). Qed.
Lemma lem5998085 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term238 A B C s t g h f) = (term235 A B C s t g h f).
Proof. exact (MK_COMB (@lem5998083 A B t s h) (@lem5998084 A B C s t g h f)). Qed.
Lemma lem5998086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5998087 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term244 A B C s t g h f) = (term245 A B C s t g h f).
Proof. exact (MK_COMB (@lem5998086) (@lem5998085 A B C s t g h f)). Qed.
Lemma lem5998088 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term240 A B t s h y) = (term231 A B t s h y).
Proof. exact (eq_refl (term240 A B t s h y)). Qed.
Lemma lem5998089 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5998090 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term246 A B t s h y) = (term247 A B t s h y).
Proof. exact (MK_COMB (@lem5998089) (@lem5998088 A B t s h y)). Qed.
Lemma lem5998091 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term148 A B C s t g h f) = (term148 A B C s t g h f).
Proof. exact (eq_refl (term148 A B C s t g h f)). Qed.
Lemma lem5998092 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term248 A B C y s t g h f) = (term249 A B C y s t g h f).
Proof. exact (MK_COMB (@lem5998090 A B t s h y) (@lem5998091 A B C s t g h f)). Qed.
Lemma lem5998093 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term250 A B C s t g h f) = (term251 A B C s t g h f).
Proof. exact (fun_ext (fun y : B => @lem5998092 A B C y s t g h f)). Qed.
Lemma lem5998094 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5998095 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term239 A B C s t g h f) = (term252 A B C s t g h f).
Proof. exact (MK_COMB (@lem5998094 B) (@lem5998093 A B C s t g h f)). Qed.
Lemma lem5998096 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : ((term238 A B C s t g h f) = (term239 A B C s t g h f)) = ((term235 A B C s t g h f) = (term252 A B C s t g h f)).
Proof. exact (MK_COMB (@lem5998087 A B C s t g h f) (@lem5998095 A B C s t g h f)). Qed.
Lemma lem5998097 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term235 A B C s t g h f) = (term252 A B C s t g h f).
Proof. exact (EQ_MP (@lem5998096 A B C s t g h f) (@lem5998077 A B C s t g h f)). Qed.
Lemma lem5998099 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term253 A P Q) = (term254 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5998100 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term253 A P Q) = (term254 A P Q).
Proof. exact (@lem5998099 A P Q). Qed.
Lemma lem5998101 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term255 A B C y s t g h f) = (term256 A B C y s t g h f).
Proof. exact (@lem5998100 A (term230 A B t s h y) (term147 A B C s t g h f)). Qed.
Lemma lem5998102 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term257 A B t s h y x) = (term229 A B t s h y x).
Proof. exact (eq_refl (term257 A B t s h y x)). Qed.
Lemma lem5998103 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term258 A B t s h y) = (term230 A B t s h y).
Proof. exact (fun_ext (fun x : A => @lem5998102 A B t s h y x)). Qed.
Lemma lem5998104 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5998105 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term259 A B t s h y) = (term231 A B t s h y).
Proof. exact (MK_COMB (@lem5998104 A) (@lem5998103 A B t s h y)). Qed.
Lemma lem5998106 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5998107 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term260 A B t s h y) = (term247 A B t s h y).
Proof. exact (MK_COMB (@lem5998106) (@lem5998105 A B t s h y)). Qed.
Lemma lem5998108 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term261 A B C s t g h f x) = (term139 A B C s t g h f x).
Proof. exact (eq_refl (term261 A B C s t g h f x)). Qed.
Lemma lem5998109 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term262 A B C s t g h f) = (term147 A B C s t g h f).
Proof. exact (fun_ext (fun x : A => @lem5998108 A B C s t g h f x)). Qed.
Lemma lem5998110 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5998111 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term263 A B C s t g h f) = (term148 A B C s t g h f).
Proof. exact (MK_COMB (@lem5998110 A) (@lem5998109 A B C s t g h f)). Qed.
Lemma lem5998112 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term255 A B C y s t g h f) = (term249 A B C y s t g h f).
Proof. exact (MK_COMB (@lem5998107 A B t s h y) (@lem5998111 A B C s t g h f)). Qed.
Lemma lem5998113 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5998114 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term264 A B C y s t g h f) = (term265 A B C y s t g h f).
Proof. exact (MK_COMB (@lem5998113) (@lem5998112 A B C y s t g h f)). Qed.
Lemma lem5998115 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term257 A B t s h y x) = (term229 A B t s h y x).
Proof. exact (eq_refl (term257 A B t s h y x)). Qed.
Lemma lem5998116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5998117 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term266 A B t s h y x) = (term267 A B t s h y x).
Proof. exact (MK_COMB (@lem5998116) (@lem5998115 A B t s h y x)). Qed.
Lemma lem5998118 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term261 A B C s t g h f x) = (term139 A B C s t g h f x).
Proof. exact (eq_refl (term261 A B C s t g h f x)). Qed.
Lemma lem5998119 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term268 A B C y s t g h f x) = (term269 A B C y s t g h f x).
Proof. exact (MK_COMB (@lem5998117 A B t s h y x) (@lem5998118 A B C s t g h f x)). Qed.
Lemma lem5998120 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term270 A B C y s t g h f) = (term271 A B C y s t g h f).
Proof. exact (fun_ext (fun x : A => @lem5998119 A B C y s t g h f x)). Qed.
Lemma lem5998121 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5998122 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term256 A B C y s t g h f) = (term272 A B C y s t g h f).
Proof. exact (MK_COMB (@lem5998121 A) (@lem5998120 A B C y s t g h f)). Qed.
Lemma lem5998123 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : ((term255 A B C y s t g h f) = (term256 A B C y s t g h f)) = ((term249 A B C y s t g h f) = (term272 A B C y s t g h f)).
Proof. exact (MK_COMB (@lem5998114 A B C y s t g h f) (@lem5998122 A B C y s t g h f)). Qed.
Lemma lem5998124 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term249 A B C y s t g h f) = (term272 A B C y s t g h f).
Proof. exact (EQ_MP (@lem5998123 A B C y s t g h f) (@lem5998101 A B C y s t g h f)). Qed.
Lemma lem5998126 {A : Type'} (P : A -> Prop) (Q : Prop) : (term236 A P Q) = (term237 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5998127 {A : Type'} (P : A -> Prop) (Q : Prop) : (term236 A P Q) = (term237 A P Q).
Proof. exact (@lem5998126 A P Q). Qed.
Lemma lem5998128 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term273 A B C y s t g h f x) = (term274 A B C y s t g h f x).
Proof. exact (@lem5998127 A (term228 A B t s h y x) (term139 A B C s t g h f x)). Qed.
Lemma lem5998129 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term275 A B t s h y x x') = (term226 A B t s h y x' x).
Proof. exact (eq_refl (term275 A B t s h y x x')). Qed.
Lemma lem5998130 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term276 A B t s h y x) = (term228 A B t s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5998129 A B t s h y x' x)). Qed.
Lemma lem5998131 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5998132 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term277 A B t s h y x) = (term229 A B t s h y x).
Proof. exact (MK_COMB (@lem5998131 A) (@lem5998130 A B t s h y x)). Qed.
Lemma lem5998133 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5998134 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term278 A B t s h y x) = (term267 A B t s h y x).
Proof. exact (MK_COMB (@lem5998133) (@lem5998132 A B t s h y x)). Qed.
Lemma lem5998135 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term139 A B C s t g h f x) = (term139 A B C s t g h f x).
Proof. exact (eq_refl (term139 A B C s t g h f x)). Qed.
Lemma lem5998136 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term273 A B C y s t g h f x) = (term269 A B C y s t g h f x).
Proof. exact (MK_COMB (@lem5998134 A B t s h y x) (@lem5998135 A B C s t g h f x)). Qed.
Lemma lem5998137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5998138 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term279 A B C y s t g h f x) = (term280 A B C y s t g h f x).
Proof. exact (MK_COMB (@lem5998137) (@lem5998136 A B C y s t g h f x)). Qed.
Lemma lem5998139 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term275 A B t s h y x x') = (term226 A B t s h y x' x).
Proof. exact (eq_refl (term275 A B t s h y x x')). Qed.
Lemma lem5998140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5998141 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term281 A B t s h y x x') = (term282 A B t s h y x' x).
Proof. exact (MK_COMB (@lem5998140) (@lem5998139 A B t s h y x' x)). Qed.
Lemma lem5998142 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term139 A B C s t g h f x) = (term139 A B C s t g h f x).
Proof. exact (eq_refl (term139 A B C s t g h f x)). Qed.
Lemma lem5998143 {A B C : Type'} (y : B) (x' : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term283 A B C y x' s t g h f x) = (term284 A B C y x' s t g h f x).
Proof. exact (MK_COMB (@lem5998141 A B t s h y x' x) (@lem5998142 A B C s t g h f x)). Qed.
Lemma lem5998144 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term285 A B C y s t g h f x) = (term286 A B C y s t g h f x).
Proof. exact (fun_ext (fun x' : A => @lem5998143 A B C y x' s t g h f x)). Qed.
Lemma lem5998145 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5998146 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term274 A B C y s t g h f x) = (term287 A B C y s t g h f x).
Proof. exact (MK_COMB (@lem5998145 A) (@lem5998144 A B C y s t g h f x)). Qed.
Lemma lem5998147 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : ((term273 A B C y s t g h f x) = (term274 A B C y s t g h f x)) = ((term269 A B C y s t g h f x) = (term287 A B C y s t g h f x)).
Proof. exact (MK_COMB (@lem5998138 A B C y s t g h f x) (@lem5998146 A B C y s t g h f x)). Qed.
Lemma lem5998148 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term269 A B C y s t g h f x) = (term287 A B C y s t g h f x).
Proof. exact (EQ_MP (@lem5998147 A B C y s t g h f x) (@lem5998128 A B C y s t g h f x)). Qed.
Lemma lem5998149 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term271 A B C y s t g h f) = (term288 A B C y s t g h f).
Proof. exact (fun_ext (fun x : A => @lem5998148 A B C y s t g h f x)). Qed.
Lemma lem5998150 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5998151 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term272 A B C y s t g h f) = (term289 A B C y s t g h f).
Proof. exact (MK_COMB (@lem5998150 A) (@lem5998149 A B C y s t g h f)). Qed.
Lemma lem5998152 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term249 A B C y s t g h f) = (term289 A B C y s t g h f).
Proof. exact (TRANS (@lem5998124 A B C y s t g h f) (@lem5998151 A B C y s t g h f)). Qed.
Lemma lem5998153 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term251 A B C s t g h f) = (term290 A B C s t g h f).
Proof. exact (fun_ext (fun y : B => @lem5998152 A B C y s t g h f)). Qed.
Lemma lem5998154 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5998155 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term252 A B C s t g h f) = (term291 A B C s t g h f).
Proof. exact (MK_COMB (@lem5998154 B) (@lem5998153 A B C s t g h f)). Qed.
Lemma lem5998156 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term235 A B C s t g h f) = (term291 A B C s t g h f).
Proof. exact (TRANS (@lem5998097 A B C s t g h f) (@lem5998155 A B C s t g h f)). Qed.
Lemma lem5998157 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term174 A B C s t g h f) = (term291 A B C s t g h f).
Proof. exact (TRANS (@lem5998071 A B C s t g h f) (@lem5998156 A B C s t g h f)). Qed.
Lemma lem5998158 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term152 A B C s t g h f) = (term291 A B C s t g h f).
Proof. exact (TRANS (@lem5997947 A B C s t g h f) (@lem5998157 A B C s t g h f)). Qed.
Lemma lem5998159 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term32 A B C s t g h f) = (term291 A B C s t g h f).
Proof. exact (TRANS (@lem5997621 A B C s t g h f) (@lem5998158 A B C s t g h f)). Qed.
Lemma lem5998160 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term32 A B C s t g h f) : term291 A B C s t g h f.
Proof. exact (EQ_MP (@lem5998159 A B C s t g h f) (@lem5997396 A B C s t g h f h1)). Qed.
Lemma lem5998161 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term289 A B C y s t g h f) : term289 A B C y s t g h f.
Proof. exact (h1). Qed.
Lemma lem5998162 {A B C : Type'} (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term287 A B C y s t g h f x) : term287 A B C y s t g h f x.
Proof. exact (h1). Qed.
Lemma lem5998163 {A B C : Type'} (y : B) (x' : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term284 A B C y x' s t g h f x) : term284 A B C y x' s t g h f x.
Proof. exact (h1). Qed.
Lemma lem5998192 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (y : B) : (term83 A B t s h k y) = (term83 A B t s h k y).
Proof. exact (eq_refl (term83 A B t s h k y)). Qed.
Lemma lem5998193 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) : (term85 A B t s h k) = (term85 A B t s h k).
Proof. exact (fun_ext (fun y : B => @lem5998192 A B t s h k y)). Qed.
Lemma lem5998194 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5998195 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) : (term86 A B t s h k) = (term86 A B t s h k).
Proof. exact (MK_COMB (@lem5998194 B) (@lem5998193 A B t s h k)). Qed.
Lemma lem5998196 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term86 A B t s h k.
Proof. exact (EQ_MP (@lem5998195 A B t s h k) (@lem5997463 A B t s h k h1)). Qed.
Lemma lem5998239 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term87 A B C s t k g h f x) = (term87 A B C s t k g h f x).
Proof. exact (eq_refl (term87 A B C s t k g h f x)). Qed.
Lemma lem5998240 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) : (term89 A B C s t k g h f) = (term89 A B C s t k g h f).
Proof. exact (fun_ext (fun x : A => @lem5998239 A B C s t k g h f x)). Qed.
Lemma lem5998241 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5998242 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) : (term90 A B C s t k g h f) = (term90 A B C s t k g h f).
Proof. exact (MK_COMB (@lem5998241 A) (@lem5998240 A B C s t k g h f)). Qed.
Lemma lem5998243 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term90 A B C s t k g h f.
Proof. exact (EQ_MP (@lem5998242 A B C s t k g h f) (@lem5997534 A B C s t k g h f h1)). Qed.
Lemma lem5998276 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term139 A B C s t g h f x) = (term139 A B C s t g h f x).
Proof. exact (eq_refl (term139 A B C s t g h f x)). Qed.
Lemma lem5998319 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term104 A B s h y x' x) = (term104 A B s h y x' x).
Proof. exact (eq_refl (term104 A B s h y x' x)). Qed.
Lemma lem5998338 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term92 A B s h x y) = (term92 A B s h x y).
Proof. exact (eq_refl (term92 A B s h x y)). Qed.
Lemma lem5998339 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term115 A B s h y) = (term115 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5998338 A B s h x y)). Qed.
Lemma lem5998340 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5998341 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term117 A B s h y) = (term117 A B s h y).
Proof. exact (MK_COMB (@lem5998340 A) (@lem5998339 A B s h y)). Qed.
Lemma lem5998342 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5998343 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term119 A B s h y) = (term119 A B s h y).
Proof. exact (MK_COMB (@lem5998342) (@lem5998341 A B s h y)). Qed.
Lemma lem5998344 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term199 A B s h y x' x) = (term199 A B s h y x' x).
Proof. exact (MK_COMB (@lem5998343 A B s h y) (@lem5998319 A B s h y x' x)). Qed.
Lemma lem5998351 {B : Type'} (y : B) (t : B -> Prop) : (term121 B y t) = (term121 B y t).
Proof. exact (eq_refl (term121 B y t)). Qed.
Lemma lem5998352 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term226 A B t s h y x' x) = (term226 A B t s h y x' x).
Proof. exact (MK_COMB (@lem5998351 B y t) (@lem5998344 A B s h y x' x)). Qed.
Lemma lem5998353 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5998354 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term282 A B t s h y x' x) = (term282 A B t s h y x' x).
Proof. exact (MK_COMB (@lem5998353) (@lem5998352 A B t s h y x' x)). Qed.
Lemma lem5998355 {A B C : Type'} (y : B) (x' : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term284 A B C y x' s t g h f x) = (term284 A B C y x' s t g h f x).
Proof. exact (MK_COMB (@lem5998354 A B t s h y x' x) (@lem5998276 A B C s t g h f x)). Qed.
Lemma lem5998356 {A B C : Type'} (y : B) (x' : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term284 A B C y x' s t g h f x) : term284 A B C y x' s t g h f x.
Proof. exact (EQ_MP (@lem5998355 A B C y x' s t g h f x) (@lem5998163 A B C y x' s t g h f x h1)). Qed.
Lemma lem5998357 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term226 A B t s h y x' x) : term226 A B t s h y x' x.
Proof. exact (h1). Qed.
Lemma lem5998358 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term139 A B C s t g h f x) : term139 A B C s t g h f x.
Proof. exact (h1). Qed.
Lemma lem5998359 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term226 A B t s h y x' x) : term199 A B s h y x' x.
Proof. exact (proj2 (@lem5998357 A B t s h y x' x h1)). Qed.
Lemma lem5998361 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (h1 : term117 A B s h y) : term117 A B s h y.
Proof. exact (h1). Qed.
Lemma lem5998362 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : term104 A B s h y x' x.
Proof. exact (h1). Qed.
Lemma lem5998363 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : term102 A B s h y x' x.
Proof. exact (proj2 (@lem5998362 A B s h y x' x h1)). Qed.
Lemma lem5998364 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : term71 A B s h x y.
Proof. exact (proj1 (@lem5998362 A B s h y x' x h1)). Qed.
Lemma lem5998366 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : term71 A B s h x' y.
Proof. exact (proj1 (@lem5998363 A B s h y x' x h1)). Qed.
Lemma lem5998371 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term139 A B C s t g h f x) : term135 A B C t g h f x.
Proof. exact (proj2 (@lem5998358 A B C s t g h f x h1)). Qed.
Lemma lem5998392 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h : A -> B) (k : B -> A) (y : B) : (term83 A B t s h k y) = (term292 A B s t h k y).
Proof. exact (@lem19490 (term293 A B k y s) (term294 B y t) ((term295 A B h k y) = y)). Qed.
Lemma lem5998393 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h : A -> B) (k : B -> A) : (term85 A B t s h k) = (term296 A B s t h k).
Proof. exact (fun_ext (fun y : B => @lem5998392 A B s t h k y)). Qed.
Lemma lem5998394 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5998396 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h : A -> B) (k : B -> A) : (term86 A B t s h k) = (term297 A B s t h k).
Proof. exact (MK_COMB (@lem5998394 B) (@lem5998393 A B s t h k)). Qed.
Lemma lem5998397 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term297 A B s t h k.
Proof. exact (EQ_MP (@lem5998396 A B s t h k) (@lem5998196 A B t s h k h1)). Qed.
Lemma lem5998442 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term92 A B s h x y) = (term92 A B s h x y).
Proof. exact (eq_refl (term92 A B s h x y)). Qed.
Lemma lem5998443 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term115 A B s h y) = (term115 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5998442 A B s h x y)). Qed.
Lemma lem5998444 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5998446 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term117 A B s h y) = (term117 A B s h y).
Proof. exact (MK_COMB (@lem5998444 A) (@lem5998443 A B s h y)). Qed.
Lemma lem5998447 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (h1 : term117 A B s h y) : term117 A B s h y.
Proof. exact (EQ_MP (@lem5998446 A B s h y) (@lem5998361 A B s h y h1)). Qed.
Lemma lem5998485 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term87 A B C s t k g h f x) = (term298 A B C t s k g h f x).
Proof. exact (@lem19490 (term136 A B h x t) (term294 A x s) (term299 A B C k g h f x)). Qed.
Lemma lem5998492 {A B C : Type'} (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term300 A B C s k g h f x) = (term301 A B C k s g h f x).
Proof. exact (@lem19490 ((term302 A B k h x) = x) (term294 A x s) ((term137 A B C g h x) = (f x))). Qed.
Lemma lem5998495 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (t : B -> Prop) : (term303 A B s h x t) = (term303 A B s h x t).
Proof. exact (eq_refl (term303 A B s h x t)). Qed.
Lemma lem5998496 {A B C : Type'} (t : B -> Prop) (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term298 A B C t s k g h f x) = (term304 A B C t k s g h f x).
Proof. exact (MK_COMB (@lem5998495 A B s h x t) (@lem5998492 A B C k s g h f x)). Qed.
Lemma lem5998498 {A B C : Type'} (t : B -> Prop) (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term87 A B C s t k g h f x) = (term304 A B C t k s g h f x).
Proof. exact (TRANS (@lem5998485 A B C t s k g h f x) (@lem5998496 A B C t k s g h f x)). Qed.
Lemma lem5998499 {A B C : Type'} (t : B -> Prop) (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term89 A B C s t k g h f) = (term305 A B C t k s g h f).
Proof. exact (fun_ext (fun x : A => @lem5998498 A B C t k s g h f x)). Qed.
Lemma lem5998500 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5998502 {A B C : Type'} (t : B -> Prop) (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term90 A B C s t k g h f) = (term306 A B C t k s g h f).
Proof. exact (MK_COMB (@lem5998500 A) (@lem5998499 A B C t k s g h f)). Qed.
Lemma lem5998503 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term306 A B C t k s g h f.
Proof. exact (EQ_MP (@lem5998502 A B C t k s g h f) (@lem5998243 A B C s t k g h f h1)). Qed.
Lemma lem5998565 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term87 A B C s t k g h f x) = (term298 A B C t s k g h f x).
Proof. exact (@lem19490 (term136 A B h x t) (term294 A x s) (term299 A B C k g h f x)). Qed.
Lemma lem5998572 {A B C : Type'} (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term300 A B C s k g h f x) = (term301 A B C k s g h f x).
Proof. exact (@lem19490 ((term302 A B k h x) = x) (term294 A x s) ((term137 A B C g h x) = (f x))). Qed.
Lemma lem5998575 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (t : B -> Prop) : (term303 A B s h x t) = (term303 A B s h x t).
Proof. exact (eq_refl (term303 A B s h x t)). Qed.
Lemma lem5998576 {A B C : Type'} (t : B -> Prop) (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term298 A B C t s k g h f x) = (term304 A B C t k s g h f x).
Proof. exact (MK_COMB (@lem5998575 A B s h x t) (@lem5998572 A B C k s g h f x)). Qed.
Lemma lem5998578 {A B C : Type'} (t : B -> Prop) (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term87 A B C s t k g h f x) = (term304 A B C t k s g h f x).
Proof. exact (TRANS (@lem5998565 A B C t s k g h f x) (@lem5998576 A B C t k s g h f x)). Qed.
Lemma lem5998579 {A B C : Type'} (t : B -> Prop) (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term89 A B C s t k g h f) = (term305 A B C t k s g h f).
Proof. exact (fun_ext (fun x : A => @lem5998578 A B C t k s g h f x)). Qed.
Lemma lem5998580 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5998582 {A B C : Type'} (t : B -> Prop) (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term90 A B C s t k g h f) = (term306 A B C t k s g h f).
Proof. exact (MK_COMB (@lem5998580 A) (@lem5998579 A B C t k s g h f)). Qed.
Lemma lem5998583 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term306 A B C t k s g h f.
Proof. exact (EQ_MP (@lem5998582 A B C t k s g h f) (@lem5998243 A B C s t k g h f h1)). Qed.
Lemma lem5998591 {A B : Type'} (h : A -> B) (x : A) (t : B -> Prop) (h1 : term307 A B h x t) : term307 A B h x t.
Proof. exact (h1). Qed.
Lemma lem5998629 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term87 A B C s t k g h f x) = (term298 A B C t s k g h f x).
Proof. exact (@lem19490 (term136 A B h x t) (term294 A x s) (term299 A B C k g h f x)). Qed.
Lemma lem5998636 {A B C : Type'} (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term300 A B C s k g h f x) = (term301 A B C k s g h f x).
Proof. exact (@lem19490 ((term302 A B k h x) = x) (term294 A x s) ((term137 A B C g h x) = (f x))). Qed.
Lemma lem5998639 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (t : B -> Prop) : (term303 A B s h x t) = (term303 A B s h x t).
Proof. exact (eq_refl (term303 A B s h x t)). Qed.
Lemma lem5998640 {A B C : Type'} (t : B -> Prop) (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term298 A B C t s k g h f x) = (term304 A B C t k s g h f x).
Proof. exact (MK_COMB (@lem5998639 A B s h x t) (@lem5998636 A B C k s g h f x)). Qed.
Lemma lem5998642 {A B C : Type'} (t : B -> Prop) (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term87 A B C s t k g h f x) = (term304 A B C t k s g h f x).
Proof. exact (TRANS (@lem5998629 A B C t s k g h f x) (@lem5998640 A B C t k s g h f x)). Qed.
Lemma lem5998643 {A B C : Type'} (t : B -> Prop) (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term89 A B C s t k g h f) = (term305 A B C t k s g h f).
Proof. exact (fun_ext (fun x : A => @lem5998642 A B C t k s g h f x)). Qed.
Lemma lem5998644 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5998646 {A B C : Type'} (t : B -> Prop) (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term90 A B C s t k g h f) = (term306 A B C t k s g h f).
Proof. exact (MK_COMB (@lem5998644 A) (@lem5998643 A B C t k s g h f)). Qed.
Lemma lem5998647 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term306 A B C t k s g h f.
Proof. exact (EQ_MP (@lem5998646 A B C t k s g h f) (@lem5998243 A B C s t k g h f h1)). Qed.
Lemma lem5998655 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term308 A B C g h f x) : term308 A B C g h f x.
Proof. exact (h1). Qed.
Lemma lem5998656 {A B : Type'} (_76291 : B) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term309 A B s t h k _76291.
Proof. exact (@lem5998397 A B t s h k h1 _76291). Qed.
Lemma lem5998657 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h : A -> B) (k : B -> A) (_76291 : B) : (term309 A B s t h k _76291) = (term292 A B s t h k _76291).
Proof. exact (eq_refl (term309 A B s t h k _76291)). Qed.
Lemma lem5998658 {A B : Type'} (_76291 : B) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term292 A B s t h k _76291.
Proof. exact (EQ_MP (@lem5998657 A B s t h k _76291) (@lem5998656 A B _76291 t s h k h1)). Qed.
Lemma lem5998662 {A B : Type'} (_76293 : A) (s : A -> Prop) (h : A -> B) (y : B) (h1 : term117 A B s h y) : term310 A B s h y _76293.
Proof. exact (@lem5998447 A B s h y h1 _76293). Qed.
Lemma lem5998663 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76293 : A) (y : B) : (term310 A B s h y _76293) = (term92 A B s h _76293 y).
Proof. exact (eq_refl (term310 A B s h y _76293)). Qed.
Lemma lem5998668 {A B C : Type'} (_76295 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term311 A B C t k s g h f _76295.
Proof. exact (@lem5998503 A B C s t k g h f h1 _76295). Qed.
Lemma lem5998669 {A B C : Type'} (t : B -> Prop) (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (_76295 : A) : (term311 A B C t k s g h f _76295) = (term304 A B C t k s g h f _76295).
Proof. exact (eq_refl (term311 A B C t k s g h f _76295)). Qed.
Lemma lem5998670 {A B C : Type'} (_76295 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term304 A B C t k s g h f _76295.
Proof. exact (EQ_MP (@lem5998669 A B C t k s g h f _76295) (@lem5998668 A B C _76295 s t k g h f h1)). Qed.
Lemma lem5998674 {A B C : Type'} (_76297 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term311 A B C t k s g h f _76297.
Proof. exact (@lem5998583 A B C s t k g h f h1 _76297). Qed.
Lemma lem5998675 {A B C : Type'} (t : B -> Prop) (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (_76297 : A) : (term311 A B C t k s g h f _76297) = (term304 A B C t k s g h f _76297).
Proof. exact (eq_refl (term311 A B C t k s g h f _76297)). Qed.
Lemma lem5998676 {A B C : Type'} (_76297 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term304 A B C t k s g h f _76297.
Proof. exact (EQ_MP (@lem5998675 A B C t k s g h f _76297) (@lem5998674 A B C _76297 s t k g h f h1)). Qed.
Lemma lem5998680 {A B C : Type'} (_76299 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term311 A B C t k s g h f _76299.
Proof. exact (@lem5998647 A B C s t k g h f h1 _76299). Qed.
Lemma lem5998681 {A B C : Type'} (t : B -> Prop) (k : B -> A) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (_76299 : A) : (term311 A B C t k s g h f _76299) = (term304 A B C t k s g h f _76299).
Proof. exact (eq_refl (term311 A B C t k s g h f _76299)). Qed.
Lemma lem5998682 {A B C : Type'} (_76299 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term304 A B C t k s g h f _76299.
Proof. exact (EQ_MP (@lem5998681 A B C t k s g h f _76299) (@lem5998680 A B C _76299 s t k g h f h1)). Qed.
Lemma lem5998689 {A B C : Type'} (_76295 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term301 A B C k s g h f _76295.
Proof. exact (proj2 (@lem5998670 A B C _76295 s t k g h f h1)). Qed.
Lemma lem5998701 {A B C : Type'} (_76299 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term301 A B C k s g h f _76299.
Proof. exact (proj2 (@lem5998682 A B C _76299 s t k g h f h1)). Qed.
Lemma lem5998714 {A B : Type'} (_76293 : A) (s : A -> Prop) (h : A -> B) (y : B) (h1 : term117 A B s h y) : term92 A B s h _76293 y.
Proof. exact (EQ_MP (@lem5998663 A B s h _76293 y) (@lem5998662 A B _76293 s h y h1)). Qed.
Lemma lem5998738 {A B : Type'} (_76291 : B) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term312 A B t k _76291 s.
Proof. exact (proj1 (@lem5998658 A B _76291 t s h k h1)). Qed.
Lemma lem5998744 {A B : Type'} (_76291 : B) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term313 A B t h k _76291.
Proof. exact (proj2 (@lem5998658 A B _76291 t s h k h1)). Qed.
Lemma lem5998752 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : (h x') = y.
Proof. exact (proj2 (@lem5998366 A B s h y x' x h1)). Qed.
Lemma lem5998756 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : (h x) = y.
Proof. exact (proj2 (@lem5998364 A B s h y x' x h1)). Qed.
Lemma lem5998790 {A B : Type'} (h : A -> B) (x : A) (t : B -> Prop) (h1 : term307 A B h x t) : term307 A B h x t.
Proof. exact (h1). Qed.
Lemma lem5998796 {A B C : Type'} (_76297 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term314 A B s h _76297 t.
Proof. exact (proj1 (@lem5998676 A B C _76297 s t k g h f h1)). Qed.
Lemma lem5998824 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term308 A B C g h f x) : term308 A B C g h f x.
Proof. exact (h1). Qed.
Lemma lem5998842 {A B C : Type'} (_76299 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term315 A B C s g h f _76299.
Proof. exact (proj2 (@lem5998701 A B C _76299 s t k g h f h1)). Qed.
Lemma lem5998855 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : y = (h x).
Proof. exact (SYM (@lem5998756 A B s h y x' x h1)). Qed.
Lemma lem5998896 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : term93 A x' x.
Proof. exact (proj2 (@lem5998363 A B s h y x' x h1)). Qed.
Lemma lem5998911 {A B : Type'} (h : A -> B) (x' : A) : (term316 A B h x') = (term316 A B h x').
Proof. exact (eq_refl (term316 A B h x')). Qed.
Lemma lem5998912 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : (term317 A B h x' y) = (term318 A B x' h x).
Proof. exact (MK_COMB (@lem5998911 A B h x') (@lem5998855 A B s h y x' x h1)). Qed.
Lemma lem5998913 {A B : Type'} (x' : A) (h : A -> B) (x : A) : (term318 A B x' h x) = ((h x') = (h x)).
Proof. exact (eq_refl (term318 A B x' h x)). Qed.
Lemma lem5998914 {A B : Type'} (h : A -> B) (x' : A) (y : B) : (term319 A B h x' y) = (term319 A B h x' y).
Proof. exact (eq_refl (term319 A B h x' y)). Qed.
Lemma lem5998915 {A B : Type'} (y : B) (x' : A) (h : A -> B) (x : A) : ((term317 A B h x' y) = (term318 A B x' h x)) = ((term317 A B h x' y) = ((h x') = (h x))).
Proof. exact (MK_COMB (@lem5998914 A B h x' y) (@lem5998913 A B x' h x)). Qed.
Lemma lem5998916 {A B : Type'} (h : A -> B) (x' : A) (y : B) : (term317 A B h x' y) = ((h x') = y).
Proof. exact (eq_refl (term317 A B h x' y)). Qed.
Lemma lem5998917 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5998918 {A B : Type'} (h : A -> B) (x' : A) (y : B) : (term319 A B h x' y) = (term320 A B h x' y).
Proof. exact (MK_COMB (@lem5998917) (@lem5998916 A B h x' y)). Qed.
Lemma lem5998919 {A B : Type'} (x' : A) (h : A -> B) (x : A) : ((h x') = (h x)) = ((h x') = (h x)).
Proof. exact (eq_refl ((h x') = (h x))). Qed.
Lemma lem5998920 {A B : Type'} (y : B) (x' : A) (h : A -> B) (x : A) : ((term317 A B h x' y) = ((h x') = (h x))) = (((h x') = y) = ((h x') = (h x))).
Proof. exact (MK_COMB (@lem5998918 A B h x' y) (@lem5998919 A B x' h x)). Qed.
Lemma lem5998921 {A B : Type'} (y : B) (x' : A) (h : A -> B) (x : A) : ((term317 A B h x' y) = (term318 A B x' h x)) = (((h x') = y) = ((h x') = (h x))).
Proof. exact (TRANS (@lem5998915 A B y x' h x) (@lem5998920 A B y x' h x)). Qed.
Lemma lem5998922 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : ((h x') = y) = ((h x') = (h x)).
Proof. exact (EQ_MP (@lem5998921 A B y x' h x) (@lem5998912 A B s h y x' x h1)). Qed.
Lemma lem5998965 {A B C : Type'} (_76295 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term321 A B s k h _76295.
Proof. exact (proj1 (@lem5998689 A B C _76295 s t k g h f h1)). Qed.
Lemma lem5999089 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term226 A B t s h y x' x) : @IN B y t.
Proof. exact (proj1 (@lem5998357 A B t s h y x' x h1)). Qed.
Lemma lem5999090 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term226 A B t s h y x' x) : term322 B y t.
Proof. exact (fun h0 : term294 B y t => @lem5999089 A B t s h y x' x h1). Qed.
Lemma lem5999092 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999093 {B : Type'} (y : B) (t : B -> Prop) : (term322 B y t) = (@IN B y t).
Proof. exact (@lem5999092 (@IN B y t)). Qed.
Lemma lem5999094 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term226 A B t s h y x' x) : @IN B y t.
Proof. exact (EQ_MP (@lem5999093 B y t) (@lem5999090 A B t s h y x' x h1)). Qed.
Lemma lem5999100 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5999101 {A B : Type'} (k : B -> A) (s : A -> Prop) (_76291 : B) (t : B -> Prop) : (term312 A B t k _76291 s) = (term324 A B k s _76291 t).
Proof. exact (@lem5999100 (term293 A B k _76291 s) (term294 B _76291 t)). Qed.
Lemma lem5999107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5999108 {A B : Type'} (k : B -> A) (s : A -> Prop) (_76291 : B) (t : B -> Prop) : (term325 A B t k _76291 s) = (term326 A B k s _76291 t).
Proof. exact (MK_COMB (@lem5999107) (@lem5999101 A B k s _76291 t)). Qed.
Lemma lem5999114 {A B : Type'} (k : B -> A) (s : A -> Prop) (_76291 : B) (t : B -> Prop) : (term324 A B k s _76291 t) = (term324 A B k s _76291 t).
Proof. exact (eq_refl (term324 A B k s _76291 t)). Qed.
Lemma lem5999115 {A B : Type'} (k : B -> A) (s : A -> Prop) (_76291 : B) (t : B -> Prop) : ((term312 A B t k _76291 s) = (term324 A B k s _76291 t)) = ((term324 A B k s _76291 t) = (term324 A B k s _76291 t)).
Proof. exact (MK_COMB (@lem5999108 A B k s _76291 t) (@lem5999114 A B k s _76291 t)). Qed.
Lemma lem5999117 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5999118 (x : Prop) : (x = x) = True.
Proof. exact (@lem5999117 Prop x). Qed.
Lemma lem5999119 {A B : Type'} (k : B -> A) (s : A -> Prop) (_76291 : B) (t : B -> Prop) : ((term324 A B k s _76291 t) = (term324 A B k s _76291 t)) = True.
Proof. exact (@lem5999118 (term324 A B k s _76291 t)). Qed.
Lemma lem5999120 {A B : Type'} (k : B -> A) (s : A -> Prop) (_76291 : B) (t : B -> Prop) : ((term312 A B t k _76291 s) = (term324 A B k s _76291 t)) = True.
Proof. exact (TRANS (@lem5999115 A B k s _76291 t) (@lem5999119 A B k s _76291 t)). Qed.
Lemma lem5999121 {A B : Type'} (k : B -> A) (s : A -> Prop) (_76291 : B) (t : B -> Prop) : True = ((term312 A B t k _76291 s) = (term324 A B k s _76291 t)).
Proof. exact (SYM (@lem5999120 A B k s _76291 t)). Qed.
Lemma lem5999122 {A B : Type'} (k : B -> A) (s : A -> Prop) (_76291 : B) (t : B -> Prop) : (term312 A B t k _76291 s) = (term324 A B k s _76291 t).
Proof. exact (EQ_MP (@lem5999121 A B k s _76291 t) (@lem0)). Qed.
Lemma lem5999123 {A B : Type'} (_76291 : B) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term324 A B k s _76291 t.
Proof. exact (EQ_MP (@lem5999122 A B k s _76291 t) (@lem5998738 A B _76291 t s h k h1)). Qed.
Lemma lem5999125 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5999126 {A B : Type'} (t : B -> Prop) (k : B -> A) (_76291 : B) (s : A -> Prop) : (term324 A B k s _76291 t) = (term328 A B t k _76291 s).
Proof. exact (@lem5999125 (term294 B _76291 t) (term293 A B k _76291 s)). Qed.
Lemma lem5999128 (a : Prop) : (term38 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5999129 {B : Type'} (_76291 : B) (t : B -> Prop) : (term329 B _76291 t) = (@IN B _76291 t).
Proof. exact (@lem5999128 (@IN B _76291 t)). Qed.
Lemma lem5999130 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5999131 {B : Type'} (_76291 : B) (t : B -> Prop) : (term330 B _76291 t) = (term74 B _76291 t).
Proof. exact (MK_COMB (@lem5999130) (@lem5999129 B _76291 t)). Qed.
Lemma lem5999132 {A B : Type'} (k : B -> A) (_76291 : B) (s : A -> Prop) : (term293 A B k _76291 s) = (term293 A B k _76291 s).
Proof. exact (eq_refl (term293 A B k _76291 s)). Qed.
Lemma lem5999133 {A B : Type'} (t : B -> Prop) (k : B -> A) (_76291 : B) (s : A -> Prop) : (term328 A B t k _76291 s) = (term331 A B t k _76291 s).
Proof. exact (MK_COMB (@lem5999131 B _76291 t) (@lem5999132 A B k _76291 s)). Qed.
Lemma lem5999134 {A B : Type'} (t : B -> Prop) (k : B -> A) (_76291 : B) (s : A -> Prop) : (term324 A B k s _76291 t) = (term331 A B t k _76291 s).
Proof. exact (TRANS (@lem5999126 A B t k _76291 s) (@lem5999133 A B t k _76291 s)). Qed.
Lemma lem5999137 {A B : Type'} (_76291 : B) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term331 A B t k _76291 s.
Proof. exact (EQ_MP (@lem5999134 A B t k _76291 s) (@lem5999123 A B _76291 t s h k h1)). Qed.
Lemma lem5999138 {A B : Type'} (_76291 : B) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term331 A B t k _76291 s.
Proof. exact (@lem5999137 A B _76291 t s h k h1). Qed.
Lemma lem5999139 {A B : Type'} (y : B) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term331 A B t k y s.
Proof. exact (@lem5999138 A B y t s h k h1). Qed.
Lemma lem5999142 {A B : Type'} (k : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term4 A B t s h k) (h2 : term226 A B t s h y x' x) : term293 A B k y s.
Proof. exact (@lem5999139 A B y t s h k h1 (@lem5999094 A B t s h y x' x h2)). Qed.
Lemma lem5999143 {A B : Type'} (k : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term4 A B t s h k) (h2 : term226 A B t s h y x' x) : term332 A B k y s.
Proof. exact (fun h0 : term333 A B k y s => @lem5999142 A B k t s h y x' x h1 h2). Qed.
Lemma lem5999145 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999146 {A B : Type'} (k : B -> A) (y : B) (s : A -> Prop) : (term332 A B k y s) = (term293 A B k y s).
Proof. exact (@lem5999145 (term293 A B k y s)). Qed.
Lemma lem5999147 {A B : Type'} (k : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term4 A B t s h k) (h2 : term226 A B t s h y x' x) : term293 A B k y s.
Proof. exact (EQ_MP (@lem5999146 A B k y s) (@lem5999143 A B k t s h y x' x h1 h2)). Qed.
Lemma lem5999149 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term226 A B t s h y x' x) : @IN B y t.
Proof. exact (proj1 (@lem5998357 A B t s h y x' x h1)). Qed.
Lemma lem5999150 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term226 A B t s h y x' x) : term322 B y t.
Proof. exact (fun h0 : term294 B y t => @lem5999149 A B t s h y x' x h1). Qed.
Lemma lem5999152 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999153 {B : Type'} (y : B) (t : B -> Prop) : (term322 B y t) = (@IN B y t).
Proof. exact (@lem5999152 (@IN B y t)). Qed.
Lemma lem5999154 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term226 A B t s h y x' x) : @IN B y t.
Proof. exact (EQ_MP (@lem5999153 B y t) (@lem5999150 A B t s h y x' x h1)). Qed.
Lemma lem5999160 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5999161 {A B : Type'} (h : A -> B) (k : B -> A) (_76291 : B) (t : B -> Prop) : (term313 A B t h k _76291) = (term334 A B h k _76291 t).
Proof. exact (@lem5999160 ((term295 A B h k _76291) = _76291) (term294 B _76291 t)). Qed.
Lemma lem5999169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5999170 {A B : Type'} (h : A -> B) (k : B -> A) (_76291 : B) (t : B -> Prop) : (term335 A B t h k _76291) = (term336 A B h k _76291 t).
Proof. exact (MK_COMB (@lem5999169) (@lem5999161 A B h k _76291 t)). Qed.
Lemma lem5999178 {A B : Type'} (h : A -> B) (k : B -> A) (_76291 : B) (t : B -> Prop) : (term334 A B h k _76291 t) = (term334 A B h k _76291 t).
Proof. exact (eq_refl (term334 A B h k _76291 t)). Qed.
Lemma lem5999179 {A B : Type'} (h : A -> B) (k : B -> A) (_76291 : B) (t : B -> Prop) : ((term313 A B t h k _76291) = (term334 A B h k _76291 t)) = ((term334 A B h k _76291 t) = (term334 A B h k _76291 t)).
Proof. exact (MK_COMB (@lem5999170 A B h k _76291 t) (@lem5999178 A B h k _76291 t)). Qed.
Lemma lem5999181 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5999182 (x : Prop) : (x = x) = True.
Proof. exact (@lem5999181 Prop x). Qed.
Lemma lem5999183 {A B : Type'} (h : A -> B) (k : B -> A) (_76291 : B) (t : B -> Prop) : ((term334 A B h k _76291 t) = (term334 A B h k _76291 t)) = True.
Proof. exact (@lem5999182 (term334 A B h k _76291 t)). Qed.
Lemma lem5999184 {A B : Type'} (h : A -> B) (k : B -> A) (_76291 : B) (t : B -> Prop) : ((term313 A B t h k _76291) = (term334 A B h k _76291 t)) = True.
Proof. exact (TRANS (@lem5999179 A B h k _76291 t) (@lem5999183 A B h k _76291 t)). Qed.
Lemma lem5999185 {A B : Type'} (h : A -> B) (k : B -> A) (_76291 : B) (t : B -> Prop) : True = ((term313 A B t h k _76291) = (term334 A B h k _76291 t)).
Proof. exact (SYM (@lem5999184 A B h k _76291 t)). Qed.
Lemma lem5999186 {A B : Type'} (h : A -> B) (k : B -> A) (_76291 : B) (t : B -> Prop) : (term313 A B t h k _76291) = (term334 A B h k _76291 t).
Proof. exact (EQ_MP (@lem5999185 A B h k _76291 t) (@lem0)). Qed.
Lemma lem5999187 {A B : Type'} (_76291 : B) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term334 A B h k _76291 t.
Proof. exact (EQ_MP (@lem5999186 A B h k _76291 t) (@lem5998744 A B _76291 t s h k h1)). Qed.
Lemma lem5999189 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5999190 {A B : Type'} (t : B -> Prop) (h : A -> B) (k : B -> A) (_76291 : B) : (term334 A B h k _76291 t) = (term337 A B t h k _76291).
Proof. exact (@lem5999189 (term294 B _76291 t) ((term295 A B h k _76291) = _76291)). Qed.
Lemma lem5999192 (a : Prop) : (term38 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5999193 {B : Type'} (_76291 : B) (t : B -> Prop) : (term329 B _76291 t) = (@IN B _76291 t).
Proof. exact (@lem5999192 (@IN B _76291 t)). Qed.
Lemma lem5999194 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5999195 {B : Type'} (_76291 : B) (t : B -> Prop) : (term330 B _76291 t) = (term74 B _76291 t).
Proof. exact (MK_COMB (@lem5999194) (@lem5999193 B _76291 t)). Qed.
Lemma lem5999196 {A B : Type'} (h : A -> B) (k : B -> A) (_76291 : B) : ((term295 A B h k _76291) = _76291) = ((term295 A B h k _76291) = _76291).
Proof. exact (eq_refl ((term295 A B h k _76291) = _76291)). Qed.
Lemma lem5999197 {A B : Type'} (t : B -> Prop) (h : A -> B) (k : B -> A) (_76291 : B) : (term337 A B t h k _76291) = (term338 A B t h k _76291).
Proof. exact (MK_COMB (@lem5999195 B _76291 t) (@lem5999196 A B h k _76291)). Qed.
Lemma lem5999198 {A B : Type'} (t : B -> Prop) (h : A -> B) (k : B -> A) (_76291 : B) : (term334 A B h k _76291 t) = (term338 A B t h k _76291).
Proof. exact (TRANS (@lem5999190 A B t h k _76291) (@lem5999197 A B t h k _76291)). Qed.
Lemma lem5999201 {A B : Type'} (_76291 : B) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term338 A B t h k _76291.
Proof. exact (EQ_MP (@lem5999198 A B t h k _76291) (@lem5999187 A B _76291 t s h k h1)). Qed.
Lemma lem5999202 {A B : Type'} (_76291 : B) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term338 A B t h k _76291.
Proof. exact (@lem5999201 A B _76291 t s h k h1). Qed.
Lemma lem5999203 {A B : Type'} (y : B) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term338 A B t h k y.
Proof. exact (@lem5999202 A B y t s h k h1). Qed.
Lemma lem5999206 {A B : Type'} (k : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term4 A B t s h k) (h2 : term226 A B t s h y x' x) : (term295 A B h k y) = y.
Proof. exact (@lem5999203 A B y t s h k h1 (@lem5999154 A B t s h y x' x h2)). Qed.
Lemma lem5999207 {A B : Type'} (k : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term4 A B t s h k) (h2 : term226 A B t s h y x' x) : term339 A B h k y.
Proof. exact (fun h0 : term340 A B h k y => @lem5999206 A B k t s h y x' x h1 h2). Qed.
Lemma lem5999209 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999210 {A B : Type'} (h : A -> B) (k : B -> A) (y : B) : (term339 A B h k y) = ((term295 A B h k y) = y).
Proof. exact (@lem5999209 ((term295 A B h k y) = y)). Qed.
Lemma lem5999211 {A B : Type'} (k : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term4 A B t s h k) (h2 : term226 A B t s h y x' x) : (term295 A B h k y) = y.
Proof. exact (EQ_MP (@lem5999210 A B h k y) (@lem5999207 A B k t s h y x' x h1 h2)). Qed.
Lemma lem5999213 (a : Prop) (b : Prop) : (term341 a b) = (term342 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5999214 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76293 : A) (y : B) : (term92 A B s h _76293 y) = (term91 A B s h _76293 y).
Proof. exact (@lem5999213 (@IN A _76293 s) ((h _76293) = y)). Qed.
Lemma lem5999216 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5999217 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76293 : A) (y : B) : (term91 A B s h _76293 y) = (term343 A B s h _76293 y).
Proof. exact (@lem5999216 (term71 A B s h _76293 y)). Qed.
Lemma lem5999218 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76293 : A) (y : B) : (term92 A B s h _76293 y) = (term343 A B s h _76293 y).
Proof. exact (TRANS (@lem5999214 A B s h _76293 y) (@lem5999217 A B s h _76293 y)). Qed.
Lemma lem5999220 {A B : Type'} (k : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term4 A B t s h k) (h2 : term226 A B t s h y x' x) : term84 A B s h k y.
Proof. exact (conj (@lem5999147 A B k t s h y x' x h1 h2) (@lem5999211 A B k t s h y x' x h1 h2)). Qed.
Lemma lem5999222 {A B : Type'} (_76293 : A) (s : A -> Prop) (h : A -> B) (y : B) (h1 : term117 A B s h y) : term343 A B s h _76293 y.
Proof. exact (EQ_MP (@lem5999218 A B s h _76293 y) (@lem5998714 A B _76293 s h y h1)). Qed.
Lemma lem5999223 {A B : Type'} (_76293 : A) (s : A -> Prop) (h : A -> B) (y : B) (h1 : term117 A B s h y) : term343 A B s h _76293 y.
Proof. exact (@lem5999222 A B _76293 s h y h1). Qed.
Lemma lem5999224 {A B : Type'} (k : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (h1 : term117 A B s h y) : term344 A B s h k y.
Proof. exact (@lem5999223 A B (k y) s h y h1). Qed.
Lemma lem5999227 {A B : Type'} (k : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term117 A B s h y) (h2 : term4 A B t s h k) (h3 : term226 A B t s h y x' x) : False.
Proof. exact (@lem5999224 A B k s h y h1 (@lem5999220 A B k t s h y x' x h2 h3)). Qed.
Lemma lem5999228 {A B : Type'} (k : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term117 A B s h y) (h2 : term4 A B t s h k) (h3 : term226 A B t s h y x' x) : term345.
Proof. exact (fun h0 : ~ False => @lem5999227 A B k t s h y x' x h1 h2 h3). Qed.
Lemma lem5999230 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999231 : term345 = False.
Proof. exact (@lem5999230 False). Qed.
Lemma lem5999232 {A B : Type'} (k : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term117 A B s h y) (h2 : term4 A B t s h k) (h3 : term226 A B t s h y x' x) : False.
Proof. exact (EQ_MP (@lem5999231) (@lem5999228 A B k t s h y x' x h1 h2 h3)). Qed.
Lemma lem5999287 {A B : Type'} (k : B -> A) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem5999288 {B : Type'} (_76350 : B) (_76351 : B) (h1 : _76350 = _76351) : _76350 = _76351.
Proof. exact (h1). Qed.
Lemma lem5999289 {A B : Type'} (k : B -> A) (_76350 : B) (_76351 : B) (h1 : _76350 = _76351) : (k _76350) = (k _76351).
Proof. exact (MK_COMB (@lem5999287 A B k) (@lem5999288 B _76350 _76351 h1)). Qed.
Lemma lem5999290 {A B : Type'} (_76350 : B) (k : B -> A) (_76351 : B) : term346 A B _76350 k _76351.
Proof. exact (fun h0 : _76350 = _76351 => @lem5999289 A B k _76350 _76351 h0). Qed.
Lemma lem5999292 (a : Prop) (b : Prop) : (a -> b) = (term347 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5999293 {A B : Type'} (_76350 : B) (k : B -> A) (_76351 : B) : (term346 A B _76350 k _76351) = (term348 A B _76350 k _76351).
Proof. exact (@lem5999292 (_76350 = _76351) ((k _76350) = (k _76351))). Qed.
Lemma lem5999294 {A B : Type'} (_76350 : B) (k : B -> A) (_76351 : B) : term348 A B _76350 k _76351.
Proof. exact (EQ_MP (@lem5999293 A B _76350 k _76351) (@lem5999290 A B _76350 k _76351)). Qed.
Lemma lem5999306 {A : Type'} (x : A) (y : A) (z : A) : term349 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem5999314 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : (h x') = (h x).
Proof. exact (EQ_MP (@lem5998922 A B s h y x' x h1) (@lem5998752 A B s h y x' x h1)). Qed.
Lemma lem5999315 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : term350 A B x' h x.
Proof. exact (fun h0 : term351 A B x' h x => @lem5999314 A B s h y x' x h1). Qed.
Lemma lem5999317 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999318 {A B : Type'} (x' : A) (h : A -> B) (x : A) : (term350 A B x' h x) = ((h x') = (h x)).
Proof. exact (@lem5999317 ((h x') = (h x))). Qed.
Lemma lem5999319 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : (h x') = (h x).
Proof. exact (EQ_MP (@lem5999318 A B x' h x) (@lem5999315 A B s h y x' x h1)). Qed.
Lemma lem5999325 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5999326 {A B : Type'} (k : B -> A) (_76350 : B) (_76351 : B) : (term348 A B _76350 k _76351) = (term352 A B k _76350 _76351).
Proof. exact (@lem5999325 ((k _76350) = (k _76351)) (term93 B _76350 _76351)). Qed.
Lemma lem5999336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5999337 {A B : Type'} (k : B -> A) (_76350 : B) (_76351 : B) : (term353 A B _76350 k _76351) = (term354 A B k _76350 _76351).
Proof. exact (MK_COMB (@lem5999336) (@lem5999326 A B k _76350 _76351)). Qed.
Lemma lem5999347 {A B : Type'} (k : B -> A) (_76350 : B) (_76351 : B) : (term352 A B k _76350 _76351) = (term352 A B k _76350 _76351).
Proof. exact (eq_refl (term352 A B k _76350 _76351)). Qed.
Lemma lem5999348 {A B : Type'} (k : B -> A) (_76350 : B) (_76351 : B) : ((term348 A B _76350 k _76351) = (term352 A B k _76350 _76351)) = ((term352 A B k _76350 _76351) = (term352 A B k _76350 _76351)).
Proof. exact (MK_COMB (@lem5999337 A B k _76350 _76351) (@lem5999347 A B k _76350 _76351)). Qed.
Lemma lem5999350 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5999351 (x : Prop) : (x = x) = True.
Proof. exact (@lem5999350 Prop x). Qed.
Lemma lem5999352 {A B : Type'} (k : B -> A) (_76350 : B) (_76351 : B) : ((term352 A B k _76350 _76351) = (term352 A B k _76350 _76351)) = True.
Proof. exact (@lem5999351 (term352 A B k _76350 _76351)). Qed.
Lemma lem5999353 {A B : Type'} (k : B -> A) (_76350 : B) (_76351 : B) : ((term348 A B _76350 k _76351) = (term352 A B k _76350 _76351)) = True.
Proof. exact (TRANS (@lem5999348 A B k _76350 _76351) (@lem5999352 A B k _76350 _76351)). Qed.
Lemma lem5999354 {A B : Type'} (k : B -> A) (_76350 : B) (_76351 : B) : True = ((term348 A B _76350 k _76351) = (term352 A B k _76350 _76351)).
Proof. exact (SYM (@lem5999353 A B k _76350 _76351)). Qed.
Lemma lem5999355 {A B : Type'} (k : B -> A) (_76350 : B) (_76351 : B) : (term348 A B _76350 k _76351) = (term352 A B k _76350 _76351).
Proof. exact (EQ_MP (@lem5999354 A B k _76350 _76351) (@lem0)). Qed.
Lemma lem5999356 {A B : Type'} (k : B -> A) (_76350 : B) (_76351 : B) : term352 A B k _76350 _76351.
Proof. exact (EQ_MP (@lem5999355 A B k _76350 _76351) (@lem5999294 A B _76350 k _76351)). Qed.
Lemma lem5999358 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5999359 {A B : Type'} (_76350 : B) (k : B -> A) (_76351 : B) : (term352 A B k _76350 _76351) = (term355 A B _76350 k _76351).
Proof. exact (@lem5999358 (term93 B _76350 _76351) ((k _76350) = (k _76351))). Qed.
Lemma lem5999361 (a : Prop) : (term38 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5999362 {B : Type'} (_76350 : B) (_76351 : B) : (term356 B _76350 _76351) = (_76350 = _76351).
Proof. exact (@lem5999361 (_76350 = _76351)). Qed.
Lemma lem5999363 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5999364 {B : Type'} (_76350 : B) (_76351 : B) : (term357 B _76350 _76351) = (term358 B _76350 _76351).
Proof. exact (MK_COMB (@lem5999363) (@lem5999362 B _76350 _76351)). Qed.
Lemma lem5999365 {A B : Type'} (_76350 : B) (k : B -> A) (_76351 : B) : ((k _76350) = (k _76351)) = ((k _76350) = (k _76351)).
Proof. exact (eq_refl ((k _76350) = (k _76351))). Qed.
Lemma lem5999366 {A B : Type'} (_76350 : B) (k : B -> A) (_76351 : B) : (term355 A B _76350 k _76351) = (term346 A B _76350 k _76351).
Proof. exact (MK_COMB (@lem5999364 B _76350 _76351) (@lem5999365 A B _76350 k _76351)). Qed.
Lemma lem5999367 {A B : Type'} (_76350 : B) (k : B -> A) (_76351 : B) : (term352 A B k _76350 _76351) = (term346 A B _76350 k _76351).
Proof. exact (TRANS (@lem5999359 A B _76350 k _76351) (@lem5999366 A B _76350 k _76351)). Qed.
Lemma lem5999370 {A B : Type'} (_76350 : B) (k : B -> A) (_76351 : B) : term346 A B _76350 k _76351.
Proof. exact (EQ_MP (@lem5999367 A B _76350 k _76351) (@lem5999356 A B k _76350 _76351)). Qed.
Lemma lem5999371 {A B : Type'} (_76350 : B) (k : B -> A) (_76351 : B) : term346 A B _76350 k _76351.
Proof. exact (@lem5999370 A B _76350 k _76351). Qed.
Lemma lem5999372 {A B : Type'} (x' : A) (k : B -> A) (h : A -> B) (x : A) : term359 A B x' k h x.
Proof. exact (@lem5999371 A B (h x') k (h x)). Qed.
Lemma lem5999375 {A B : Type'} (k : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : (term302 A B k h x') = (term302 A B k h x).
Proof. exact (@lem5999372 A B x' k h x (@lem5999319 A B s h y x' x h1)). Qed.
Lemma lem5999376 {A B : Type'} (k : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : term360 A B x' k h x.
Proof. exact (fun h0 : term361 A B x' k h x => @lem5999375 A B k s h y x' x h1). Qed.
Lemma lem5999378 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999379 {A B : Type'} (x' : A) (k : B -> A) (h : A -> B) (x : A) : (term360 A B x' k h x) = ((term302 A B k h x') = (term302 A B k h x)).
Proof. exact (@lem5999378 ((term302 A B k h x') = (term302 A B k h x))). Qed.
Lemma lem5999380 {A B : Type'} (k : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : (term302 A B k h x') = (term302 A B k h x).
Proof. exact (EQ_MP (@lem5999379 A B x' k h x) (@lem5999376 A B k s h y x' x h1)). Qed.
Lemma lem5999382 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : @IN A x' s.
Proof. exact (proj1 (@lem5998366 A B s h y x' x h1)). Qed.
Lemma lem5999383 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : term322 A x' s.
Proof. exact (fun h0 : term294 A x' s => @lem5999382 A B s h y x' x h1). Qed.
Lemma lem5999385 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999386 {A : Type'} (x' : A) (s : A -> Prop) : (term322 A x' s) = (@IN A x' s).
Proof. exact (@lem5999385 (@IN A x' s)). Qed.
Lemma lem5999387 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : @IN A x' s.
Proof. exact (EQ_MP (@lem5999386 A x' s) (@lem5999383 A B s h y x' x h1)). Qed.
Lemma lem5999393 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5999394 {A B : Type'} (k : B -> A) (h : A -> B) (_76295 : A) (s : A -> Prop) : (term321 A B s k h _76295) = (term362 A B k h _76295 s).
Proof. exact (@lem5999393 ((term302 A B k h _76295) = _76295) (term294 A _76295 s)). Qed.
Lemma lem5999402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5999403 {A B : Type'} (k : B -> A) (h : A -> B) (_76295 : A) (s : A -> Prop) : (term363 A B s k h _76295) = (term364 A B k h _76295 s).
Proof. exact (MK_COMB (@lem5999402) (@lem5999394 A B k h _76295 s)). Qed.
Lemma lem5999411 {A B : Type'} (k : B -> A) (h : A -> B) (_76295 : A) (s : A -> Prop) : (term362 A B k h _76295 s) = (term362 A B k h _76295 s).
Proof. exact (eq_refl (term362 A B k h _76295 s)). Qed.
Lemma lem5999412 {A B : Type'} (k : B -> A) (h : A -> B) (_76295 : A) (s : A -> Prop) : ((term321 A B s k h _76295) = (term362 A B k h _76295 s)) = ((term362 A B k h _76295 s) = (term362 A B k h _76295 s)).
Proof. exact (MK_COMB (@lem5999403 A B k h _76295 s) (@lem5999411 A B k h _76295 s)). Qed.
Lemma lem5999414 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5999415 (x : Prop) : (x = x) = True.
Proof. exact (@lem5999414 Prop x). Qed.
Lemma lem5999416 {A B : Type'} (k : B -> A) (h : A -> B) (_76295 : A) (s : A -> Prop) : ((term362 A B k h _76295 s) = (term362 A B k h _76295 s)) = True.
Proof. exact (@lem5999415 (term362 A B k h _76295 s)). Qed.
Lemma lem5999417 {A B : Type'} (k : B -> A) (h : A -> B) (_76295 : A) (s : A -> Prop) : ((term321 A B s k h _76295) = (term362 A B k h _76295 s)) = True.
Proof. exact (TRANS (@lem5999412 A B k h _76295 s) (@lem5999416 A B k h _76295 s)). Qed.
Lemma lem5999418 {A B : Type'} (k : B -> A) (h : A -> B) (_76295 : A) (s : A -> Prop) : True = ((term321 A B s k h _76295) = (term362 A B k h _76295 s)).
Proof. exact (SYM (@lem5999417 A B k h _76295 s)). Qed.
Lemma lem5999419 {A B : Type'} (k : B -> A) (h : A -> B) (_76295 : A) (s : A -> Prop) : (term321 A B s k h _76295) = (term362 A B k h _76295 s).
Proof. exact (EQ_MP (@lem5999418 A B k h _76295 s) (@lem0)). Qed.
Lemma lem5999420 {A B C : Type'} (_76295 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term362 A B k h _76295 s.
Proof. exact (EQ_MP (@lem5999419 A B k h _76295 s) (@lem5998965 A B C _76295 s t k g h f h1)). Qed.
Lemma lem5999422 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5999423 {A B : Type'} (s : A -> Prop) (k : B -> A) (h : A -> B) (_76295 : A) : (term362 A B k h _76295 s) = (term365 A B s k h _76295).
Proof. exact (@lem5999422 (term294 A _76295 s) ((term302 A B k h _76295) = _76295)). Qed.
Lemma lem5999425 (a : Prop) : (term38 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5999426 {A : Type'} (_76295 : A) (s : A -> Prop) : (term329 A _76295 s) = (@IN A _76295 s).
Proof. exact (@lem5999425 (@IN A _76295 s)). Qed.
Lemma lem5999427 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5999428 {A : Type'} (_76295 : A) (s : A -> Prop) : (term330 A _76295 s) = (term74 A _76295 s).
Proof. exact (MK_COMB (@lem5999427) (@lem5999426 A _76295 s)). Qed.
Lemma lem5999429 {A B : Type'} (k : B -> A) (h : A -> B) (_76295 : A) : ((term302 A B k h _76295) = _76295) = ((term302 A B k h _76295) = _76295).
Proof. exact (eq_refl ((term302 A B k h _76295) = _76295)). Qed.
Lemma lem5999430 {A B : Type'} (s : A -> Prop) (k : B -> A) (h : A -> B) (_76295 : A) : (term365 A B s k h _76295) = (term366 A B s k h _76295).
Proof. exact (MK_COMB (@lem5999428 A _76295 s) (@lem5999429 A B k h _76295)). Qed.
Lemma lem5999431 {A B : Type'} (s : A -> Prop) (k : B -> A) (h : A -> B) (_76295 : A) : (term362 A B k h _76295 s) = (term366 A B s k h _76295).
Proof. exact (TRANS (@lem5999423 A B s k h _76295) (@lem5999430 A B s k h _76295)). Qed.
Lemma lem5999434 {A B C : Type'} (_76295 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term366 A B s k h _76295.
Proof. exact (EQ_MP (@lem5999431 A B s k h _76295) (@lem5999420 A B C _76295 s t k g h f h1)). Qed.
Lemma lem5999435 {A B C : Type'} (_76295 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term366 A B s k h _76295.
Proof. exact (@lem5999434 A B C _76295 s t k g h f h1). Qed.
Lemma lem5999436 {A B C : Type'} (x' : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term366 A B s k h x'.
Proof. exact (@lem5999435 A B C x' s t k g h f h1). Qed.
Lemma lem5999439 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : (term302 A B k h x') = x'.
Proof. exact (@lem5999436 A B C x' s t k g h f h1 (@lem5999387 A B s h y x' x h2)). Qed.
Lemma lem5999440 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : term367 A B k h x'.
Proof. exact (fun h0 : term368 A B k h x' => @lem5999439 A B C t k g f s h y x' x h1 h2). Qed.
Lemma lem5999442 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999443 {A B : Type'} (k : B -> A) (h : A -> B) (x' : A) : (term367 A B k h x') = ((term302 A B k h x') = x').
Proof. exact (@lem5999442 ((term302 A B k h x') = x')). Qed.
Lemma lem5999444 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : (term302 A B k h x') = x'.
Proof. exact (EQ_MP (@lem5999443 A B k h x') (@lem5999440 A B C t k g f s h y x' x h1 h2)). Qed.
Lemma lem5999462 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5999463 {A : Type'} (y : A) (x : A) (z : A) : (term369 A x y z) = (term370 A y x z).
Proof. exact (@lem5999462 (y = z) (term93 A x z)). Qed.
Lemma lem5999473 {A : Type'} (x : A) (y : A) : (term371 A x y) = (term371 A x y).
Proof. exact (eq_refl (term371 A x y)). Qed.
Lemma lem5999474 {A : Type'} (y : A) (x : A) (z : A) : (term349 A x y z) = (term372 A y x z).
Proof. exact (MK_COMB (@lem5999473 A x y) (@lem5999463 A y x z)). Qed.
Lemma lem5999478 (q : Prop) (p : Prop) (r : Prop) : (term373 p q r) = (term373 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5999479 {A : Type'} (y : A) (x : A) (z : A) : (term372 A y x z) = (term374 A y x z).
Proof. exact (@lem5999478 (y = z) (term93 A x y) (term93 A x z)). Qed.
Lemma lem5999501 {A : Type'} (y : A) (x : A) (z : A) : (term349 A x y z) = (term374 A y x z).
Proof. exact (TRANS (@lem5999474 A y x z) (@lem5999479 A y x z)). Qed.
Lemma lem5999502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5999503 {A : Type'} (y : A) (x : A) (z : A) : (term375 A x y z) = (term376 A y x z).
Proof. exact (MK_COMB (@lem5999502) (@lem5999501 A y x z)). Qed.
Lemma lem5999525 {A : Type'} (y : A) (x : A) (z : A) : (term374 A y x z) = (term374 A y x z).
Proof. exact (eq_refl (term374 A y x z)). Qed.
Lemma lem5999526 {A : Type'} (y : A) (x : A) (z : A) : ((term349 A x y z) = (term374 A y x z)) = ((term374 A y x z) = (term374 A y x z)).
Proof. exact (MK_COMB (@lem5999503 A y x z) (@lem5999525 A y x z)). Qed.
Lemma lem5999528 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5999529 (x : Prop) : (x = x) = True.
Proof. exact (@lem5999528 Prop x). Qed.
Lemma lem5999530 {A : Type'} (y : A) (x : A) (z : A) : ((term374 A y x z) = (term374 A y x z)) = True.
Proof. exact (@lem5999529 (term374 A y x z)). Qed.
Lemma lem5999531 {A : Type'} (y : A) (x : A) (z : A) : ((term349 A x y z) = (term374 A y x z)) = True.
Proof. exact (TRANS (@lem5999526 A y x z) (@lem5999530 A y x z)). Qed.
Lemma lem5999532 {A : Type'} (y : A) (x : A) (z : A) : True = ((term349 A x y z) = (term374 A y x z)).
Proof. exact (SYM (@lem5999531 A y x z)). Qed.
Lemma lem5999533 {A : Type'} (y : A) (x : A) (z : A) : (term349 A x y z) = (term374 A y x z).
Proof. exact (EQ_MP (@lem5999532 A y x z) (@lem0)). Qed.
Lemma lem5999534 {A : Type'} (y : A) (x : A) (z : A) : term374 A y x z.
Proof. exact (EQ_MP (@lem5999533 A y x z) (@lem5999306 A x y z)). Qed.
Lemma lem5999536 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5999537 {A : Type'} (x : A) (y : A) (z : A) : (term374 A y x z) = (term377 A x y z).
Proof. exact (@lem5999536 (term378 A y x z) (y = z)). Qed.
Lemma lem5999539 (a : Prop) (b : Prop) : (term379 a b) = (term380 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5999540 {A : Type'} (y : A) (x : A) (z : A) : (term381 A y x z) = (term382 A y x z).
Proof. exact (@lem5999539 (term93 A x y) (term93 A x z)). Qed.
Lemma lem5999542 (a : Prop) : (term38 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5999543 {A : Type'} (x : A) (y : A) : (term356 A x y) = (x = y).
Proof. exact (@lem5999542 (x = y)). Qed.
Lemma lem5999544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5999545 {A : Type'} (x : A) (y : A) : (term383 A x y) = (term384 A x y).
Proof. exact (MK_COMB (@lem5999544) (@lem5999543 A x y)). Qed.
Lemma lem5999547 (a : Prop) : (term38 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5999548 {A : Type'} (x : A) (z : A) : (term356 A x z) = (x = z).
Proof. exact (@lem5999547 (x = z)). Qed.
Lemma lem5999549 {A : Type'} (y : A) (x : A) (z : A) : (term382 A y x z) = (term385 A y x z).
Proof. exact (MK_COMB (@lem5999545 A x y) (@lem5999548 A x z)). Qed.
Lemma lem5999550 {A : Type'} (y : A) (x : A) (z : A) : (term381 A y x z) = (term385 A y x z).
Proof. exact (TRANS (@lem5999540 A y x z) (@lem5999549 A y x z)). Qed.
Lemma lem5999551 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5999552 {A : Type'} (y : A) (x : A) (z : A) : (term386 A y x z) = (term387 A y x z).
Proof. exact (MK_COMB (@lem5999551) (@lem5999550 A y x z)). Qed.
Lemma lem5999553 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5999554 {A : Type'} (x : A) (y : A) (z : A) : (term377 A x y z) = (term388 A x y z).
Proof. exact (MK_COMB (@lem5999552 A y x z) (@lem5999553 A y z)). Qed.
Lemma lem5999555 {A : Type'} (x : A) (y : A) (z : A) : (term374 A y x z) = (term388 A x y z).
Proof. exact (TRANS (@lem5999537 A x y z) (@lem5999554 A x y z)). Qed.
Lemma lem5999557 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : term389 A B x k h x'.
Proof. exact (conj (@lem5999380 A B k s h y x' x h2) (@lem5999444 A B C t k g f s h y x' x h1 h2)). Qed.
Lemma lem5999559 {A : Type'} (x : A) (y : A) (z : A) : term388 A x y z.
Proof. exact (EQ_MP (@lem5999555 A x y z) (@lem5999534 A y x z)). Qed.
Lemma lem5999560 {A : Type'} (x : A) (y : A) (z : A) : term388 A x y z.
Proof. exact (@lem5999559 A x y z). Qed.
Lemma lem5999561 {A B : Type'} (k : B -> A) (h : A -> B) (x : A) (x' : A) : term390 A B k h x x'.
Proof. exact (@lem5999560 A (term302 A B k h x') (term302 A B k h x) x'). Qed.
Lemma lem5999564 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : (term302 A B k h x) = x'.
Proof. exact (@lem5999561 A B k h x x' (@lem5999557 A B C t k g f s h y x' x h1 h2)). Qed.
Lemma lem5999565 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : term391 A B k h x x'.
Proof. exact (fun h0 : term392 A B k h x x' => @lem5999564 A B C t k g f s h y x' x h1 h2). Qed.
Lemma lem5999567 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999568 {A B : Type'} (k : B -> A) (h : A -> B) (x : A) (x' : A) : (term391 A B k h x x') = ((term302 A B k h x) = x').
Proof. exact (@lem5999567 ((term302 A B k h x) = x')). Qed.
Lemma lem5999569 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : (term302 A B k h x) = x'.
Proof. exact (EQ_MP (@lem5999568 A B k h x x') (@lem5999565 A B C t k g f s h y x' x h1 h2)). Qed.
Lemma lem5999571 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : @IN A x s.
Proof. exact (proj1 (@lem5998364 A B s h y x' x h1)). Qed.
Lemma lem5999572 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : term322 A x s.
Proof. exact (fun h0 : term294 A x s => @lem5999571 A B s h y x' x h1). Qed.
Lemma lem5999574 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999575 {A : Type'} (x : A) (s : A -> Prop) : (term322 A x s) = (@IN A x s).
Proof. exact (@lem5999574 (@IN A x s)). Qed.
Lemma lem5999576 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : @IN A x s.
Proof. exact (EQ_MP (@lem5999575 A x s) (@lem5999572 A B s h y x' x h1)). Qed.
Lemma lem5999578 {A B C : Type'} (_76295 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term366 A B s k h _76295.
Proof. exact (EQ_MP (@lem5999431 A B s k h _76295) (@lem5999420 A B C _76295 s t k g h f h1)). Qed.
Lemma lem5999579 {A B C : Type'} (_76295 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term366 A B s k h _76295.
Proof. exact (@lem5999578 A B C _76295 s t k g h f h1). Qed.
Lemma lem5999580 {A B C : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term366 A B s k h x.
Proof. exact (@lem5999579 A B C x s t k g h f h1). Qed.
Lemma lem5999583 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : (term302 A B k h x) = x.
Proof. exact (@lem5999580 A B C x s t k g h f h1 (@lem5999576 A B s h y x' x h2)). Qed.
Lemma lem5999584 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : term367 A B k h x.
Proof. exact (fun h0 : term368 A B k h x => @lem5999583 A B C t k g f s h y x' x h1 h2). Qed.
Lemma lem5999586 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999587 {A B : Type'} (k : B -> A) (h : A -> B) (x : A) : (term367 A B k h x) = ((term302 A B k h x) = x).
Proof. exact (@lem5999586 ((term302 A B k h x) = x)). Qed.
Lemma lem5999588 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : (term302 A B k h x) = x.
Proof. exact (EQ_MP (@lem5999587 A B k h x) (@lem5999584 A B C t k g f s h y x' x h1 h2)). Qed.
Lemma lem5999589 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : term393 A B x' k h x.
Proof. exact (conj (@lem5999569 A B C t k g f s h y x' x h1 h2) (@lem5999588 A B C t k g f s h y x' x h1 h2)). Qed.
Lemma lem5999591 {A : Type'} (x : A) (y : A) (z : A) : term388 A x y z.
Proof. exact (EQ_MP (@lem5999555 A x y z) (@lem5999534 A y x z)). Qed.
Lemma lem5999592 {A : Type'} (x : A) (y : A) (z : A) : term388 A x y z.
Proof. exact (@lem5999591 A x y z). Qed.
Lemma lem5999593 {A B : Type'} (k : B -> A) (h : A -> B) (x' : A) (x : A) : term394 A B k h x' x.
Proof. exact (@lem5999592 A (term302 A B k h x) x' x). Qed.
Lemma lem5999596 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : x' = x.
Proof. exact (@lem5999593 A B k h x' x (@lem5999589 A B C t k g f s h y x' x h1 h2)). Qed.
Lemma lem5999597 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : term395 A x' x.
Proof. exact (fun h0 : term93 A x' x => @lem5999596 A B C t k g f s h y x' x h1 h2). Qed.
Lemma lem5999599 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999600 {A : Type'} (x' : A) (x : A) : (term395 A x' x) = (x' = x).
Proof. exact (@lem5999599 (x' = x)). Qed.
Lemma lem5999601 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : x' = x.
Proof. exact (EQ_MP (@lem5999600 A x' x) (@lem5999597 A B C t k g f s h y x' x h1 h2)). Qed.
Lemma lem5999604 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5999606 {A : Type'} (x' : A) (x : A) : (term93 A x' x) = (term396 A x' x).
Proof. exact (@lem5999604 (x' = x)). Qed.
Lemma lem5999609 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term104 A B s h y x' x) : term396 A x' x.
Proof. exact (EQ_MP (@lem5999606 A x' x) (@lem5998896 A B s h y x' x h1)). Qed.
Lemma lem5999612 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : False.
Proof. exact (@lem5999609 A B s h y x' x h2 (@lem5999601 A B C t k g f s h y x' x h1 h2)). Qed.
Lemma lem5999613 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : term345.
Proof. exact (fun h0 : ~ False => @lem5999612 A B C t k g f s h y x' x h1 h2). Qed.
Lemma lem5999615 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999616 : term345 = False.
Proof. exact (@lem5999615 False). Qed.
Lemma lem5999699 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term139 A B C s t g h f x) : @IN A x s.
Proof. exact (proj1 (@lem5998358 A B C s t g h f x h1)). Qed.
Lemma lem5999700 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term139 A B C s t g h f x) : term322 A x s.
Proof. exact (fun h0 : term294 A x s => @lem5999699 A B C s t g h f x h1). Qed.
Lemma lem5999702 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999703 {A : Type'} (x : A) (s : A -> Prop) : (term322 A x s) = (@IN A x s).
Proof. exact (@lem5999702 (@IN A x s)). Qed.
Lemma lem5999704 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term139 A B C s t g h f x) : @IN A x s.
Proof. exact (EQ_MP (@lem5999703 A x s) (@lem5999700 A B C s t g h f x h1)). Qed.
Lemma lem5999710 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5999711 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76297 : A) (s : A -> Prop) : (term314 A B s h _76297 t) = (term397 A B h t _76297 s).
Proof. exact (@lem5999710 (term136 A B h _76297 t) (term294 A _76297 s)). Qed.
Lemma lem5999717 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5999718 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76297 : A) (s : A -> Prop) : (term398 A B s h _76297 t) = (term399 A B h t _76297 s).
Proof. exact (MK_COMB (@lem5999717) (@lem5999711 A B h t _76297 s)). Qed.
Lemma lem5999724 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76297 : A) (s : A -> Prop) : (term397 A B h t _76297 s) = (term397 A B h t _76297 s).
Proof. exact (eq_refl (term397 A B h t _76297 s)). Qed.
Lemma lem5999725 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76297 : A) (s : A -> Prop) : ((term314 A B s h _76297 t) = (term397 A B h t _76297 s)) = ((term397 A B h t _76297 s) = (term397 A B h t _76297 s)).
Proof. exact (MK_COMB (@lem5999718 A B h t _76297 s) (@lem5999724 A B h t _76297 s)). Qed.
Lemma lem5999727 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5999728 (x : Prop) : (x = x) = True.
Proof. exact (@lem5999727 Prop x). Qed.
Lemma lem5999729 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76297 : A) (s : A -> Prop) : ((term397 A B h t _76297 s) = (term397 A B h t _76297 s)) = True.
Proof. exact (@lem5999728 (term397 A B h t _76297 s)). Qed.
Lemma lem5999730 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76297 : A) (s : A -> Prop) : ((term314 A B s h _76297 t) = (term397 A B h t _76297 s)) = True.
Proof. exact (TRANS (@lem5999725 A B h t _76297 s) (@lem5999729 A B h t _76297 s)). Qed.
Lemma lem5999731 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76297 : A) (s : A -> Prop) : True = ((term314 A B s h _76297 t) = (term397 A B h t _76297 s)).
Proof. exact (SYM (@lem5999730 A B h t _76297 s)). Qed.
Lemma lem5999732 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76297 : A) (s : A -> Prop) : (term314 A B s h _76297 t) = (term397 A B h t _76297 s).
Proof. exact (EQ_MP (@lem5999731 A B h t _76297 s) (@lem0)). Qed.
Lemma lem5999733 {A B C : Type'} (_76297 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term397 A B h t _76297 s.
Proof. exact (EQ_MP (@lem5999732 A B h t _76297 s) (@lem5998796 A B C _76297 s t k g h f h1)). Qed.
Lemma lem5999735 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5999736 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76297 : A) (t : B -> Prop) : (term397 A B h t _76297 s) = (term400 A B s h _76297 t).
Proof. exact (@lem5999735 (term294 A _76297 s) (term136 A B h _76297 t)). Qed.
Lemma lem5999738 (a : Prop) : (term38 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5999739 {A : Type'} (_76297 : A) (s : A -> Prop) : (term329 A _76297 s) = (@IN A _76297 s).
Proof. exact (@lem5999738 (@IN A _76297 s)). Qed.
Lemma lem5999740 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5999741 {A : Type'} (_76297 : A) (s : A -> Prop) : (term330 A _76297 s) = (term74 A _76297 s).
Proof. exact (MK_COMB (@lem5999740) (@lem5999739 A _76297 s)). Qed.
Lemma lem5999742 {A B : Type'} (h : A -> B) (_76297 : A) (t : B -> Prop) : (term136 A B h _76297 t) = (term136 A B h _76297 t).
Proof. exact (eq_refl (term136 A B h _76297 t)). Qed.
Lemma lem5999743 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76297 : A) (t : B -> Prop) : (term400 A B s h _76297 t) = (term401 A B s h _76297 t).
Proof. exact (MK_COMB (@lem5999741 A _76297 s) (@lem5999742 A B h _76297 t)). Qed.
Lemma lem5999744 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76297 : A) (t : B -> Prop) : (term397 A B h t _76297 s) = (term401 A B s h _76297 t).
Proof. exact (TRANS (@lem5999736 A B s h _76297 t) (@lem5999743 A B s h _76297 t)). Qed.
Lemma lem5999747 {A B C : Type'} (_76297 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term401 A B s h _76297 t.
Proof. exact (EQ_MP (@lem5999744 A B s h _76297 t) (@lem5999733 A B C _76297 s t k g h f h1)). Qed.
Lemma lem5999748 {A B C : Type'} (_76297 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term401 A B s h _76297 t.
Proof. exact (@lem5999747 A B C _76297 s t k g h f h1). Qed.
Lemma lem5999749 {A B C : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term401 A B s h x t.
Proof. exact (@lem5999748 A B C x s t k g h f h1). Qed.
Lemma lem5999752 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term139 A B C s t g h f x) : term136 A B h x t.
Proof. exact (@lem5999749 A B C x s t k g h f h1 (@lem5999704 A B C s t g h f x h2)). Qed.
Lemma lem5999753 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term139 A B C s t g h f x) : term402 A B h x t.
Proof. exact (fun h0 : term307 A B h x t => @lem5999752 A B C k s t g h f x h1 h2). Qed.
Lemma lem5999755 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999756 {A B : Type'} (h : A -> B) (x : A) (t : B -> Prop) : (term402 A B h x t) = (term136 A B h x t).
Proof. exact (@lem5999755 (term136 A B h x t)). Qed.
Lemma lem5999757 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term139 A B C s t g h f x) : term136 A B h x t.
Proof. exact (EQ_MP (@lem5999756 A B h x t) (@lem5999753 A B C k s t g h f x h1 h2)). Qed.
Lemma lem5999760 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5999762 {A B : Type'} (h : A -> B) (x : A) (t : B -> Prop) : (term307 A B h x t) = (term403 A B h x t).
Proof. exact (@lem5999760 (term136 A B h x t)). Qed.
Lemma lem5999765 {A B : Type'} (h : A -> B) (x : A) (t : B -> Prop) (h1 : term307 A B h x t) : term403 A B h x t.
Proof. exact (EQ_MP (@lem5999762 A B h x t) (@lem5998790 A B h x t h1)). Qed.
Lemma lem5999768 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term307 A B h x t) (h3 : term139 A B C s t g h f x) : False.
Proof. exact (@lem5999765 A B h x t h2 (@lem5999757 A B C k s t g h f x h1 h3)). Qed.
Lemma lem5999769 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term307 A B h x t) (h3 : term139 A B C s t g h f x) : term345.
Proof. exact (fun h0 : ~ False => @lem5999768 A B C k s t g h f x h1 h2 h3). Qed.
Lemma lem5999771 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999772 : term345 = False.
Proof. exact (@lem5999771 False). Qed.
Lemma lem5999773 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term307 A B h x t) (h3 : term139 A B C s t g h f x) : False.
Proof. exact (EQ_MP (@lem5999772) (@lem5999769 A B C k s t g h f x h1 h2 h3)). Qed.
Lemma lem5999855 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term139 A B C s t g h f x) : @IN A x s.
Proof. exact (proj1 (@lem5998358 A B C s t g h f x h1)). Qed.
Lemma lem5999856 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term139 A B C s t g h f x) : term322 A x s.
Proof. exact (fun h0 : term294 A x s => @lem5999855 A B C s t g h f x h1). Qed.
Lemma lem5999858 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999859 {A : Type'} (x : A) (s : A -> Prop) : (term322 A x s) = (@IN A x s).
Proof. exact (@lem5999858 (@IN A x s)). Qed.
Lemma lem5999860 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term139 A B C s t g h f x) : @IN A x s.
Proof. exact (EQ_MP (@lem5999859 A x s) (@lem5999856 A B C s t g h f x h1)). Qed.
Lemma lem5999866 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5999867 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76299 : A) (s : A -> Prop) : (term315 A B C s g h f _76299) = (term404 A B C g h f _76299 s).
Proof. exact (@lem5999866 ((term137 A B C g h _76299) = (f _76299)) (term294 A _76299 s)). Qed.
Lemma lem5999875 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5999876 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76299 : A) (s : A -> Prop) : (term405 A B C s g h f _76299) = (term406 A B C g h f _76299 s).
Proof. exact (MK_COMB (@lem5999875) (@lem5999867 A B C g h f _76299 s)). Qed.
Lemma lem5999884 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76299 : A) (s : A -> Prop) : (term404 A B C g h f _76299 s) = (term404 A B C g h f _76299 s).
Proof. exact (eq_refl (term404 A B C g h f _76299 s)). Qed.
Lemma lem5999885 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76299 : A) (s : A -> Prop) : ((term315 A B C s g h f _76299) = (term404 A B C g h f _76299 s)) = ((term404 A B C g h f _76299 s) = (term404 A B C g h f _76299 s)).
Proof. exact (MK_COMB (@lem5999876 A B C g h f _76299 s) (@lem5999884 A B C g h f _76299 s)). Qed.
Lemma lem5999887 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5999888 (x : Prop) : (x = x) = True.
Proof. exact (@lem5999887 Prop x). Qed.
Lemma lem5999889 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76299 : A) (s : A -> Prop) : ((term404 A B C g h f _76299 s) = (term404 A B C g h f _76299 s)) = True.
Proof. exact (@lem5999888 (term404 A B C g h f _76299 s)). Qed.
Lemma lem5999890 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76299 : A) (s : A -> Prop) : ((term315 A B C s g h f _76299) = (term404 A B C g h f _76299 s)) = True.
Proof. exact (TRANS (@lem5999885 A B C g h f _76299 s) (@lem5999889 A B C g h f _76299 s)). Qed.
Lemma lem5999891 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76299 : A) (s : A -> Prop) : True = ((term315 A B C s g h f _76299) = (term404 A B C g h f _76299 s)).
Proof. exact (SYM (@lem5999890 A B C g h f _76299 s)). Qed.
Lemma lem5999892 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76299 : A) (s : A -> Prop) : (term315 A B C s g h f _76299) = (term404 A B C g h f _76299 s).
Proof. exact (EQ_MP (@lem5999891 A B C g h f _76299 s) (@lem0)). Qed.
Lemma lem5999893 {A B C : Type'} (_76299 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term404 A B C g h f _76299 s.
Proof. exact (EQ_MP (@lem5999892 A B C g h f _76299 s) (@lem5998842 A B C _76299 s t k g h f h1)). Qed.
Lemma lem5999895 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5999896 {A B C : Type'} (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (_76299 : A) : (term404 A B C g h f _76299 s) = (term407 A B C s g h f _76299).
Proof. exact (@lem5999895 (term294 A _76299 s) ((term137 A B C g h _76299) = (f _76299))). Qed.
Lemma lem5999898 (a : Prop) : (term38 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5999899 {A : Type'} (_76299 : A) (s : A -> Prop) : (term329 A _76299 s) = (@IN A _76299 s).
Proof. exact (@lem5999898 (@IN A _76299 s)). Qed.
Lemma lem5999900 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5999901 {A : Type'} (_76299 : A) (s : A -> Prop) : (term330 A _76299 s) = (term74 A _76299 s).
Proof. exact (MK_COMB (@lem5999900) (@lem5999899 A _76299 s)). Qed.
Lemma lem5999902 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76299 : A) : ((term137 A B C g h _76299) = (f _76299)) = ((term137 A B C g h _76299) = (f _76299)).
Proof. exact (eq_refl ((term137 A B C g h _76299) = (f _76299))). Qed.
Lemma lem5999903 {A B C : Type'} (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (_76299 : A) : (term407 A B C s g h f _76299) = (term408 A B C s g h f _76299).
Proof. exact (MK_COMB (@lem5999901 A _76299 s) (@lem5999902 A B C g h f _76299)). Qed.
Lemma lem5999904 {A B C : Type'} (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (_76299 : A) : (term404 A B C g h f _76299 s) = (term408 A B C s g h f _76299).
Proof. exact (TRANS (@lem5999896 A B C s g h f _76299) (@lem5999903 A B C s g h f _76299)). Qed.
Lemma lem5999907 {A B C : Type'} (_76299 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term408 A B C s g h f _76299.
Proof. exact (EQ_MP (@lem5999904 A B C s g h f _76299) (@lem5999893 A B C _76299 s t k g h f h1)). Qed.
Lemma lem5999908 {A B C : Type'} (_76299 : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term408 A B C s g h f _76299.
Proof. exact (@lem5999907 A B C _76299 s t k g h f h1). Qed.
Lemma lem5999909 {A B C : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) : term408 A B C s g h f x.
Proof. exact (@lem5999908 A B C x s t k g h f h1). Qed.
Lemma lem5999912 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term139 A B C s t g h f x) : (term137 A B C g h x) = (f x).
Proof. exact (@lem5999909 A B C x s t k g h f h1 (@lem5999860 A B C s t g h f x h2)). Qed.
Lemma lem5999913 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term139 A B C s t g h f x) : term409 A B C g h f x.
Proof. exact (fun h0 : term308 A B C g h f x => @lem5999912 A B C k s t g h f x h1 h2). Qed.
Lemma lem5999915 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999916 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term409 A B C g h f x) = ((term137 A B C g h x) = (f x)).
Proof. exact (@lem5999915 ((term137 A B C g h x) = (f x))). Qed.
Lemma lem5999917 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term139 A B C s t g h f x) : (term137 A B C g h x) = (f x).
Proof. exact (EQ_MP (@lem5999916 A B C g h f x) (@lem5999913 A B C k s t g h f x h1 h2)). Qed.
Lemma lem5999920 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5999922 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term308 A B C g h f x) = (term410 A B C g h f x).
Proof. exact (@lem5999920 ((term137 A B C g h x) = (f x))). Qed.
Lemma lem5999925 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term308 A B C g h f x) : term410 A B C g h f x.
Proof. exact (EQ_MP (@lem5999922 A B C g h f x) (@lem5998824 A B C g h f x h1)). Qed.
Lemma lem5999928 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term308 A B C g h f x) (h3 : term139 A B C s t g h f x) : False.
Proof. exact (@lem5999925 A B C g h f x h2 (@lem5999917 A B C k s t g h f x h1 h3)). Qed.
Lemma lem5999929 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term308 A B C g h f x) (h3 : term139 A B C s t g h f x) : term345.
Proof. exact (fun h0 : ~ False => @lem5999928 A B C k s t g h f x h1 h2 h3). Qed.
Lemma lem5999931 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5999932 : term345 = False.
Proof. exact (@lem5999931 False). Qed.
Lemma lem5999933 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term308 A B C g h f x) (h3 : term139 A B C s t g h f x) : False.
Proof. exact (EQ_MP (@lem5999932) (@lem5999929 A B C k s t g h f x h1 h2 h3)). Qed.
Lemma lem5999934 {A B C : Type'} (t : B -> Prop) (k : B -> A) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term104 A B s h y x' x) : False.
Proof. exact (EQ_MP (@lem5999616) (@lem5999613 A B C t k g f s h y x' x h1 h2)). Qed.
Lemma lem5999935 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term308 A B C g h f x) (h3 : term139 A B C s t g h f x) : (term308 A B C g h f x) = False.
Proof. exact (prop_ext (fun h4 : term308 A B C g h f x => @lem5999933 A B C k s t g h f x h1 h2 h3) (fun h4 : False => @lem5998824 A B C g h f x h2)). Qed.
Lemma lem5999936 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term308 A B C g h f x) (h3 : term139 A B C s t g h f x) : False.
Proof. exact (EQ_MP (@lem5999935 A B C k s t g h f x h1 h2 h3) (@lem5998824 A B C g h f x h2)). Qed.
Lemma lem5999937 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term307 A B h x t) (h3 : term139 A B C s t g h f x) : (term307 A B h x t) = False.
Proof. exact (prop_ext (fun h4 : term307 A B h x t => @lem5999773 A B C k s t g h f x h1 h2 h3) (fun h4 : False => @lem5998790 A B h x t h2)). Qed.
Lemma lem5999938 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term307 A B h x t) (h3 : term139 A B C s t g h f x) : False.
Proof. exact (EQ_MP (@lem5999937 A B C k s t g h f x h1 h2 h3) (@lem5998790 A B h x t h2)). Qed.
Lemma lem5999939 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term308 A B C g h f x) (h3 : term139 A B C s t g h f x) : (term308 A B C g h f x) = False.
Proof. exact (prop_ext (fun h4 : term308 A B C g h f x => @lem5999936 A B C k s t g h f x h1 h2 h3) (fun h4 : False => @lem5998655 A B C g h f x h2)). Qed.
Lemma lem5999940 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term308 A B C g h f x) (h3 : term139 A B C s t g h f x) : False.
Proof. exact (EQ_MP (@lem5999939 A B C k s t g h f x h1 h2 h3) (@lem5998655 A B C g h f x h2)). Qed.
Lemma lem5999941 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term307 A B h x t) (h3 : term139 A B C s t g h f x) : (term307 A B h x t) = False.
Proof. exact (prop_ext (fun h4 : term307 A B h x t => @lem5999938 A B C k s t g h f x h1 h2 h3) (fun h4 : False => @lem5998591 A B h x t h2)). Qed.
Lemma lem5999942 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term307 A B h x t) (h3 : term139 A B C s t g h f x) : False.
Proof. exact (EQ_MP (@lem5999941 A B C k s t g h f x h1 h2 h3) (@lem5998591 A B h x t h2)). Qed.
Lemma lem5999943 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term308 A B C g h f x) (h3 : term139 A B C s t g h f x) : (term308 A B C g h f x) = False.
Proof. exact (prop_ext (fun h4 : term308 A B C g h f x => @lem5999940 A B C k s t g h f x h1 h2 h3) (fun h4 : False => @lem5998655 A B C g h f x h2)). Qed.
Lemma lem5999944 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term308 A B C g h f x) (h3 : term139 A B C s t g h f x) : False.
Proof. exact (EQ_MP (@lem5999943 A B C k s t g h f x h1 h2 h3) (@lem5998655 A B C g h f x h2)). Qed.
Lemma lem5999945 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term307 A B h x t) (h3 : term139 A B C s t g h f x) : (term307 A B h x t) = False.
Proof. exact (prop_ext (fun h4 : term307 A B h x t => @lem5999942 A B C k s t g h f x h1 h2 h3) (fun h4 : False => @lem5998591 A B h x t h2)). Qed.
Lemma lem5999946 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term307 A B h x t) (h3 : term139 A B C s t g h f x) : False.
Proof. exact (EQ_MP (@lem5999945 A B C k s t g h f x h1 h2 h3) (@lem5998591 A B h x t h2)). Qed.
Lemma lem5999947 {A B : Type'} (k : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term117 A B s h y) (h2 : term4 A B t s h k) (h3 : term226 A B t s h y x' x) : (term117 A B s h y) = False.
Proof. exact (prop_ext (fun h4 : term117 A B s h y => @lem5999232 A B k t s h y x' x h1 h2 h3) (fun h4 : False => @lem5998447 A B s h y h1)). Qed.
Lemma lem5999948 {A B : Type'} (k : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term117 A B s h y) (h2 : term4 A B t s h k) (h3 : term226 A B t s h y x' x) : False.
Proof. exact (EQ_MP (@lem5999947 A B k t s h y x' x h1 h2 h3) (@lem5998447 A B s h y h1)). Qed.
Lemma lem5999949 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term139 A B C s t g h f x) : False.
Proof. exact (or_elim (@lem5998371 A B C s t g h f x h2) (fun h0 : term307 A B h x t => @lem5999946 A B C k s t g h f x h1 h0 h2) (fun h0 : term308 A B C g h f x => @lem5999944 A B C k s t g h f x h1 h0 h2)). Qed.
Lemma lem5999950 {A B C : Type'} (g : B -> C) (f : A -> C) (k : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : term226 A B t s h y x' x) : False.
Proof. exact (or_elim (@lem5998359 A B t s h y x' x h3) (fun h0 : term117 A B s h y => @lem5999948 A B k t s h y x' x h0 h2 h3) (fun h0 : term104 A B s h y x' x => @lem5999934 A B C t k g f s h y x' x h1 h0)). Qed.
Lemma lem5999951 {A B C : Type'} (k : B -> A) (y : B) (x' : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : term284 A B C y x' s t g h f x) : False.
Proof. exact (or_elim (@lem5998356 A B C y x' s t g h f x h3) (fun h0 : term226 A B t s h y x' x => @lem5999950 A B C g f k t s h y x' x h1 h2 h0) (fun h0 : term139 A B C s t g h f x => @lem5999949 A B C k s t g h f x h1 h0)). Qed.
Lemma lem5999952 {A B C : Type'} (k : B -> A) (y : B) (x' : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : term284 A B C y x' s t g h f x) : (term284 A B C y x' s t g h f x) = False.
Proof. exact (prop_ext (fun h4 : term284 A B C y x' s t g h f x => @lem5999951 A B C k y x' s t g h f x h1 h2 h3) (fun h4 : False => @lem5998356 A B C y x' s t g h f x h3)). Qed.
Lemma lem5999953 {A B C : Type'} (k : B -> A) (y : B) (x' : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : term284 A B C y x' s t g h f x) : False.
Proof. exact (EQ_MP (@lem5999952 A B C k y x' s t g h f x h1 h2 h3) (@lem5998356 A B C y x' s t g h f x h3)). Qed.
Lemma lem5999954 {A B C : Type'} (k : B -> A) (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : term287 A B C y s t g h f x) : False.
Proof. exact (ex_elim (@lem5998162 A B C y s t g h f x h3) (fun x' : A => fun h0 : term286 A B C y s t g h f x x' => @lem5999953 A B C k y x' s t g h f x h1 h2 h0)). Qed.
Lemma lem5999955 {A B C : Type'} (k : B -> A) (y : B) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : term289 A B C y s t g h f) : False.
Proof. exact (ex_elim (@lem5998161 A B C y s t g h f h3) (fun x : A => fun h0 : term288 A B C y s t g h f x => @lem5999954 A B C k y s t g h f x h1 h2 h0)). Qed.
Lemma lem5999956 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : term32 A B C s t g h f) : False.
Proof. exact (ex_elim (@lem5998160 A B C s t g h f h3) (fun y : B => fun h0 : term290 A B C s t g h f y => @lem5999955 A B C k y s t g h f h1 h2 h0)). Qed.
Lemma lem5999957 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : term32 A B C s t g h f) : (term32 A B C s t g h f) = False.
Proof. exact (prop_ext (fun h4 : term32 A B C s t g h f => @lem5999956 A B C k s t g h f h1 h2 h3) (fun h4 : False => @lem5997396 A B C s t g h f h3)). Qed.
Lemma lem5999958 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : term32 A B C s t g h f) : False.
Proof. exact (EQ_MP (@lem5999957 A B C k s t g h f h1 h2 h3) (@lem5997396 A B C s t g h f h3)). Qed.
Lemma lem5999959 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) : term31 A B C s t g h f.
Proof. exact (fun h0 : term32 A B C s t g h f => @lem5999958 A B C k s t g h f h1 h2 h0). Qed.
Lemma lem5999960 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) : term16 A B C s t g h f.
Proof. exact (EQ_MP (@lem5997395 A B C s t g h f) (@lem5999959 A B C g f t s h k h1 h2)). Qed.
Lemma lem5999961 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term41 A B C k s t g h f.
Proof. exact (fun h0 : term3 A B C s t k g h f => @lem5999960 A B C g f t s h k h0 h1). Qed.
Lemma lem5999962 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : term43 A B C k s t g h f.
Proof. exact (fun h0 : term4 A B t s h k => @lem5999961 A B C g f t s h k h0). Qed.
Lemma lem5999967 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : term47 A B C s t g h f.
Proof. exact (fun k : B -> A => @lem5999962 A B C k s t g h f). Qed.
Lemma lem5999972 {A B C : Type'} (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : term51 A B C t g h f.
Proof. exact (fun s : A -> Prop => @lem5999967 A B C s t g h f). Qed.
Lemma lem5999977 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) : term55 A B C g h f.
Proof. exact (fun t : B -> Prop => @lem5999972 A B C t g h f). Qed.
Lemma lem5999982 {A B C : Type'} (h : A -> B) (f : A -> C) : term59 A B C h f.
Proof. exact (fun g : B -> C => @lem5999977 A B C g h f). Qed.
Lemma lem5999987 {A B C : Type'} (f : A -> C) : term63 A B C f.
Proof. exact (fun h : A -> B => @lem5999982 A B C h f). Qed.
Lemma lem5999992 {A B C : Type'} : term67 A B C.
Proof. exact (fun f : A -> C => @lem5999987 A B C f). Qed.
Lemma lem5999993 {A B C : Type'} : term66 A B C.
Proof. exact (EQ_MP (@lem5997389 A B C) (@lem5999992 A B C)). Qed.
Lemma lem5999994 {A B C : Type'} (f : A -> C) : term411 A B C f.
Proof. exact (@lem5999993 A B C f). Qed.
Lemma lem5999995 {A B C : Type'} (f : A -> C) : (term411 A B C f) = (term62 A B C f).
Proof. exact (eq_refl (term411 A B C f)). Qed.
Lemma lem5999996 {A B C : Type'} (f : A -> C) : term62 A B C f.
Proof. exact (EQ_MP (@lem5999995 A B C f) (@lem5999994 A B C f)). Qed.
Lemma lem5999997 {A B C : Type'} (f : A -> C) (h : A -> B) : term412 A B C f h.
Proof. exact (@lem5999996 A B C f h). Qed.
Lemma lem5999998 {A B C : Type'} (h : A -> B) (f : A -> C) : (term412 A B C f h) = (term58 A B C h f).
Proof. exact (eq_refl (term412 A B C f h)). Qed.
Lemma lem5999999 {A B C : Type'} (h : A -> B) (f : A -> C) : term58 A B C h f.
Proof. exact (EQ_MP (@lem5999998 A B C h f) (@lem5999997 A B C f h)). Qed.
Lemma lem6000000 {A B C : Type'} (h : A -> B) (f : A -> C) (g : B -> C) : term413 A B C h f g.
Proof. exact (@lem5999999 A B C h f g). Qed.
Lemma lem6000001 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) : (term413 A B C h f g) = (term54 A B C g h f).
Proof. exact (eq_refl (term413 A B C h f g)). Qed.
Lemma lem6000002 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) : term54 A B C g h f.
Proof. exact (EQ_MP (@lem6000001 A B C g h f) (@lem6000000 A B C h f g)). Qed.
Lemma lem6000003 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (t : B -> Prop) : term414 A B C g h f t.
Proof. exact (@lem6000002 A B C g h f t). Qed.
Lemma lem6000004 {A B C : Type'} (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term414 A B C g h f t) = (term50 A B C t g h f).
Proof. exact (eq_refl (term414 A B C g h f t)). Qed.
Lemma lem6000005 {A B C : Type'} (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : term50 A B C t g h f.
Proof. exact (EQ_MP (@lem6000004 A B C t g h f) (@lem6000003 A B C g h f t)). Qed.
Lemma lem6000006 {A B C : Type'} (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (s : A -> Prop) : term415 A B C t g h f s.
Proof. exact (@lem6000005 A B C t g h f s). Qed.
Lemma lem6000007 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term415 A B C t g h f s) = (term46 A B C s t g h f).
Proof. exact (eq_refl (term415 A B C t g h f s)). Qed.
Lemma lem6000008 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : term46 A B C s t g h f.
Proof. exact (EQ_MP (@lem6000007 A B C s t g h f) (@lem6000006 A B C t g h f s)). Qed.
Lemma lem6000009 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (k : B -> A) : term416 A B C s t g h f k.
Proof. exact (@lem6000008 A B C s t g h f k). Qed.
Lemma lem6000010 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term416 A B C s t g h f k) = (term33 A B C k s t g h f).
Proof. exact (eq_refl (term416 A B C s t g h f k)). Qed.
Lemma lem6000011 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : term33 A B C k s t g h f.
Proof. exact (EQ_MP (@lem6000010 A B C k s t g h f) (@lem6000009 A B C s t g h f k)). Qed.
Lemma lem6000013 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : term33 A B C k s t g h f.
Proof. exact (@lem5997094 A B C k s t g h f (@lem6000011 A B C k s t g h f)). Qed.
Lemma lem6000014 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term4 A B t s h k) : term40 A B C k s t g h f.
Proof. exact (@lem6000013 A B C k s t g h f (@lem5997020 A B t s h k h1)). Qed.
Lemma lem6000015 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) : term31 A B C s t g h f.
Proof. exact (@lem6000014 A B C g f t s h k h2 (@lem5997019 A B C s t k g h f h1)). Qed.
Lemma lem6000016 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : term32 A B C s t g h f) : False.
Proof. exact (@lem6000015 A B C g f t s h k h1 h2 (@lem5997078 A B C s t g h f h3)). Qed.
Lemma lem6000017 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : term32 A B C s t g h f) : (term32 A B C s t g h f) = False.
Proof. exact (prop_ext (fun h4 : term32 A B C s t g h f => @lem6000016 A B C k s t g h f h1 h2 h3) (fun h4 : False => @lem5997078 A B C s t g h f h3)). Qed.
Lemma lem6000018 {A B C : Type'} (k : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : term32 A B C s t g h f) : False.
Proof. exact (EQ_MP (@lem6000017 A B C k s t g h f h1 h2 h3) (@lem5997078 A B C s t g h f h3)). Qed.
Lemma lem6000019 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) : term31 A B C s t g h f.
Proof. exact (fun h0 : term32 A B C s t g h f => @lem6000018 A B C k s t g h f h1 h2 h0). Qed.
Lemma lem6000020 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) : term16 A B C s t g h f.
Proof. exact (EQ_MP (@lem5997077 A B C s t g h f) (@lem6000019 A B C g f t s h k h1 h2)). Qed.
Lemma lem6000021 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) : term18 A B C s t g f.
Proof. exact (ex_intro (term19 A B C s t g f) h (@lem6000020 A B C g f t s h k h1 h2)). Qed.
Lemma lem6000022 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (op : type1400 C) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : @monoidal C op) : (@iterate C A op s f) = (@iterate C B op t g).
Proof. exact (@lem5997073 A B C s f t g op h3 (@lem6000021 A B C g f t s h k h1 h2)). Qed.
Lemma lem6000023 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term2 A B C s t k g h f) : term3 A B C s t k g h f.
Proof. exact (proj2 (@lem5997018 A B C s t k g h f h1)). Qed.
Lemma lem6000024 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term2 A B C s t k g h f) : term4 A B t s h k.
Proof. exact (proj1 (@lem5997018 A B C s t k g h f h1)). Qed.
Lemma lem6000025 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (op : type1400 C) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : @monoidal C op) : (term3 A B C s t k g h f) = ((@iterate C A op s f) = (@iterate C B op t g)).
Proof. exact (prop_ext (fun h4 : term3 A B C s t k g h f => @lem6000022 A B C g f t s h k op h1 h2 h3) (fun h4 : (@iterate C A op s f) = (@iterate C B op t g) => @lem5997019 A B C s t k g h f h1)). Qed.
Lemma lem6000026 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (op : type1400 C) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : @monoidal C op) : (@iterate C A op s f) = (@iterate C B op t g).
Proof. exact (EQ_MP (@lem6000025 A B C g f t s h k op h1 h2 h3) (@lem5997019 A B C s t k g h f h1)). Qed.
Lemma lem6000027 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (op : type1400 C) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : @monoidal C op) : (term4 A B t s h k) = ((@iterate C A op s f) = (@iterate C B op t g)).
Proof. exact (prop_ext (fun h4 : term4 A B t s h k => @lem6000026 A B C g f t s h k op h1 h2 h3) (fun h4 : (@iterate C A op s f) = (@iterate C B op t g) => @lem5997020 A B t s h k h2)). Qed.
Lemma lem6000028 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (k : B -> A) (op : type1400 C) (h1 : term3 A B C s t k g h f) (h2 : term4 A B t s h k) (h3 : @monoidal C op) : (@iterate C A op s f) = (@iterate C B op t g).
Proof. exact (EQ_MP (@lem6000027 A B C g f t s h k op h1 h2 h3) (@lem5997020 A B t s h k h2)). Qed.
Lemma lem6000029 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term4 A B t s h k) (h2 : @monoidal C op) (h3 : term2 A B C s t k g h f) : (term3 A B C s t k g h f) = ((@iterate C A op s f) = (@iterate C B op t g)).
Proof. exact (prop_ext (fun h4 : term3 A B C s t k g h f => @lem6000028 A B C g f t s h k op h4 h1 h2) (fun h4 : (@iterate C A op s f) = (@iterate C B op t g) => @lem6000023 A B C s t k g h f h3)). Qed.
Lemma lem6000030 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term4 A B t s h k) (h2 : @monoidal C op) (h3 : term2 A B C s t k g h f) : (@iterate C A op s f) = (@iterate C B op t g).
Proof. exact (EQ_MP (@lem6000029 A B C op s t k g h f h1 h2 h3) (@lem6000023 A B C s t k g h f h3)). Qed.
Lemma lem6000031 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : @monoidal C op) (h2 : term2 A B C s t k g h f) : (term4 A B t s h k) = ((@iterate C A op s f) = (@iterate C B op t g)).
Proof. exact (prop_ext (fun h3 : term4 A B t s h k => @lem6000030 A B C op s t k g h f h3 h1 h2) (fun h3 : (@iterate C A op s f) = (@iterate C B op t g) => @lem6000024 A B C s t k g h f h2)). Qed.
Lemma lem6000032 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : @monoidal C op) (h2 : term2 A B C s t k g h f) : (@iterate C A op s f) = (@iterate C B op t g).
Proof. exact (EQ_MP (@lem6000031 A B C op s t k g h f h1 h2) (@lem6000024 A B C s t k g h f h2)). Qed.
Lemma lem6000033 {A B C : Type'} (k : B -> A) (h : A -> B) (s : A -> Prop) (f : A -> C) (t : B -> Prop) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : term417 A B C k h s f op t g.
Proof. exact (fun h0 : term2 A B C s t k g h f => @lem6000032 A B C op s t k g h f h1 h0). Qed.
Lemma lem6000038 {A B C : Type'} (h : A -> B) (s : A -> Prop) (f : A -> C) (t : B -> Prop) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : term418 A B C h s f op t g.
Proof. exact (fun k : B -> A => @lem6000033 A B C k h s f t g op h1). Qed.
Lemma lem6000043 {A B C : Type'} (s : A -> Prop) (f : A -> C) (t : B -> Prop) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : term419 A B C s f op t g.
Proof. exact (fun h : A -> B => @lem6000038 A B C h s f t g op h1). Qed.
Lemma lem6000048 {A B C : Type'} (s : A -> Prop) (f : A -> C) (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term420 A B C s f op t.
Proof. exact (fun g : B -> C => @lem6000043 A B C s f t g op h1). Qed.
Lemma lem6000053 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term421 A B C s op t.
Proof. exact (fun f : A -> C => @lem6000048 A B C s f t op h1). Qed.
Lemma lem6000058 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term422 A B C s op.
Proof. exact (fun t : B -> Prop => @lem6000053 A B C s t op h1). Qed.
Lemma lem6000063 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term423 A B C op.
Proof. exact (fun s : A -> Prop => @lem6000058 A B C s op h1). Qed.
Lemma lem6000064 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = (term423 A B C op).
Proof. exact (prop_ext (fun h2 : @monoidal C op => @lem6000063 A B C op h1) (fun h2 : term423 A B C op => @lem5997017 C op h1)). Qed.
Lemma lem6000065 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term423 A B C op.
Proof. exact (EQ_MP (@lem6000064 A B C op h1) (@lem5997017 C op h1)). Qed.
Lemma lem6000066 {A B C : Type'} (op : type1400 C) : term424 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem6000065 A B C op h0). Qed.
Lemma lem6000071 {A B C : Type'} : term425 A B C.
Proof. exact (fun op : type1400 C => @lem6000066 A B C op). Qed.
