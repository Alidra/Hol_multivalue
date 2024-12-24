Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8057155_term_abbrevs.
Require Import thm8049005_spec.
Require Import thm8049006_spec.
Require Import thm8049023_spec.
Require Import thm8050197_spec.
Require Import thm8050477_spec.
Require Import thm8054010_spec.
Require Import thm8055464_spec.
Lemma lem8057146 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (f : type56 _143007 _143009) (h1 : term0 _143007 _143009 f) : (term1 _143007 _143008 _143009 s f) = (term2 _143007 _143008 _143009 f s).
Proof. exact (EQ_MP (@lem8050477 _143007 _143008 _143009 f s) (@lem8055464 _143007 _143008 _143009 s f h1)). Qed.
Lemma lem8057147 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (f : type56 _143007 _143009) (h1 : term0 _143007 _143009 f) : (term0 _143007 _143009 f) = ((term1 _143007 _143008 _143009 s f) = (term2 _143007 _143008 _143009 f s)).
Proof. exact (prop_ext (fun h2 : term0 _143007 _143009 f => @lem8057146 _143007 _143008 _143009 s f h1) (fun h2 : (term1 _143007 _143008 _143009 s f) = (term2 _143007 _143008 _143009 f s) => @lem8049023 _143007 _143009 f h1)). Qed.
Lemma lem8057148 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (f : type56 _143007 _143009) (h1 : term0 _143007 _143009 f) : (term1 _143007 _143008 _143009 s f) = (term2 _143007 _143008 _143009 f s).
Proof. exact (EQ_MP (@lem8057147 _143007 _143008 _143009 s f h1) (@lem8049023 _143007 _143009 f h1)). Qed.
Lemma lem8057149 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term3 _143007 _143008 _143009 f s.
Proof. exact (fun h0 : term0 _143007 _143009 f => @lem8057148 _143007 _143008 _143009 s f h0). Qed.
Lemma lem8057150 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : (term1 _143007 _143008 _143009 s f) = (@PCROSS _143007 _143008 _143009 s (@UNIV (cart _143007 _143009))).
Proof. exact (EQ_MP (@lem8050197 _143007 _143008 _143009 s f h1) (@lem8054010 _143007 _143008 _143009 s f h1)). Qed.
Lemma lem8057151 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : (f = (@EMPTY ((cart _143007 _143009) -> Prop))) = ((term1 _143007 _143008 _143009 s f) = (@PCROSS _143007 _143008 _143009 s (@UNIV (cart _143007 _143009)))).
Proof. exact (prop_ext (fun h2 : f = (@EMPTY ((cart _143007 _143009) -> Prop)) => @lem8057150 _143007 _143008 _143009 s f h1) (fun h2 : (term1 _143007 _143008 _143009 s f) = (@PCROSS _143007 _143008 _143009 s (@UNIV (cart _143007 _143009))) => @lem8049006 _143007 _143009 f h1)). Qed.
Lemma lem8057152 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : (term1 _143007 _143008 _143009 s f) = (@PCROSS _143007 _143008 _143009 s (@UNIV (cart _143007 _143009))).
Proof. exact (EQ_MP (@lem8057151 _143007 _143008 _143009 s f h1) (@lem8049006 _143007 _143009 f h1)). Qed.
Lemma lem8057153 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term4 _143007 _143008 _143009 f s.
Proof. exact (fun h0 : f = (@EMPTY ((cart _143007 _143009) -> Prop)) => @lem8057152 _143007 _143008 _143009 s f h0). Qed.
Lemma lem8057154 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term5 _143007 _143008 _143009 f s.
Proof. exact (conj (@lem8057153 _143007 _143008 _143009 f s) (@lem8057149 _143007 _143008 _143009 f s)). Qed.
Lemma lem8057155 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term1 _143007 _143008 _143009 s f) = (term6 _143007 _143008 _143009 f s).
Proof. exact (EQ_MP (@lem8049005 _143007 _143008 _143009 f s) (@lem8057154 _143007 _143008 _143009 f s)). Qed.
