Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8057179_term_abbrevs.
Require Import thm8048849_spec.
Require Import thm8048850_spec.
Require Import thm8048867_spec.
Require Import thm8048931_spec.
Require Import thm8048932_spec.
Require Import thm8048949_spec.
Require Import thm8049396_spec.
Require Import thm8049688_spec.
Require Import thm8050018_spec.
Require Import thm8051187_spec.
Require Import thm8051509_spec.
Require Import thm8053821_spec.
Lemma lem8057158 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term0 _142951 _142952 f) (h2 : term0 _142951 _142953 g) : (term1 _142951 _142952 _142953 f g) = (term2 _142951 _142952 _142953 f g).
Proof. exact (EQ_MP (@lem8050018 _142951 _142952 _142953 f g) (@lem8053821 _142951 _142952 _142953 f g h1 h2)). Qed.
Lemma lem8057159 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term0 _142951 _142952 f) (h2 : term0 _142951 _142953 g) : (term0 _142951 _142953 g) = ((term1 _142951 _142952 _142953 f g) = (term2 _142951 _142952 _142953 f g)).
Proof. exact (prop_ext (fun h3 : term0 _142951 _142953 g => @lem8057158 _142951 _142952 _142953 f g h1 h2) (fun h3 : (term1 _142951 _142952 _142953 f g) = (term2 _142951 _142952 _142953 f g) => @lem8048949 _142951 _142953 g h2)). Qed.
Lemma lem8057160 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term0 _142951 _142952 f) (h2 : term0 _142951 _142953 g) : (term1 _142951 _142952 _142953 f g) = (term2 _142951 _142952 _142953 f g).
Proof. exact (EQ_MP (@lem8057159 _142951 _142952 _142953 f g h1 h2) (@lem8048949 _142951 _142953 g h2)). Qed.
Lemma lem8057161 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term0 _142951 _142952 f) : term3 _142951 _142952 _142953 f g.
Proof. exact (fun h0 : term0 _142951 _142953 g => @lem8057160 _142951 _142952 _142953 f g h1 h0). Qed.
Lemma lem8057162 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term0 _142951 _142952 f) (h2 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : (term1 _142951 _142952 _142953 f g) = (term4 _142951 _142952 _142953 f).
Proof. exact (EQ_MP (@lem8049688 _142951 _142952 _142953 f g h2) (@lem8051509 _142951 _142952 _142953 f g h1 h2)). Qed.
Lemma lem8057163 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term0 _142951 _142952 f) (h2 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : (g = (@EMPTY ((cart _142951 _142953) -> Prop))) = ((term1 _142951 _142952 _142953 f g) = (term4 _142951 _142952 _142953 f)).
Proof. exact (prop_ext (fun h3 : g = (@EMPTY ((cart _142951 _142953) -> Prop)) => @lem8057162 _142951 _142952 _142953 f g h1 h2) (fun h3 : (term1 _142951 _142952 _142953 f g) = (term4 _142951 _142952 _142953 f) => @lem8048932 _142951 _142953 g h2)). Qed.
Lemma lem8057164 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term0 _142951 _142952 f) (h2 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : (term1 _142951 _142952 _142953 f g) = (term4 _142951 _142952 _142953 f).
Proof. exact (EQ_MP (@lem8057163 _142951 _142952 _142953 f g h1 h2) (@lem8048932 _142951 _142953 g h2)). Qed.
Lemma lem8057165 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term0 _142951 _142952 f) : term5 _142951 _142952 _142953 g f.
Proof. exact (fun h0 : g = (@EMPTY ((cart _142951 _142953) -> Prop)) => @lem8057164 _142951 _142952 _142953 f g h1 h0). Qed.
Lemma lem8057166 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term0 _142951 _142952 f) : term6 _142951 _142952 _142953 f g.
Proof. exact (conj (@lem8057165 _142951 _142952 _142953 g f h1) (@lem8057161 _142951 _142952 _142953 g f h1)). Qed.
Lemma lem8057170 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term0 _142951 _142952 f) : (term1 _142951 _142952 _142953 f g) = (term7 _142951 _142952 _142953 f g).
Proof. exact (EQ_MP (@lem8048931 _142951 _142952 _142953 f g) (@lem8057166 _142951 _142952 _142953 g f h1)). Qed.
Lemma lem8057171 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term0 _142951 _142952 f) : (term0 _142951 _142952 f) = ((term1 _142951 _142952 _142953 f g) = (term7 _142951 _142952 _142953 f g)).
Proof. exact (prop_ext (fun h2 : term0 _142951 _142952 f => @lem8057170 _142951 _142952 _142953 g f h1) (fun h2 : (term1 _142951 _142952 _142953 f g) = (term7 _142951 _142952 _142953 f g) => @lem8048867 _142951 _142952 f h1)). Qed.
Lemma lem8057172 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term0 _142951 _142952 f) : (term1 _142951 _142952 _142953 f g) = (term7 _142951 _142952 _142953 f g).
Proof. exact (EQ_MP (@lem8057171 _142951 _142952 _142953 g f h1) (@lem8048867 _142951 _142952 f h1)). Qed.
Lemma lem8057173 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term8 _142951 _142952 _142953 f g.
Proof. exact (fun h0 : term0 _142951 _142952 f => @lem8057172 _142951 _142952 _142953 g f h0). Qed.
Lemma lem8057174 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : (term1 _142951 _142952 _142953 f g) = (term9 _142951 _142952 _142953 g).
Proof. exact (EQ_MP (@lem8049396 _142951 _142952 _142953 g f h1) (@lem8051187 _142951 _142952 _142953 g f h1)). Qed.
Lemma lem8057175 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : (f = (@EMPTY ((cart _142951 _142952) -> Prop))) = ((term1 _142951 _142952 _142953 f g) = (term9 _142951 _142952 _142953 g)).
Proof. exact (prop_ext (fun h2 : f = (@EMPTY ((cart _142951 _142952) -> Prop)) => @lem8057174 _142951 _142952 _142953 g f h1) (fun h2 : (term1 _142951 _142952 _142953 f g) = (term9 _142951 _142952 _142953 g) => @lem8048850 _142951 _142952 f h1)). Qed.
Lemma lem8057176 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : (term1 _142951 _142952 _142953 f g) = (term9 _142951 _142952 _142953 g).
Proof. exact (EQ_MP (@lem8057175 _142951 _142952 _142953 g f h1) (@lem8048850 _142951 _142952 f h1)). Qed.
Lemma lem8057177 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term10 _142951 _142952 _142953 f g.
Proof. exact (fun h0 : f = (@EMPTY ((cart _142951 _142952) -> Prop)) => @lem8057176 _142951 _142952 _142953 g f h0). Qed.
Lemma lem8057178 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term11 _142951 _142952 _142953 f g.
Proof. exact (conj (@lem8057177 _142951 _142952 _142953 f g) (@lem8057173 _142951 _142952 _142953 f g)). Qed.
Lemma lem8057179 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term1 _142951 _142952 _142953 f g) = (term12 _142951 _142952 _142953 f g).
Proof. exact (EQ_MP (@lem8048849 _142951 _142952 _142953 f g) (@lem8057178 _142951 _142952 _142953 f g)). Qed.
