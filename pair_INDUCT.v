Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import pair_INDUCT_term_abbrevs.
Require Import PAIR_spec.
Lemma lem48083 {A B : Type'} (x : prod A B) (h1 : (term0 A B x) = x) : (term0 A B x) = x.
Proof. exact (h1). Qed.
Lemma lem48084 {A B : Type'} (x : prod A B) (h1 : (term0 A B x) = x) : x = (term0 A B x).
Proof. exact (SYM (@lem48083 A B x h1)). Qed.
Lemma lem48085 {A B : Type'} (x : prod A B) (h1 : x = (term0 A B x)) : x = (term0 A B x).
Proof. exact (h1). Qed.
Lemma lem48086 {A B : Type'} (x : prod A B) (h1 : x = (term0 A B x)) : (term0 A B x) = x.
Proof. exact (SYM (@lem48085 A B x h1)). Qed.
Lemma lem48087 {A B : Type'} (x : prod A B) : ((term0 A B x) = x) = (x = (term0 A B x)).
Proof. exact (prop_ext (fun h1 : (term0 A B x) = x => @lem48084 A B x h1) (fun h1 : x = (term0 A B x) => @lem48086 A B x h1)). Qed.
Lemma lem48088 {A B : Type'} : (term1 A B) = (term2 A B).
Proof. exact (fun_ext (fun x : prod A B => @lem48087 A B x)). Qed.
Lemma lem48089 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem48090 {A B : Type'} : (term3 A B) = (term4 A B).
Proof. exact (MK_COMB (@lem48089 A B) (@lem48088 A B)). Qed.
Lemma lem48091 {A B : Type'} : term4 A B.
Proof. exact (EQ_MP (@lem48090 A B) (@lem48081 A B)). Qed.
Lemma lem48092 {A B : Type'} (x : prod A B) : term5 A B x.
Proof. exact (@lem48091 A B x). Qed.
Lemma lem48093 {A B : Type'} (x : prod A B) : (term5 A B x) = (x = (term0 A B x)).
Proof. exact (eq_refl (term5 A B x)). Qed.
Lemma lem48095 {_4949 _4950 : Type'} (P : type1223 _4949 _4950) (h1 : term6 _4949 _4950 P) : term6 _4949 _4950 P.
Proof. exact (h1). Qed.
Lemma lem48097 {A B : Type'} (x : prod A B) : x = (term0 A B x).
Proof. exact (EQ_MP (@lem48093 A B x) (@lem48092 A B x)). Qed.
Lemma lem48098 {_4949 _4950 : Type'} (x : prod _4950 _4949) : x = (term7 _4949 _4950 x).
Proof. exact (@lem48097 _4950 _4949 x). Qed.
Lemma lem48099 {_4949 _4950 : Type'} (p : prod _4950 _4949) : p = (term7 _4949 _4950 p).
Proof. exact (@lem48098 _4949 _4950 p). Qed.
Lemma lem48100 {_4949 _4950 : Type'} (P : type1223 _4949 _4950) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem48101 {_4949 _4950 : Type'} (P : type1223 _4949 _4950) (p : prod _4950 _4949) : (P p) = (term8 _4949 _4950 P p).
Proof. exact (MK_COMB (@lem48100 _4949 _4950 P) (@lem48099 _4949 _4950 p)). Qed.
Lemma lem48102 {_4949 _4950 : Type'} (P : type1223 _4949 _4950) (p : prod _4950 _4949) : (term8 _4949 _4950 P p) = (P p).
Proof. exact (SYM (@lem48101 _4949 _4950 P p)). Qed.
Lemma lem48103 {_4949 _4950 : Type'} (x : _4950) (P : type1223 _4949 _4950) (h1 : term6 _4949 _4950 P) : term9 _4949 _4950 P x.
Proof. exact (@lem48095 _4949 _4950 P h1 x). Qed.
Lemma lem48104 {_4949 _4950 : Type'} (P : type1223 _4949 _4950) (x : _4950) : (term9 _4949 _4950 P x) = (term10 _4949 _4950 P x).
Proof. exact (eq_refl (term9 _4949 _4950 P x)). Qed.
Lemma lem48105 {_4949 _4950 : Type'} (x : _4950) (P : type1223 _4949 _4950) (h1 : term6 _4949 _4950 P) : term10 _4949 _4950 P x.
Proof. exact (EQ_MP (@lem48104 _4949 _4950 P x) (@lem48103 _4949 _4950 x P h1)). Qed.
Lemma lem48106 {_4949 _4950 : Type'} (x : _4950) (y : _4949) (P : type1223 _4949 _4950) (h1 : term6 _4949 _4950 P) : term11 _4949 _4950 P x y.
Proof. exact (@lem48105 _4949 _4950 x P h1 y). Qed.
Lemma lem48107 {_4949 _4950 : Type'} (P : type1223 _4949 _4950) (x : _4950) (y : _4949) : (term11 _4949 _4950 P x y) = (term12 _4949 _4950 P x y).
Proof. exact (eq_refl (term11 _4949 _4950 P x y)). Qed.
Lemma lem48110 {_4949 _4950 : Type'} (x : _4950) (y : _4949) (P : type1223 _4949 _4950) (h1 : term6 _4949 _4950 P) : term12 _4949 _4950 P x y.
Proof. exact (EQ_MP (@lem48107 _4949 _4950 P x y) (@lem48106 _4949 _4950 x y P h1)). Qed.
Lemma lem48111 {_4949 _4950 : Type'} (x : _4950) (y : _4949) (P : type1223 _4949 _4950) (h1 : term6 _4949 _4950 P) : term12 _4949 _4950 P x y.
Proof. exact (@lem48110 _4949 _4950 x y P h1). Qed.
Lemma lem48112 {_4949 _4950 : Type'} (p : prod _4950 _4949) (P : type1223 _4949 _4950) (h1 : term6 _4949 _4950 P) : term8 _4949 _4950 P p.
Proof. exact (@lem48111 _4949 _4950 (@fst _4950 _4949 p) (@snd _4950 _4949 p) P h1). Qed.
Lemma lem48113 {_4949 _4950 : Type'} (p : prod _4950 _4949) (P : type1223 _4949 _4950) (h1 : term6 _4949 _4950 P) : P p.
Proof. exact (EQ_MP (@lem48102 _4949 _4950 P p) (@lem48112 _4949 _4950 p P h1)). Qed.
Lemma lem48118 {_4949 _4950 : Type'} (P : type1223 _4949 _4950) (h1 : term6 _4949 _4950 P) : term13 _4949 _4950 P.
Proof. exact (fun p : prod _4950 _4949 => @lem48113 _4949 _4950 p P h1). Qed.
Lemma lem48119 {_4949 _4950 : Type'} (P : type1223 _4949 _4950) (h1 : term6 _4949 _4950 P) : (term6 _4949 _4950 P) = (term13 _4949 _4950 P).
Proof. exact (prop_ext (fun h2 : term6 _4949 _4950 P => @lem48118 _4949 _4950 P h1) (fun h2 : term13 _4949 _4950 P => @lem48095 _4949 _4950 P h1)). Qed.
Lemma lem48120 {_4949 _4950 : Type'} (P : type1223 _4949 _4950) (h1 : term6 _4949 _4950 P) : term13 _4949 _4950 P.
Proof. exact (EQ_MP (@lem48119 _4949 _4950 P h1) (@lem48095 _4949 _4950 P h1)). Qed.
Lemma lem48121 {_4949 _4950 : Type'} (P : type1223 _4949 _4950) : term14 _4949 _4950 P.
Proof. exact (fun h0 : term6 _4949 _4950 P => @lem48120 _4949 _4950 P h0). Qed.
Lemma lem48126 {_4949 _4950 : Type'} : term15 _4949 _4950.
Proof. exact (fun P : type1223 _4949 _4950 => @lem48121 _4949 _4950 P). Qed.
