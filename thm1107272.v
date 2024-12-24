Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1107272_term_abbrevs.
Require Import thm1106843_spec.
Require Import thm1107225_spec.
Lemma lem1107226 {_25617 _25623 : Type'} : (term0 _25617 _25623) = (term1 _25617 _25623).
Proof. exact (eq_refl (term0 _25617 _25623)). Qed.
Lemma lem1107227 {_25617 _25623 : Type'} : term1 _25617 _25623.
Proof. exact (EQ_MP (@lem1107226 _25617 _25623) (@lem1106843 _25617 _25623)). Qed.
Lemma lem1107228 {_25617 _25623 : Type'} : term2 _25617 _25623.
Proof. exact (@lem1107227 _25617 _25623 term3). Qed.
Lemma lem1107229 {_25617 _25623 : Type'} : (term2 _25617 _25623) = (term4 _25617 _25623).
Proof. exact (eq_refl (term2 _25617 _25623)). Qed.
Lemma lem1107230 {_25617 _25623 : Type'} : term4 _25617 _25623.
Proof. exact (EQ_MP (@lem1107229 _25617 _25623) (@lem1107228 _25617 _25623)). Qed.
Lemma lem1107231 {_25617 _25623 : Type'} (h1 : (@ASSOC _25617 _25623) = (term5 _25617 _25623)) : (@ASSOC _25617 _25623) = (term5 _25617 _25623).
Proof. exact (h1). Qed.
Lemma lem1107232 {_25617 _25623 : Type'} (h1 : (@ASSOC _25617 _25623) = (term5 _25617 _25623)) : (term5 _25617 _25623) = (@ASSOC _25617 _25623).
Proof. exact (SYM (@lem1107231 _25617 _25623 h1)). Qed.
Lemma lem1107233 {_25617 _25623 : Type'} (h1 : (term5 _25617 _25623) = (@ASSOC _25617 _25623)) : (term5 _25617 _25623) = (@ASSOC _25617 _25623).
Proof. exact (h1). Qed.
Lemma lem1107234 {_25617 _25623 : Type'} (h1 : (term5 _25617 _25623) = (@ASSOC _25617 _25623)) : (@ASSOC _25617 _25623) = (term5 _25617 _25623).
Proof. exact (SYM (@lem1107233 _25617 _25623 h1)). Qed.
Lemma lem1107235 {_25617 _25623 : Type'} : ((@ASSOC _25617 _25623) = (term5 _25617 _25623)) = ((term5 _25617 _25623) = (@ASSOC _25617 _25623)).
Proof. exact (prop_ext (fun h1 : (@ASSOC _25617 _25623) = (term5 _25617 _25623) => @lem1107232 _25617 _25623 h1) (fun h1 : (term5 _25617 _25623) = (@ASSOC _25617 _25623) => @lem1107234 _25617 _25623 h1)). Qed.
Lemma lem1107238 {_25617 _25623 : Type'} : (term5 _25617 _25623) = (@ASSOC _25617 _25623).
Proof. exact (EQ_MP (@lem1107235 _25617 _25623) (@lem1107225 _25617 _25623)). Qed.
Lemma lem1107239 {_25617 _25623 : Type'} : (term5 _25617 _25623) = (@ASSOC _25617 _25623).
Proof. exact (@lem1107238 _25617 _25623). Qed.
Lemma lem1107240 {_25623 : Type'} (a : _25623) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1107241 {_25617 _25623 : Type'} (a : _25623) : (term6 _25617 _25623 a) = (@ASSOC _25617 _25623 a).
Proof. exact (MK_COMB (@lem1107239 _25617 _25623) (@lem1107240 _25623 a)). Qed.
Lemma lem1107242 {_25617 _25623 : Type'} (h : prod _25623 _25617) (t : type1641 _25617 _25623) : (@cons (prod _25623 _25617) h t) = (@cons (prod _25623 _25617) h t).
Proof. exact (eq_refl (@cons (prod _25623 _25617) h t)). Qed.
Lemma lem1107243 {_25617 _25623 : Type'} (a : _25623) (h : prod _25623 _25617) (t : type1641 _25617 _25623) : (term7 _25617 _25623 a h t) = (term8 _25617 _25623 a h t).
Proof. exact (MK_COMB (@lem1107241 _25617 _25623 a) (@lem1107242 _25617 _25623 h t)). Qed.
Lemma lem1107244 {_25617 : Type'} : (@eq _25617) = (@eq _25617).
Proof. exact (eq_refl (@eq _25617)). Qed.
Lemma lem1107245 {_25617 _25623 : Type'} (a : _25623) (h : prod _25623 _25617) (t : type1641 _25617 _25623) : (term9 _25617 _25623 a h t) = (term10 _25617 _25623 a h t).
Proof. exact (MK_COMB (@lem1107244 _25617) (@lem1107243 _25617 _25623 a h t)). Qed.
Lemma lem1107247 {_25617 _25623 : Type'} : (term5 _25617 _25623) = (@ASSOC _25617 _25623).
Proof. exact (EQ_MP (@lem1107235 _25617 _25623) (@lem1107225 _25617 _25623)). Qed.
Lemma lem1107248 {_25617 _25623 : Type'} : (term5 _25617 _25623) = (@ASSOC _25617 _25623).
Proof. exact (@lem1107247 _25617 _25623). Qed.
Lemma lem1107249 {_25623 : Type'} (a : _25623) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1107250 {_25617 _25623 : Type'} (a : _25623) : (term6 _25617 _25623 a) = (@ASSOC _25617 _25623 a).
Proof. exact (MK_COMB (@lem1107248 _25617 _25623) (@lem1107249 _25623 a)). Qed.
Lemma lem1107251 {_25617 _25623 : Type'} (t : type1641 _25617 _25623) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1107252 {_25617 _25623 : Type'} (a : _25623) (t : type1641 _25617 _25623) : (term11 _25617 _25623 a t) = (@ASSOC _25617 _25623 a t).
Proof. exact (MK_COMB (@lem1107250 _25617 _25623 a) (@lem1107251 _25617 _25623 t)). Qed.
Lemma lem1107253 {_25617 _25623 : Type'} (a : _25623) (h : prod _25623 _25617) : (term12 _25617 _25623 a h) = (term12 _25617 _25623 a h).
Proof. exact (eq_refl (term12 _25617 _25623 a h)). Qed.
Lemma lem1107254 {_25617 _25623 : Type'} (h : prod _25623 _25617) (a : _25623) (t : type1641 _25617 _25623) : (term13 _25617 _25623 h a t) = (term14 _25617 _25623 h a t).
Proof. exact (MK_COMB (@lem1107253 _25617 _25623 a h) (@lem1107252 _25617 _25623 a t)). Qed.
Lemma lem1107255 {_25617 _25623 : Type'} (h : prod _25623 _25617) (a : _25623) (t : type1641 _25617 _25623) : ((term7 _25617 _25623 a h t) = (term13 _25617 _25623 h a t)) = ((term8 _25617 _25623 a h t) = (term14 _25617 _25623 h a t)).
Proof. exact (MK_COMB (@lem1107245 _25617 _25623 a h t) (@lem1107254 _25617 _25623 h a t)). Qed.
Lemma lem1107256 {_25617 _25623 : Type'} (h : prod _25623 _25617) (a : _25623) : (term15 _25617 _25623 h a) = (term16 _25617 _25623 h a).
Proof. exact (fun_ext (fun t : type1641 _25617 _25623 => @lem1107255 _25617 _25623 h a t)). Qed.
Lemma lem1107257 {_25617 _25623 : Type'} : (@all (list (prod _25623 _25617))) = (@all (list (prod _25623 _25617))).
Proof. exact (eq_refl (@all (list (prod _25623 _25617)))). Qed.
Lemma lem1107258 {_25617 _25623 : Type'} (h : prod _25623 _25617) (a : _25623) : (term17 _25617 _25623 h a) = (term18 _25617 _25623 h a).
Proof. exact (MK_COMB (@lem1107257 _25617 _25623) (@lem1107256 _25617 _25623 h a)). Qed.
Lemma lem1107259 {_25617 _25623 : Type'} (h : prod _25623 _25617) : (term19 _25617 _25623 h) = (term20 _25617 _25623 h).
Proof. exact (fun_ext (fun a : _25623 => @lem1107258 _25617 _25623 h a)). Qed.
Lemma lem1107260 {_25623 : Type'} : (@all _25623) = (@all _25623).
Proof. exact (eq_refl (@all _25623)). Qed.
Lemma lem1107261 {_25617 _25623 : Type'} (h : prod _25623 _25617) : (term21 _25617 _25623 h) = (term22 _25617 _25623 h).
Proof. exact (MK_COMB (@lem1107260 _25623) (@lem1107259 _25617 _25623 h)). Qed.
Lemma lem1107262 {_25617 _25623 : Type'} : (term23 _25617 _25623) = (term24 _25617 _25623).
Proof. exact (fun_ext (fun h : prod _25623 _25617 => @lem1107261 _25617 _25623 h)). Qed.
Lemma lem1107263 {_25617 _25623 : Type'} : (@all (prod _25623 _25617)) = (@all (prod _25623 _25617)).
Proof. exact (eq_refl (@all (prod _25623 _25617))). Qed.
Lemma lem1107264 {_25617 _25623 : Type'} : (term4 _25617 _25623) = (term25 _25617 _25623).
Proof. exact (MK_COMB (@lem1107263 _25617 _25623) (@lem1107262 _25617 _25623)). Qed.
Lemma lem1107265 {_25617 _25623 : Type'} : term25 _25617 _25623.
Proof. exact (EQ_MP (@lem1107264 _25617 _25623) (@lem1107230 _25617 _25623)). Qed.
Lemma lem1107266 {_25617 _25623 : Type'} (h : prod _25623 _25617) : term26 _25617 _25623 h.
Proof. exact (@lem1107265 _25617 _25623 h). Qed.
Lemma lem1107267 {_25617 _25623 : Type'} (h : prod _25623 _25617) : (term26 _25617 _25623 h) = (term22 _25617 _25623 h).
Proof. exact (eq_refl (term26 _25617 _25623 h)). Qed.
Lemma lem1107268 {_25617 _25623 : Type'} (h : prod _25623 _25617) : term22 _25617 _25623 h.
Proof. exact (EQ_MP (@lem1107267 _25617 _25623 h) (@lem1107266 _25617 _25623 h)). Qed.
Lemma lem1107269 {_25617 _25623 : Type'} (h : prod _25623 _25617) (a : _25623) : term27 _25617 _25623 h a.
Proof. exact (@lem1107268 _25617 _25623 h a). Qed.
Lemma lem1107270 {_25617 _25623 : Type'} (h : prod _25623 _25617) (a : _25623) : (term27 _25617 _25623 h a) = (term18 _25617 _25623 h a).
Proof. exact (eq_refl (term27 _25617 _25623 h a)). Qed.
Lemma lem1107271 {_25617 _25623 : Type'} (h : prod _25623 _25617) (a : _25623) : term18 _25617 _25623 h a.
Proof. exact (EQ_MP (@lem1107270 _25617 _25623 h a) (@lem1107269 _25617 _25623 h a)). Qed.
Lemma lem1107272 {_25617 _25623 : Type'} (h : prod _25623 _25617) (a : _25623) (t : type1641 _25617 _25623) : term28 _25617 _25623 h a t.
Proof. exact (@lem1107271 _25617 _25623 h a t). Qed.
