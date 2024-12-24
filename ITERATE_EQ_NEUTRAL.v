Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_EQ_NEUTRAL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import FINITE_RULES_spec.
Require Import IN_SUPPORT_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import ITERATE_SUPPORT_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19024_spec.
Require Import thm19025_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
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
Require Import thm69_spec.
Lemma lem5783476 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5783477 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) : term0 A B s f op.
Proof. exact (h1). Qed.
Lemma lem5783478 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : (@support A B op f s) = (@EMPTY A)) : (@support A B op f s) = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5783480 (p : Prop) : p = (term1 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5783481 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : ((@support A B op f s) = (@EMPTY A)) = (term2 A B op f s).
Proof. exact (@lem5783480 ((@support A B op f s) = (@EMPTY A))). Qed.
Lemma lem5783482 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term2 A B op f s) = ((@support A B op f s) = (@EMPTY A)).
Proof. exact (SYM (@lem5783481 A B op f s)). Qed.
Lemma lem5783483 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term3 A B op f s) : term3 A B op f s.
Proof. exact (h1). Qed.
Lemma lem5783484 {A : Type'} : term4 A.
Proof. exact (@lem3181245 A). Qed.
Lemma lem5783486 {A : Type'} : term5 A.
Proof. exact (@lem3204775 A). Qed.
Lemma lem5783488 {_119826 A : Type'} : term6 _119826 A.
Proof. exact (@lem5718201 _119826 A). Qed.
Lemma lem5783489 {A B : Type'} : term7 A B.
Proof. exact (@lem5718201 B A). Qed.
Lemma lem5783490 {_119829 B : Type'} : term7 _119829 B.
Proof. exact (@lem5718201 B _119829). Qed.
Lemma lem5783491 {_119829 A : Type'} : term8 _119829 A.
Proof. exact (@lem5718201 (A -> Prop) _119829). Qed.
Lemma lem5783495 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term9 _119826 _119829 A B op f s) : term9 _119826 _119829 A B op f s.
Proof. exact (h1). Qed.
Lemma lem5783496 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : term10 _119826 _119829 A B op f s.
Proof. exact (fun h0 : term9 _119826 _119829 A B op f s => @lem5783495 _119826 _119829 A B op f s h0). Qed.
Lemma lem5783497 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term10 _119826 _119829 A B op f s) : term10 _119826 _119829 A B op f s.
Proof. exact (h1). Qed.
Lemma lem5783498 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term9 _119826 _119829 A B op f s) : term9 _119826 _119829 A B op f s.
Proof. exact (h1). Qed.
Lemma lem5783499 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term9 _119826 _119829 A B op f s) (h2 : term10 _119826 _119829 A B op f s) : term9 _119826 _119829 A B op f s.
Proof. exact (@lem5783497 _119826 _119829 A B op f s h2 (@lem5783498 _119826 _119829 A B op f s h1)). Qed.
Lemma lem5783500 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term9 _119826 _119829 A B op f s) : term11 _119826 _119829 A B op f s.
Proof. exact (fun h0 : term10 _119826 _119829 A B op f s => @lem5783499 _119826 _119829 A B op f s h1 h0). Qed.
Lemma lem5783501 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term10 _119826 _119829 A B op f s) : term10 _119826 _119829 A B op f s.
Proof. exact (h1). Qed.
Lemma lem5783502 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term9 _119826 _119829 A B op f s) (h2 : term10 _119826 _119829 A B op f s) : term9 _119826 _119829 A B op f s.
Proof. exact (@lem5783500 _119826 _119829 A B op f s h1 (@lem5783501 _119826 _119829 A B op f s h2)). Qed.
Lemma lem5783503 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term10 _119826 _119829 A B op f s) : term10 _119826 _119829 A B op f s.
Proof. exact (fun h0 : term9 _119826 _119829 A B op f s => @lem5783502 _119826 _119829 A B op f s h0 h1). Qed.
Lemma lem5783504 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : term12 _119826 _119829 A B op f s.
Proof. exact (fun h0 : term10 _119826 _119829 A B op f s => @lem5783503 _119826 _119829 A B op f s h0). Qed.
Lemma lem5783507 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : term10 _119826 _119829 A B op f s.
Proof. exact (@lem5783504 _119826 _119829 A B op f s (@lem5783496 _119826 _119829 A B op f s)). Qed.
Lemma lem5783508 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : term10 _119826 _119829 A B op f s.
Proof. exact (@lem5783507 _119826 _119829 A B op f s). Qed.
Lemma lem5783620 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5783621 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (@lem5783620 (term4 A)). Qed.
Lemma lem5783634 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (eq_refl (term15 A)). Qed.
Lemma lem5783635 {A : Type'} : (term16 A) = (term17 A).
Proof. exact (MK_COMB (@lem5783634 A) (@lem5783621 A)). Qed.
Lemma lem5783638 {_119829 A : Type'} : (term18 _119829 A) = (term18 _119829 A).
Proof. exact (eq_refl (term18 _119829 A)). Qed.
Lemma lem5783639 {_119829 A : Type'} : (term19 _119829 A) = (term20 _119829 A).
Proof. exact (MK_COMB (@lem5783638 _119829 A) (@lem5783635 A)). Qed.
Lemma lem5783642 {A B : Type'} : (term21 A B) = (term21 A B).
Proof. exact (eq_refl (term21 A B)). Qed.
Lemma lem5783643 {_119829 A B : Type'} : (term22 _119829 A B) = (term23 _119829 A B).
Proof. exact (MK_COMB (@lem5783642 A B) (@lem5783639 _119829 A)). Qed.
Lemma lem5783646 {_119829 B : Type'} : (term21 _119829 B) = (term21 _119829 B).
Proof. exact (eq_refl (term21 _119829 B)). Qed.
Lemma lem5783647 {_119829 A B : Type'} : (term24 _119829 A B) = (term25 _119829 A B).
Proof. exact (MK_COMB (@lem5783646 _119829 B) (@lem5783643 _119829 A B)). Qed.
Lemma lem5783650 {_119826 A : Type'} : (term26 _119826 A) = (term26 _119826 A).
Proof. exact (eq_refl (term26 _119826 A)). Qed.
Lemma lem5783651 {_119826 _119829 A B : Type'} : (term27 _119826 _119829 A B) = (term28 _119826 _119829 A B).
Proof. exact (MK_COMB (@lem5783650 _119826 A) (@lem5783647 _119829 A B)). Qed.
Lemma lem5783654 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term29 A B op f s) = (term29 A B op f s).
Proof. exact (eq_refl (term29 A B op f s)). Qed.
Lemma lem5783655 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term30 _119826 _119829 A B op f s) = (term31 _119826 _119829 A B op f s).
Proof. exact (MK_COMB (@lem5783654 A B op f s) (@lem5783651 _119826 _119829 A B)). Qed.
Lemma lem5783658 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term32 A B s f op) = (term32 A B s f op).
Proof. exact (eq_refl (term32 A B s f op)). Qed.
Lemma lem5783659 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term33 _119826 _119829 A B op f s) = (term34 _119826 _119829 A B op f s).
Proof. exact (MK_COMB (@lem5783658 A B s f op) (@lem5783655 _119826 _119829 A B op f s)). Qed.
Lemma lem5783662 {B : Type'} (op : type1400 B) : (term35 B op) = (term35 B op).
Proof. exact (eq_refl (term35 B op)). Qed.
Lemma lem5783663 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term9 _119826 _119829 A B op f s) = (term36 _119826 _119829 A B op f s).
Proof. exact (MK_COMB (@lem5783662 B op) (@lem5783659 _119826 _119829 A B op f s)). Qed.
Lemma lem5783666 {_119826 _119829 A B : Type'} (f : A -> B) (s : A -> Prop) : (term37 _119826 _119829 A B f s) = (term38 _119826 _119829 A B f s).
Proof. exact (fun_ext (fun op : type1400 B => @lem5783663 _119826 _119829 A B op f s)). Qed.
Lemma lem5783667 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5783668 {_119826 _119829 A B : Type'} (f : A -> B) (s : A -> Prop) : (term39 _119826 _119829 A B f s) = (term40 _119826 _119829 A B f s).
Proof. exact (MK_COMB (@lem5783667 B) (@lem5783666 _119826 _119829 A B f s)). Qed.
Lemma lem5783673 {_119826 _119829 A B : Type'} (s : A -> Prop) : (term41 _119826 _119829 A B s) = (term42 _119826 _119829 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem5783668 _119826 _119829 A B f s)). Qed.
Lemma lem5783674 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5783675 {_119826 _119829 A B : Type'} (s : A -> Prop) : (term43 _119826 _119829 A B s) = (term44 _119826 _119829 A B s).
Proof. exact (MK_COMB (@lem5783674 A B) (@lem5783673 _119826 _119829 A B s)). Qed.
Lemma lem5783680 {_119826 _119829 A B : Type'} : (term45 _119826 _119829 A B) = (term46 _119826 _119829 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5783675 _119826 _119829 A B s)). Qed.
Lemma lem5783681 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5783690 {_119826 _119829 A B : Type'} : (term47 _119826 _119829 A B) = (term48 _119826 _119829 A B).
Proof. exact (MK_COMB (@lem5783681 A) (@lem5783680 _119826 _119829 A B)). Qed.
Lemma lem5783695 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((@IN A x s) = (@IN A x t)) = ((@IN A x s) = (@IN A x t)).
Proof. exact (eq_refl ((@IN A x s) = (@IN A x t))). Qed.
Lemma lem5783696 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term49 A s t) = (term49 A s t).
Proof. exact (fun_ext (fun x : A => @lem5783695 A s x t)). Qed.
Lemma lem5783697 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5783698 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term50 A s t).
Proof. exact (MK_COMB (@lem5783697 A) (@lem5783696 A s t)). Qed.
Lemma lem5783701 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term51 A s t) = (term51 A s t).
Proof. exact (eq_refl (term51 A s t)). Qed.
Lemma lem5783702 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((s = t) = (term50 A s t)) = ((s = t) = (term50 A s t)).
Proof. exact (MK_COMB (@lem5783701 A s t) (@lem5783698 A s t)). Qed.
Lemma lem5783703 {A : Type'} (s : A -> Prop) : (term52 A s) = (term52 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5783702 A s t)). Qed.
Lemma lem5783704 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5783705 {A : Type'} (s : A -> Prop) : (term53 A s) = (term53 A s).
Proof. exact (MK_COMB (@lem5783704 A) (@lem5783703 A s)). Qed.
Lemma lem5783706 {A : Type'} : (term54 A) = (term54 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5783705 A s)). Qed.
Lemma lem5783707 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5783708 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (MK_COMB (@lem5783707 A) (@lem5783706 A)). Qed.
Lemma lem5783709 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5783710 {A : Type'} : (term14 A) = (term14 A).
Proof. exact (MK_COMB (@lem5783709) (@lem5783708 A)). Qed.
Lemma lem5783713 {A : Type'} (x : A) : (term55 A x) = (term55 A x).
Proof. exact (eq_refl (term55 A x)). Qed.
Lemma lem5783714 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (fun_ext (fun x : A => @lem5783713 A x)). Qed.
Lemma lem5783715 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5783716 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (MK_COMB (@lem5783715 A) (@lem5783714 A)). Qed.
Lemma lem5783717 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5783718 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (MK_COMB (@lem5783717) (@lem5783716 A)). Qed.
Lemma lem5783719 {A : Type'} : (term17 A) = (term17 A).
Proof. exact (MK_COMB (@lem5783718 A) (@lem5783710 A)). Qed.
Lemma lem5783730 {_119829 A : Type'} (s : _119829 -> Prop) (f : type1413 _119829 A) (x : _119829) (op : type636 A) : ((term57 _119829 A x op f s) = (term58 _119829 A s f x op)) = ((term57 _119829 A x op f s) = (term58 _119829 A s f x op)).
Proof. exact (eq_refl ((term57 _119829 A x op f s) = (term58 _119829 A s f x op))). Qed.
Lemma lem5783731 {_119829 A : Type'} (f : type1413 _119829 A) (x : _119829) (op : type636 A) : (term59 _119829 A f x op) = (term59 _119829 A f x op).
Proof. exact (fun_ext (fun s : _119829 -> Prop => @lem5783730 _119829 A s f x op)). Qed.
Lemma lem5783732 {_119829 : Type'} : (@all (_119829 -> Prop)) = (@all (_119829 -> Prop)).
Proof. exact (eq_refl (@all (_119829 -> Prop))). Qed.
Lemma lem5783733 {_119829 A : Type'} (f : type1413 _119829 A) (x : _119829) (op : type636 A) : (term60 _119829 A f x op) = (term60 _119829 A f x op).
Proof. exact (MK_COMB (@lem5783732 _119829) (@lem5783731 _119829 A f x op)). Qed.
Lemma lem5783734 {_119829 A : Type'} (f : type1413 _119829 A) (op : type636 A) : (term61 _119829 A f op) = (term61 _119829 A f op).
Proof. exact (fun_ext (fun x : _119829 => @lem5783733 _119829 A f x op)). Qed.
Lemma lem5783735 {_119829 : Type'} : (@all _119829) = (@all _119829).
Proof. exact (eq_refl (@all _119829)). Qed.
Lemma lem5783736 {_119829 A : Type'} (f : type1413 _119829 A) (op : type636 A) : (term62 _119829 A f op) = (term62 _119829 A f op).
Proof. exact (MK_COMB (@lem5783735 _119829) (@lem5783734 _119829 A f op)). Qed.
Lemma lem5783737 {_119829 A : Type'} (op : type636 A) : (term63 _119829 A op) = (term63 _119829 A op).
Proof. exact (fun_ext (fun f : type1413 _119829 A => @lem5783736 _119829 A f op)). Qed.
Lemma lem5783738 {_119829 A : Type'} : (@all (_119829 -> A -> Prop)) = (@all (_119829 -> A -> Prop)).
Proof. exact (eq_refl (@all (_119829 -> A -> Prop))). Qed.
Lemma lem5783739 {_119829 A : Type'} (op : type636 A) : (term64 _119829 A op) = (term64 _119829 A op).
Proof. exact (MK_COMB (@lem5783738 _119829 A) (@lem5783737 _119829 A op)). Qed.
Lemma lem5783740 {_119829 A : Type'} : (term65 _119829 A) = (term65 _119829 A).
Proof. exact (fun_ext (fun op : type636 A => @lem5783739 _119829 A op)). Qed.
Lemma lem5783741 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem5783742 {_119829 A : Type'} : (term8 _119829 A) = (term8 _119829 A).
Proof. exact (MK_COMB (@lem5783741 A) (@lem5783740 _119829 A)). Qed.
Lemma lem5783743 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5783744 {_119829 A : Type'} : (term18 _119829 A) = (term18 _119829 A).
Proof. exact (MK_COMB (@lem5783743) (@lem5783742 _119829 A)). Qed.
Lemma lem5783745 {_119829 A : Type'} : (term20 _119829 A) = (term20 _119829 A).
Proof. exact (MK_COMB (@lem5783744 _119829 A) (@lem5783719 A)). Qed.
Lemma lem5783756 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term66 A B x op f s) = (term67 A B s f x op)) = ((term66 A B x op f s) = (term67 A B s f x op)).
Proof. exact (eq_refl ((term66 A B x op f s) = (term67 A B s f x op))). Qed.
Lemma lem5783757 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term68 A B f x op) = (term68 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5783756 A B s f x op)). Qed.
Lemma lem5783758 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5783759 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term69 A B f x op) = (term69 A B f x op).
Proof. exact (MK_COMB (@lem5783758 A) (@lem5783757 A B f x op)). Qed.
Lemma lem5783760 {A B : Type'} (f : A -> B) (op : type1400 B) : (term70 A B f op) = (term70 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5783759 A B f x op)). Qed.
Lemma lem5783761 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5783762 {A B : Type'} (f : A -> B) (op : type1400 B) : (term71 A B f op) = (term71 A B f op).
Proof. exact (MK_COMB (@lem5783761 A) (@lem5783760 A B f op)). Qed.
Lemma lem5783763 {A B : Type'} (op : type1400 B) : (term72 A B op) = (term72 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5783762 A B f op)). Qed.
Lemma lem5783764 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5783765 {A B : Type'} (op : type1400 B) : (term73 A B op) = (term73 A B op).
Proof. exact (MK_COMB (@lem5783764 A B) (@lem5783763 A B op)). Qed.
Lemma lem5783766 {A B : Type'} : (term74 A B) = (term74 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5783765 A B op)). Qed.
Lemma lem5783767 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5783768 {A B : Type'} : (term7 A B) = (term7 A B).
Proof. exact (MK_COMB (@lem5783767 B) (@lem5783766 A B)). Qed.
Lemma lem5783769 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5783770 {A B : Type'} : (term21 A B) = (term21 A B).
Proof. exact (MK_COMB (@lem5783769) (@lem5783768 A B)). Qed.
Lemma lem5783771 {_119829 A B : Type'} : (term23 _119829 A B) = (term23 _119829 A B).
Proof. exact (MK_COMB (@lem5783770 A B) (@lem5783745 _119829 A)). Qed.
Lemma lem5783782 {_119829 B : Type'} (s : _119829 -> Prop) (f : _119829 -> B) (x : _119829) (op : type1400 B) : ((term66 _119829 B x op f s) = (term67 _119829 B s f x op)) = ((term66 _119829 B x op f s) = (term67 _119829 B s f x op)).
Proof. exact (eq_refl ((term66 _119829 B x op f s) = (term67 _119829 B s f x op))). Qed.
Lemma lem5783783 {_119829 B : Type'} (f : _119829 -> B) (x : _119829) (op : type1400 B) : (term68 _119829 B f x op) = (term68 _119829 B f x op).
Proof. exact (fun_ext (fun s : _119829 -> Prop => @lem5783782 _119829 B s f x op)). Qed.
Lemma lem5783784 {_119829 : Type'} : (@all (_119829 -> Prop)) = (@all (_119829 -> Prop)).
Proof. exact (eq_refl (@all (_119829 -> Prop))). Qed.
Lemma lem5783785 {_119829 B : Type'} (f : _119829 -> B) (x : _119829) (op : type1400 B) : (term69 _119829 B f x op) = (term69 _119829 B f x op).
Proof. exact (MK_COMB (@lem5783784 _119829) (@lem5783783 _119829 B f x op)). Qed.
Lemma lem5783786 {_119829 B : Type'} (f : _119829 -> B) (op : type1400 B) : (term70 _119829 B f op) = (term70 _119829 B f op).
Proof. exact (fun_ext (fun x : _119829 => @lem5783785 _119829 B f x op)). Qed.
Lemma lem5783787 {_119829 : Type'} : (@all _119829) = (@all _119829).
Proof. exact (eq_refl (@all _119829)). Qed.
Lemma lem5783788 {_119829 B : Type'} (f : _119829 -> B) (op : type1400 B) : (term71 _119829 B f op) = (term71 _119829 B f op).
Proof. exact (MK_COMB (@lem5783787 _119829) (@lem5783786 _119829 B f op)). Qed.
Lemma lem5783789 {_119829 B : Type'} (op : type1400 B) : (term72 _119829 B op) = (term72 _119829 B op).
Proof. exact (fun_ext (fun f : _119829 -> B => @lem5783788 _119829 B f op)). Qed.
Lemma lem5783790 {_119829 B : Type'} : (@all (_119829 -> B)) = (@all (_119829 -> B)).
Proof. exact (eq_refl (@all (_119829 -> B))). Qed.
Lemma lem5783791 {_119829 B : Type'} (op : type1400 B) : (term73 _119829 B op) = (term73 _119829 B op).
Proof. exact (MK_COMB (@lem5783790 _119829 B) (@lem5783789 _119829 B op)). Qed.
Lemma lem5783792 {_119829 B : Type'} : (term74 _119829 B) = (term74 _119829 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5783791 _119829 B op)). Qed.
Lemma lem5783793 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5783794 {_119829 B : Type'} : (term7 _119829 B) = (term7 _119829 B).
Proof. exact (MK_COMB (@lem5783793 B) (@lem5783792 _119829 B)). Qed.
Lemma lem5783795 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5783796 {_119829 B : Type'} : (term21 _119829 B) = (term21 _119829 B).
Proof. exact (MK_COMB (@lem5783795) (@lem5783794 _119829 B)). Qed.
Lemma lem5783797 {_119829 A B : Type'} : (term25 _119829 A B) = (term25 _119829 A B).
Proof. exact (MK_COMB (@lem5783796 _119829 B) (@lem5783771 _119829 A B)). Qed.
Lemma lem5783808 {_119826 A : Type'} (s : A -> Prop) (f : A -> _119826) (x : A) (op : type1400 _119826) : ((term75 _119826 A x op f s) = (term76 _119826 A s f x op)) = ((term75 _119826 A x op f s) = (term76 _119826 A s f x op)).
Proof. exact (eq_refl ((term75 _119826 A x op f s) = (term76 _119826 A s f x op))). Qed.
Lemma lem5783809 {_119826 A : Type'} (f : A -> _119826) (x : A) (op : type1400 _119826) : (term77 _119826 A f x op) = (term77 _119826 A f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5783808 _119826 A s f x op)). Qed.
Lemma lem5783810 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5783811 {_119826 A : Type'} (f : A -> _119826) (x : A) (op : type1400 _119826) : (term78 _119826 A f x op) = (term78 _119826 A f x op).
Proof. exact (MK_COMB (@lem5783810 A) (@lem5783809 _119826 A f x op)). Qed.
Lemma lem5783812 {_119826 A : Type'} (f : A -> _119826) (op : type1400 _119826) : (term79 _119826 A f op) = (term79 _119826 A f op).
Proof. exact (fun_ext (fun x : A => @lem5783811 _119826 A f x op)). Qed.
Lemma lem5783813 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5783814 {_119826 A : Type'} (f : A -> _119826) (op : type1400 _119826) : (term80 _119826 A f op) = (term80 _119826 A f op).
Proof. exact (MK_COMB (@lem5783813 A) (@lem5783812 _119826 A f op)). Qed.
Lemma lem5783815 {_119826 A : Type'} (op : type1400 _119826) : (term81 _119826 A op) = (term81 _119826 A op).
Proof. exact (fun_ext (fun f : A -> _119826 => @lem5783814 _119826 A f op)). Qed.
Lemma lem5783816 {_119826 A : Type'} : (@all (A -> _119826)) = (@all (A -> _119826)).
Proof. exact (eq_refl (@all (A -> _119826))). Qed.
Lemma lem5783817 {_119826 A : Type'} (op : type1400 _119826) : (term82 _119826 A op) = (term82 _119826 A op).
Proof. exact (MK_COMB (@lem5783816 _119826 A) (@lem5783815 _119826 A op)). Qed.
Lemma lem5783818 {_119826 A : Type'} : (term83 _119826 A) = (term83 _119826 A).
Proof. exact (fun_ext (fun op : type1400 _119826 => @lem5783817 _119826 A op)). Qed.
Lemma lem5783819 {_119826 : Type'} : (@all (_119826 -> _119826 -> _119826)) = (@all (_119826 -> _119826 -> _119826)).
Proof. exact (eq_refl (@all (_119826 -> _119826 -> _119826))). Qed.
Lemma lem5783820 {_119826 A : Type'} : (term6 _119826 A) = (term6 _119826 A).
Proof. exact (MK_COMB (@lem5783819 _119826) (@lem5783818 _119826 A)). Qed.
Lemma lem5783821 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5783822 {_119826 A : Type'} : (term26 _119826 A) = (term26 _119826 A).
Proof. exact (MK_COMB (@lem5783821) (@lem5783820 _119826 A)). Qed.
Lemma lem5783823 {_119826 _119829 A B : Type'} : (term28 _119826 _119829 A B) = (term28 _119826 _119829 A B).
Proof. exact (MK_COMB (@lem5783822 _119826 A) (@lem5783797 _119829 A B)). Qed.
Lemma lem5783828 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term29 A B op f s) = (term29 A B op f s).
Proof. exact (eq_refl (term29 A B op f s)). Qed.
Lemma lem5783829 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term31 _119826 _119829 A B op f s) = (term31 _119826 _119829 A B op f s).
Proof. exact (MK_COMB (@lem5783828 A B op f s) (@lem5783823 _119826 _119829 A B)). Qed.
Lemma lem5783834 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term84 A B s f x op) = (term84 A B s f x op).
Proof. exact (eq_refl (term84 A B s f x op)). Qed.
Lemma lem5783835 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term85 A B s f op) = (term85 A B s f op).
Proof. exact (fun_ext (fun x : A => @lem5783834 A B s f x op)). Qed.
Lemma lem5783836 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5783837 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term0 A B s f op) = (term0 A B s f op).
Proof. exact (MK_COMB (@lem5783836 A) (@lem5783835 A B s f op)). Qed.
Lemma lem5783838 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5783839 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term32 A B s f op) = (term32 A B s f op).
Proof. exact (MK_COMB (@lem5783838) (@lem5783837 A B s f op)). Qed.
Lemma lem5783840 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term34 _119826 _119829 A B op f s) = (term34 _119826 _119829 A B op f s).
Proof. exact (MK_COMB (@lem5783839 A B s f op) (@lem5783829 _119826 _119829 A B op f s)). Qed.
Lemma lem5783843 {B : Type'} (op : type1400 B) : (term35 B op) = (term35 B op).
Proof. exact (eq_refl (term35 B op)). Qed.
Lemma lem5783844 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term36 _119826 _119829 A B op f s) = (term36 _119826 _119829 A B op f s).
Proof. exact (MK_COMB (@lem5783843 B op) (@lem5783840 _119826 _119829 A B op f s)). Qed.
Lemma lem5783845 {_119826 _119829 A B : Type'} (f : A -> B) (s : A -> Prop) : (term38 _119826 _119829 A B f s) = (term38 _119826 _119829 A B f s).
Proof. exact (fun_ext (fun op : type1400 B => @lem5783844 _119826 _119829 A B op f s)). Qed.
Lemma lem5783846 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5783847 {_119826 _119829 A B : Type'} (f : A -> B) (s : A -> Prop) : (term40 _119826 _119829 A B f s) = (term40 _119826 _119829 A B f s).
Proof. exact (MK_COMB (@lem5783846 B) (@lem5783845 _119826 _119829 A B f s)). Qed.
Lemma lem5783848 {_119826 _119829 A B : Type'} (s : A -> Prop) : (term42 _119826 _119829 A B s) = (term42 _119826 _119829 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem5783847 _119826 _119829 A B f s)). Qed.
Lemma lem5783849 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5783850 {_119826 _119829 A B : Type'} (s : A -> Prop) : (term44 _119826 _119829 A B s) = (term44 _119826 _119829 A B s).
Proof. exact (MK_COMB (@lem5783849 A B) (@lem5783848 _119826 _119829 A B s)). Qed.
Lemma lem5783851 {_119826 _119829 A B : Type'} : (term46 _119826 _119829 A B) = (term46 _119826 _119829 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5783850 _119826 _119829 A B s)). Qed.
Lemma lem5783852 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5783853 {_119826 _119829 A B : Type'} : (term48 _119826 _119829 A B) = (term48 _119826 _119829 A B).
Proof. exact (MK_COMB (@lem5783852 A) (@lem5783851 _119826 _119829 A B)). Qed.
Lemma lem5784026 {_119826 _119829 A B : Type'} : (term47 _119826 _119829 A B) = (term48 _119826 _119829 A B).
Proof. exact (TRANS (@lem5783690 _119826 _119829 A B) (@lem5783853 _119826 _119829 A B)). Qed.
Lemma lem5784027 {_119826 _119829 A B : Type'} : (term48 _119826 _119829 A B) = (term47 _119826 _119829 A B).
Proof. exact (SYM (@lem5784026 _119826 _119829 A B)). Qed.
Lemma lem5784029 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) : term0 A B s f op.
Proof. exact (h1). Qed.
Lemma lem5784033 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (h1). Qed.
Lemma lem5784035 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem5784036 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (h1). Qed.
Lemma lem5784049 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term84 A B s f x op) = (term86 A B s f x op).
Proof. exact (@lem17265 (@IN A x s) ((f x) = (@neutral B op))). Qed.
Lemma lem5784050 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term85 A B s f op) = (term87 A B s f op).
Proof. exact (fun_ext (fun x : A => @lem5784049 A B s f x op)). Qed.
Lemma lem5784051 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5784104 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term0 A B s f op) = (term88 A B s f op).
Proof. exact (MK_COMB (@lem5784051 A) (@lem5784050 A B s f op)). Qed.
Lemma lem5784105 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) : term88 A B s f op.
Proof. exact (EQ_MP (@lem5784104 A B s f op) (@lem5784029 A B s f op h1)). Qed.
Lemma lem5784111 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term3 A B op f s) : term3 A B op f s.
Proof. exact (h1). Qed.
Lemma lem5785333 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term89 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem16933 ((f x) = (@neutral B op))). Qed.
Lemma lem5785335 {A : Type'} (x : A) (s : A -> Prop) : (term90 A x s) = (term90 A x s).
Proof. exact (eq_refl (term90 A x s)). Qed.
Lemma lem5785336 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term91 A B s f x op) = (term86 A B s f x op).
Proof. exact (MK_COMB (@lem5785335 A x s) (@lem5785333 A B f x op)). Qed.
Lemma lem5785337 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term92 A B s f x op) = (term91 A B s f x op).
Proof. exact (@lem17045 (@IN A x s) (term93 A B f x op)). Qed.
Lemma lem5785338 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term92 A B s f x op) = (term86 A B s f x op).
Proof. exact (TRANS (@lem5785337 A B s f x op) (@lem5785336 A B s f x op)). Qed.
Lemma lem5785344 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term94 A B s f x op) = (term94 A B s f x op).
Proof. exact (eq_refl (term94 A B s f x op)). Qed.
Lemma lem5785346 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term95 A B x op f s) = (term95 A B x op f s).
Proof. exact (eq_refl (term95 A B x op f s)). Qed.
Lemma lem5785347 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term96 A B s f x op) = (term97 A B s f x op).
Proof. exact (MK_COMB (@lem5785346 A B x op f s) (@lem5785338 A B s f x op)). Qed.
Lemma lem5785348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5785349 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term98 A B s f x op) = (term99 A B s f x op).
Proof. exact (MK_COMB (@lem5785348) (@lem5785347 A B s f x op)). Qed.
Lemma lem5785350 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term100 A B s f x op) = (term101 A B s f x op).
Proof. exact (MK_COMB (@lem5785349 A B s f x op) (@lem5785344 A B s f x op)). Qed.
Lemma lem5785351 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term66 A B x op f s) = (term67 A B s f x op)) = (term100 A B s f x op).
Proof. exact (@lem17784 (term66 A B x op f s) (term67 A B s f x op)). Qed.
Lemma lem5785352 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term66 A B x op f s) = (term67 A B s f x op)) = (term101 A B s f x op).
Proof. exact (TRANS (@lem5785351 A B s f x op) (@lem5785350 A B s f x op)). Qed.
Lemma lem5785353 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term68 A B f x op) = (term102 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5785352 A B s f x op)). Qed.
Lemma lem5785354 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5785355 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term69 A B f x op) = (term103 A B f x op).
Proof. exact (MK_COMB (@lem5785354 A) (@lem5785353 A B f x op)). Qed.
Lemma lem5785356 {A B : Type'} (f : A -> B) (op : type1400 B) : (term70 A B f op) = (term104 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5785355 A B f x op)). Qed.
Lemma lem5785357 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5785358 {A B : Type'} (f : A -> B) (op : type1400 B) : (term71 A B f op) = (term105 A B f op).
Proof. exact (MK_COMB (@lem5785357 A) (@lem5785356 A B f op)). Qed.
Lemma lem5785359 {A B : Type'} (op : type1400 B) : (term72 A B op) = (term106 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5785358 A B f op)). Qed.
Lemma lem5785360 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5785361 {A B : Type'} (op : type1400 B) : (term73 A B op) = (term107 A B op).
Proof. exact (MK_COMB (@lem5785360 A B) (@lem5785359 A B op)). Qed.
Lemma lem5785362 {A B : Type'} : (term74 A B) = (term108 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5785361 A B op)). Qed.
Lemma lem5785363 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5785364 {A B : Type'} : (term7 A B) = (term109 A B).
Proof. exact (MK_COMB (@lem5785363 B) (@lem5785362 A B)). Qed.
Lemma lem5785378 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5785379 {A : Type'} (P : type686 A) (Q : type686 A) : (term112 A P Q) = (term113 A P Q).
Proof. exact (@lem5785378 (A -> Prop) P Q). Qed.
Lemma lem5785380 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term114 A B f x op) = (term115 A B f x op).
Proof. exact (@lem5785379 A (term116 A B f x op) (term117 A B f x op)). Qed.
Lemma lem5785381 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term118 A B f x op s) = (term97 A B s f x op).
Proof. exact (eq_refl (term118 A B f x op s)). Qed.
Lemma lem5785382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5785383 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term119 A B f x op s) = (term99 A B s f x op).
Proof. exact (MK_COMB (@lem5785382) (@lem5785381 A B s f x op)). Qed.
Lemma lem5785384 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term120 A B f x op s) = (term94 A B s f x op).
Proof. exact (eq_refl (term120 A B f x op s)). Qed.
Lemma lem5785385 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term121 A B f x op s) = (term101 A B s f x op).
Proof. exact (MK_COMB (@lem5785383 A B s f x op) (@lem5785384 A B s f x op)). Qed.
Lemma lem5785386 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term122 A B f x op) = (term102 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5785385 A B s f x op)). Qed.
Lemma lem5785387 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5785388 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term114 A B f x op) = (term103 A B f x op).
Proof. exact (MK_COMB (@lem5785387 A) (@lem5785386 A B f x op)). Qed.
Lemma lem5785389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5785390 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term123 A B f x op) = (term124 A B f x op).
Proof. exact (MK_COMB (@lem5785389) (@lem5785388 A B f x op)). Qed.
Lemma lem5785391 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term118 A B f x op s) = (term97 A B s f x op).
Proof. exact (eq_refl (term118 A B f x op s)). Qed.
Lemma lem5785392 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term125 A B f x op) = (term116 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5785391 A B s f x op)). Qed.
Lemma lem5785393 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5785394 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term126 A B f x op) = (term127 A B f x op).
Proof. exact (MK_COMB (@lem5785393 A) (@lem5785392 A B f x op)). Qed.
Lemma lem5785395 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5785396 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term128 A B f x op) = (term129 A B f x op).
Proof. exact (MK_COMB (@lem5785395) (@lem5785394 A B f x op)). Qed.
Lemma lem5785397 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term120 A B f x op s) = (term94 A B s f x op).
Proof. exact (eq_refl (term120 A B f x op s)). Qed.
Lemma lem5785398 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term130 A B f x op) = (term117 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5785397 A B s f x op)). Qed.
Lemma lem5785399 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5785400 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term131 A B f x op) = (term132 A B f x op).
Proof. exact (MK_COMB (@lem5785399 A) (@lem5785398 A B f x op)). Qed.
Lemma lem5785401 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term115 A B f x op) = (term133 A B f x op).
Proof. exact (MK_COMB (@lem5785396 A B f x op) (@lem5785400 A B f x op)). Qed.
Lemma lem5785402 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : ((term114 A B f x op) = (term115 A B f x op)) = ((term103 A B f x op) = (term133 A B f x op)).
Proof. exact (MK_COMB (@lem5785390 A B f x op) (@lem5785401 A B f x op)). Qed.
Lemma lem5785403 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term103 A B f x op) = (term133 A B f x op).
Proof. exact (EQ_MP (@lem5785402 A B f x op) (@lem5785380 A B f x op)). Qed.
Lemma lem5785500 {A B : Type'} (f : A -> B) (op : type1400 B) : (term104 A B f op) = (term134 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5785403 A B f x op)). Qed.
Lemma lem5785501 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5785502 {A B : Type'} (f : A -> B) (op : type1400 B) : (term105 A B f op) = (term135 A B f op).
Proof. exact (MK_COMB (@lem5785501 A) (@lem5785500 A B f op)). Qed.
Lemma lem5785504 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5785505 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (@lem5785504 A P Q). Qed.
Lemma lem5785506 {A B : Type'} (f : A -> B) (op : type1400 B) : (term136 A B f op) = (term137 A B f op).
Proof. exact (@lem5785505 A (term138 A B f op) (term139 A B f op)). Qed.
Lemma lem5785507 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term140 A B f op x) = (term127 A B f x op).
Proof. exact (eq_refl (term140 A B f op x)). Qed.
Lemma lem5785508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5785509 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term141 A B f op x) = (term129 A B f x op).
Proof. exact (MK_COMB (@lem5785508) (@lem5785507 A B f x op)). Qed.
Lemma lem5785510 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term142 A B f op x) = (term132 A B f x op).
Proof. exact (eq_refl (term142 A B f op x)). Qed.
Lemma lem5785511 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term143 A B f op x) = (term133 A B f x op).
Proof. exact (MK_COMB (@lem5785509 A B f x op) (@lem5785510 A B f x op)). Qed.
Lemma lem5785512 {A B : Type'} (f : A -> B) (op : type1400 B) : (term144 A B f op) = (term134 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5785511 A B f x op)). Qed.
Lemma lem5785513 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5785514 {A B : Type'} (f : A -> B) (op : type1400 B) : (term136 A B f op) = (term135 A B f op).
Proof. exact (MK_COMB (@lem5785513 A) (@lem5785512 A B f op)). Qed.
Lemma lem5785515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5785516 {A B : Type'} (f : A -> B) (op : type1400 B) : (term145 A B f op) = (term146 A B f op).
Proof. exact (MK_COMB (@lem5785515) (@lem5785514 A B f op)). Qed.
Lemma lem5785517 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term140 A B f op x) = (term127 A B f x op).
Proof. exact (eq_refl (term140 A B f op x)). Qed.
Lemma lem5785518 {A B : Type'} (f : A -> B) (op : type1400 B) : (term147 A B f op) = (term138 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5785517 A B f x op)). Qed.
Lemma lem5785519 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5785520 {A B : Type'} (f : A -> B) (op : type1400 B) : (term148 A B f op) = (term149 A B f op).
Proof. exact (MK_COMB (@lem5785519 A) (@lem5785518 A B f op)). Qed.
Lemma lem5785521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5785522 {A B : Type'} (f : A -> B) (op : type1400 B) : (term150 A B f op) = (term151 A B f op).
Proof. exact (MK_COMB (@lem5785521) (@lem5785520 A B f op)). Qed.
Lemma lem5785523 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term142 A B f op x) = (term132 A B f x op).
Proof. exact (eq_refl (term142 A B f op x)). Qed.
Lemma lem5785524 {A B : Type'} (f : A -> B) (op : type1400 B) : (term152 A B f op) = (term139 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5785523 A B f x op)). Qed.
Lemma lem5785525 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5785526 {A B : Type'} (f : A -> B) (op : type1400 B) : (term153 A B f op) = (term154 A B f op).
Proof. exact (MK_COMB (@lem5785525 A) (@lem5785524 A B f op)). Qed.
Lemma lem5785527 {A B : Type'} (f : A -> B) (op : type1400 B) : (term137 A B f op) = (term155 A B f op).
Proof. exact (MK_COMB (@lem5785522 A B f op) (@lem5785526 A B f op)). Qed.
Lemma lem5785528 {A B : Type'} (f : A -> B) (op : type1400 B) : ((term136 A B f op) = (term137 A B f op)) = ((term135 A B f op) = (term155 A B f op)).
Proof. exact (MK_COMB (@lem5785516 A B f op) (@lem5785527 A B f op)). Qed.
Lemma lem5785529 {A B : Type'} (f : A -> B) (op : type1400 B) : (term135 A B f op) = (term155 A B f op).
Proof. exact (EQ_MP (@lem5785528 A B f op) (@lem5785506 A B f op)). Qed.
Lemma lem5785634 {A B : Type'} (f : A -> B) (op : type1400 B) : (term105 A B f op) = (term155 A B f op).
Proof. exact (TRANS (@lem5785502 A B f op) (@lem5785529 A B f op)). Qed.
Lemma lem5785635 {A B : Type'} (op : type1400 B) : (term106 A B op) = (term156 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5785634 A B f op)). Qed.
Lemma lem5785636 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5785637 {A B : Type'} (op : type1400 B) : (term107 A B op) = (term157 A B op).
Proof. exact (MK_COMB (@lem5785636 A B) (@lem5785635 A B op)). Qed.
Lemma lem5785639 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5785640 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term158 A B P Q) = (term159 A B P Q).
Proof. exact (@lem5785639 (A -> B) P Q). Qed.
Lemma lem5785641 {A B : Type'} (op : type1400 B) : (term160 A B op) = (term161 A B op).
Proof. exact (@lem5785640 A B (term162 A B op) (term163 A B op)). Qed.
Lemma lem5785642 {A B : Type'} (f : A -> B) (op : type1400 B) : (term164 A B op f) = (term149 A B f op).
Proof. exact (eq_refl (term164 A B op f)). Qed.
Lemma lem5785643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5785644 {A B : Type'} (f : A -> B) (op : type1400 B) : (term165 A B op f) = (term151 A B f op).
Proof. exact (MK_COMB (@lem5785643) (@lem5785642 A B f op)). Qed.
Lemma lem5785645 {A B : Type'} (f : A -> B) (op : type1400 B) : (term166 A B op f) = (term154 A B f op).
Proof. exact (eq_refl (term166 A B op f)). Qed.
Lemma lem5785646 {A B : Type'} (f : A -> B) (op : type1400 B) : (term167 A B op f) = (term155 A B f op).
Proof. exact (MK_COMB (@lem5785644 A B f op) (@lem5785645 A B f op)). Qed.
Lemma lem5785647 {A B : Type'} (op : type1400 B) : (term168 A B op) = (term156 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5785646 A B f op)). Qed.
Lemma lem5785648 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5785649 {A B : Type'} (op : type1400 B) : (term160 A B op) = (term157 A B op).
Proof. exact (MK_COMB (@lem5785648 A B) (@lem5785647 A B op)). Qed.
Lemma lem5785650 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5785651 {A B : Type'} (op : type1400 B) : (term169 A B op) = (term170 A B op).
Proof. exact (MK_COMB (@lem5785650) (@lem5785649 A B op)). Qed.
Lemma lem5785652 {A B : Type'} (f : A -> B) (op : type1400 B) : (term164 A B op f) = (term149 A B f op).
Proof. exact (eq_refl (term164 A B op f)). Qed.
Lemma lem5785653 {A B : Type'} (op : type1400 B) : (term171 A B op) = (term162 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5785652 A B f op)). Qed.
Lemma lem5785654 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5785655 {A B : Type'} (op : type1400 B) : (term172 A B op) = (term173 A B op).
Proof. exact (MK_COMB (@lem5785654 A B) (@lem5785653 A B op)). Qed.
Lemma lem5785656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5785657 {A B : Type'} (op : type1400 B) : (term174 A B op) = (term175 A B op).
Proof. exact (MK_COMB (@lem5785656) (@lem5785655 A B op)). Qed.
Lemma lem5785658 {A B : Type'} (f : A -> B) (op : type1400 B) : (term166 A B op f) = (term154 A B f op).
Proof. exact (eq_refl (term166 A B op f)). Qed.
Lemma lem5785659 {A B : Type'} (op : type1400 B) : (term176 A B op) = (term163 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5785658 A B f op)). Qed.
Lemma lem5785660 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5785661 {A B : Type'} (op : type1400 B) : (term177 A B op) = (term178 A B op).
Proof. exact (MK_COMB (@lem5785660 A B) (@lem5785659 A B op)). Qed.
Lemma lem5785662 {A B : Type'} (op : type1400 B) : (term161 A B op) = (term179 A B op).
Proof. exact (MK_COMB (@lem5785657 A B op) (@lem5785661 A B op)). Qed.
Lemma lem5785663 {A B : Type'} (op : type1400 B) : ((term160 A B op) = (term161 A B op)) = ((term157 A B op) = (term179 A B op)).
Proof. exact (MK_COMB (@lem5785651 A B op) (@lem5785662 A B op)). Qed.
Lemma lem5785664 {A B : Type'} (op : type1400 B) : (term157 A B op) = (term179 A B op).
Proof. exact (EQ_MP (@lem5785663 A B op) (@lem5785641 A B op)). Qed.
Lemma lem5785777 {A B : Type'} (op : type1400 B) : (term107 A B op) = (term179 A B op).
Proof. exact (TRANS (@lem5785637 A B op) (@lem5785664 A B op)). Qed.
Lemma lem5785778 {A B : Type'} : (term108 A B) = (term180 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5785777 A B op)). Qed.
Lemma lem5785779 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5785780 {A B : Type'} : (term109 A B) = (term181 A B).
Proof. exact (MK_COMB (@lem5785779 B) (@lem5785778 A B)). Qed.
Lemma lem5785782 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5785783 {B : Type'} (P : type403 B) (Q : type403 B) : (term182 B P Q) = (term183 B P Q).
Proof. exact (@lem5785782 (type1400 B) P Q). Qed.
Lemma lem5785784 {A B : Type'} : (term184 A B) = (term185 A B).
Proof. exact (@lem5785783 B (term186 A B) (term187 A B)). Qed.
Lemma lem5785785 {A B : Type'} (op : type1400 B) : (term188 A B op) = (term173 A B op).
Proof. exact (eq_refl (term188 A B op)). Qed.
Lemma lem5785786 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5785787 {A B : Type'} (op : type1400 B) : (term189 A B op) = (term175 A B op).
Proof. exact (MK_COMB (@lem5785786) (@lem5785785 A B op)). Qed.
Lemma lem5785788 {A B : Type'} (op : type1400 B) : (term190 A B op) = (term178 A B op).
Proof. exact (eq_refl (term190 A B op)). Qed.
Lemma lem5785789 {A B : Type'} (op : type1400 B) : (term191 A B op) = (term179 A B op).
Proof. exact (MK_COMB (@lem5785787 A B op) (@lem5785788 A B op)). Qed.
Lemma lem5785790 {A B : Type'} : (term192 A B) = (term180 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5785789 A B op)). Qed.
Lemma lem5785791 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5785792 {A B : Type'} : (term184 A B) = (term181 A B).
Proof. exact (MK_COMB (@lem5785791 B) (@lem5785790 A B)). Qed.
Lemma lem5785793 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5785794 {A B : Type'} : (term193 A B) = (term194 A B).
Proof. exact (MK_COMB (@lem5785793) (@lem5785792 A B)). Qed.
Lemma lem5785795 {A B : Type'} (op : type1400 B) : (term188 A B op) = (term173 A B op).
Proof. exact (eq_refl (term188 A B op)). Qed.
Lemma lem5785796 {A B : Type'} : (term195 A B) = (term186 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5785795 A B op)). Qed.
Lemma lem5785797 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5785798 {A B : Type'} : (term196 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem5785797 B) (@lem5785796 A B)). Qed.
Lemma lem5785799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5785800 {A B : Type'} : (term198 A B) = (term199 A B).
Proof. exact (MK_COMB (@lem5785799) (@lem5785798 A B)). Qed.
Lemma lem5785801 {A B : Type'} (op : type1400 B) : (term190 A B op) = (term178 A B op).
Proof. exact (eq_refl (term190 A B op)). Qed.
Lemma lem5785802 {A B : Type'} : (term200 A B) = (term187 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5785801 A B op)). Qed.
Lemma lem5785803 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5785804 {A B : Type'} : (term201 A B) = (term202 A B).
Proof. exact (MK_COMB (@lem5785803 B) (@lem5785802 A B)). Qed.
Lemma lem5785805 {A B : Type'} : (term185 A B) = (term203 A B).
Proof. exact (MK_COMB (@lem5785800 A B) (@lem5785804 A B)). Qed.
Lemma lem5785806 {A B : Type'} : ((term184 A B) = (term185 A B)) = ((term181 A B) = (term203 A B)).
Proof. exact (MK_COMB (@lem5785794 A B) (@lem5785805 A B)). Qed.
Lemma lem5785807 {A B : Type'} : (term181 A B) = (term203 A B).
Proof. exact (EQ_MP (@lem5785806 A B) (@lem5785784 A B)). Qed.
Lemma lem5785930 {A B : Type'} : (term109 A B) = (term203 A B).
Proof. exact (TRANS (@lem5785780 A B) (@lem5785807 A B)). Qed.
Lemma lem5785931 {A B : Type'} : (term7 A B) = (term203 A B).
Proof. exact (TRANS (@lem5785364 A B) (@lem5785930 A B)). Qed.
Lemma lem5785932 {A B : Type'} (h1 : term7 A B) : term203 A B.
Proof. exact (EQ_MP (@lem5785931 A B) (@lem5784033 A B h1)). Qed.
Lemma lem5786540 {A : Type'} (x : A) : (term55 A x) = (term55 A x).
Proof. exact (eq_refl (term55 A x)). Qed.
Lemma lem5786541 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (fun_ext (fun x : A => @lem5786540 A x)). Qed.
Lemma lem5786542 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5786551 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (MK_COMB (@lem5786542 A) (@lem5786541 A)). Qed.
Lemma lem5786552 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (EQ_MP (@lem5786551 A) (@lem5784035 A h1)). Qed.
Lemma lem5786569 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term204 A s x t) = (term205 A s x t).
Proof. exact (@lem17930 (@IN A x s) (@IN A x t)). Qed.
Lemma lem5786580 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((@IN A x s) = (@IN A x t)) = (term206 A s x t).
Proof. exact (@lem17784 (@IN A x s) (@IN A x t)). Qed.
Lemma lem5786581 {A : Type'} (P : A -> Prop) : (term207 A P) = (term208 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5786582 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term209 A s t) = (term210 A s t).
Proof. exact (@lem5786581 A (term49 A s t)). Qed.
Lemma lem5786583 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term211 A s t x) = ((@IN A x s) = (@IN A x t)).
Proof. exact (eq_refl (term211 A s t x)). Qed.
Lemma lem5786584 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5786585 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term212 A s t x) = (term204 A s x t).
Proof. exact (MK_COMB (@lem5786584) (@lem5786583 A s x t)). Qed.
Lemma lem5786586 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term212 A s t x) = (term205 A s x t).
Proof. exact (TRANS (@lem5786585 A s x t) (@lem5786569 A s x t)). Qed.
Lemma lem5786587 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term213 A s t) = (term214 A s t).
Proof. exact (fun_ext (fun x : A => @lem5786586 A s x t)). Qed.
Lemma lem5786588 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5786589 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term210 A s t) = (term215 A s t).
Proof. exact (MK_COMB (@lem5786588 A) (@lem5786587 A s t)). Qed.
Lemma lem5786590 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term209 A s t) = (term215 A s t).
Proof. exact (TRANS (@lem5786582 A s t) (@lem5786589 A s t)). Qed.
Lemma lem5786591 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term49 A s t) = (term216 A s t).
Proof. exact (fun_ext (fun x : A => @lem5786580 A s x t)). Qed.
Lemma lem5786592 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5786593 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term217 A s t).
Proof. exact (MK_COMB (@lem5786592 A) (@lem5786591 A s t)). Qed.
Lemma lem5786595 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term218 A s t) = (term218 A s t).
Proof. exact (eq_refl (term218 A s t)). Qed.
Lemma lem5786596 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term219 A s t) = (term220 A s t).
Proof. exact (MK_COMB (@lem5786595 A s t) (@lem5786593 A s t)). Qed.
Lemma lem5786598 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term221 A s t) = (term221 A s t).
Proof. exact (eq_refl (term221 A s t)). Qed.
Lemma lem5786599 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term222 A s t) = (term223 A s t).
Proof. exact (MK_COMB (@lem5786598 A s t) (@lem5786590 A s t)). Qed.
Lemma lem5786600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5786601 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term224 A s t) = (term225 A s t).
Proof. exact (MK_COMB (@lem5786600) (@lem5786599 A s t)). Qed.
Lemma lem5786602 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term226 A s t) = (term227 A s t).
Proof. exact (MK_COMB (@lem5786601 A s t) (@lem5786596 A s t)). Qed.
Lemma lem5786603 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((s = t) = (term50 A s t)) = (term226 A s t).
Proof. exact (@lem17784 (s = t) (term50 A s t)). Qed.
Lemma lem5786604 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((s = t) = (term50 A s t)) = (term227 A s t).
Proof. exact (TRANS (@lem5786603 A s t) (@lem5786602 A s t)). Qed.
Lemma lem5786605 {A : Type'} (s : A -> Prop) : (term52 A s) = (term228 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5786604 A s t)). Qed.
Lemma lem5786606 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5786607 {A : Type'} (s : A -> Prop) : (term53 A s) = (term229 A s).
Proof. exact (MK_COMB (@lem5786606 A) (@lem5786605 A s)). Qed.
Lemma lem5786608 {A : Type'} : (term54 A) = (term230 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5786607 A s)). Qed.
Lemma lem5786609 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5786610 {A : Type'} : (term4 A) = (term231 A).
Proof. exact (MK_COMB (@lem5786609 A) (@lem5786608 A)). Qed.
Lemma lem5786616 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5786617 {A : Type'} (P : type686 A) (Q : type686 A) : (term112 A P Q) = (term113 A P Q).
Proof. exact (@lem5786616 (A -> Prop) P Q). Qed.
Lemma lem5786618 {A : Type'} (s : A -> Prop) : (term232 A s) = (term233 A s).
Proof. exact (@lem5786617 A (term234 A s) (term235 A s)). Qed.
Lemma lem5786619 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term236 A s t) = (term223 A s t).
Proof. exact (eq_refl (term236 A s t)). Qed.
Lemma lem5786620 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5786621 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term237 A s t) = (term225 A s t).
Proof. exact (MK_COMB (@lem5786620) (@lem5786619 A s t)). Qed.
Lemma lem5786622 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term238 A s t) = (term220 A s t).
Proof. exact (eq_refl (term238 A s t)). Qed.
Lemma lem5786623 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term239 A s t) = (term227 A s t).
Proof. exact (MK_COMB (@lem5786621 A s t) (@lem5786622 A s t)). Qed.
Lemma lem5786624 {A : Type'} (s : A -> Prop) : (term240 A s) = (term228 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5786623 A s t)). Qed.
Lemma lem5786625 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5786626 {A : Type'} (s : A -> Prop) : (term232 A s) = (term229 A s).
Proof. exact (MK_COMB (@lem5786625 A) (@lem5786624 A s)). Qed.
Lemma lem5786627 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5786628 {A : Type'} (s : A -> Prop) : (term241 A s) = (term242 A s).
Proof. exact (MK_COMB (@lem5786627) (@lem5786626 A s)). Qed.
Lemma lem5786629 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term236 A s t) = (term223 A s t).
Proof. exact (eq_refl (term236 A s t)). Qed.
Lemma lem5786630 {A : Type'} (s : A -> Prop) : (term243 A s) = (term234 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5786629 A s t)). Qed.
Lemma lem5786631 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5786632 {A : Type'} (s : A -> Prop) : (term244 A s) = (term245 A s).
Proof. exact (MK_COMB (@lem5786631 A) (@lem5786630 A s)). Qed.
Lemma lem5786633 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5786634 {A : Type'} (s : A -> Prop) : (term246 A s) = (term247 A s).
Proof. exact (MK_COMB (@lem5786633) (@lem5786632 A s)). Qed.
Lemma lem5786635 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term238 A s t) = (term220 A s t).
Proof. exact (eq_refl (term238 A s t)). Qed.
Lemma lem5786636 {A : Type'} (s : A -> Prop) : (term248 A s) = (term235 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5786635 A s t)). Qed.
Lemma lem5786637 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5786638 {A : Type'} (s : A -> Prop) : (term249 A s) = (term250 A s).
Proof. exact (MK_COMB (@lem5786637 A) (@lem5786636 A s)). Qed.
Lemma lem5786639 {A : Type'} (s : A -> Prop) : (term233 A s) = (term251 A s).
Proof. exact (MK_COMB (@lem5786634 A s) (@lem5786638 A s)). Qed.
Lemma lem5786640 {A : Type'} (s : A -> Prop) : ((term232 A s) = (term233 A s)) = ((term229 A s) = (term251 A s)).
Proof. exact (MK_COMB (@lem5786628 A s) (@lem5786639 A s)). Qed.
Lemma lem5786641 {A : Type'} (s : A -> Prop) : (term229 A s) = (term251 A s).
Proof. exact (EQ_MP (@lem5786640 A s) (@lem5786618 A s)). Qed.
Lemma lem5786787 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5786788 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (@lem5786787 A P Q). Qed.
Lemma lem5786789 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term252 A s t) = (term253 A s t).
Proof. exact (@lem5786788 A (term254 A s t) (term255 A s t)). Qed.
Lemma lem5786790 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term256 A s t x) = (term257 A s x t).
Proof. exact (eq_refl (term256 A s t x)). Qed.
Lemma lem5786791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5786792 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term258 A s t x) = (term259 A s x t).
Proof. exact (MK_COMB (@lem5786791) (@lem5786790 A s x t)). Qed.
Lemma lem5786793 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term260 A s t x) = (term261 A s x t).
Proof. exact (eq_refl (term260 A s t x)). Qed.
Lemma lem5786794 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term262 A s t x) = (term206 A s x t).
Proof. exact (MK_COMB (@lem5786792 A s x t) (@lem5786793 A s x t)). Qed.
Lemma lem5786795 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term263 A s t) = (term216 A s t).
Proof. exact (fun_ext (fun x : A => @lem5786794 A s x t)). Qed.
Lemma lem5786796 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5786797 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term252 A s t) = (term217 A s t).
Proof. exact (MK_COMB (@lem5786796 A) (@lem5786795 A s t)). Qed.
Lemma lem5786798 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5786799 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term264 A s t) = (term265 A s t).
Proof. exact (MK_COMB (@lem5786798) (@lem5786797 A s t)). Qed.
Lemma lem5786800 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term256 A s t x) = (term257 A s x t).
Proof. exact (eq_refl (term256 A s t x)). Qed.
Lemma lem5786801 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term266 A s t) = (term254 A s t).
Proof. exact (fun_ext (fun x : A => @lem5786800 A s x t)). Qed.
Lemma lem5786802 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5786803 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term267 A s t) = (term268 A s t).
Proof. exact (MK_COMB (@lem5786802 A) (@lem5786801 A s t)). Qed.
Lemma lem5786804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5786805 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term269 A s t) = (term270 A s t).
Proof. exact (MK_COMB (@lem5786804) (@lem5786803 A s t)). Qed.
Lemma lem5786806 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term260 A s t x) = (term261 A s x t).
Proof. exact (eq_refl (term260 A s t x)). Qed.
Lemma lem5786807 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term271 A s t) = (term255 A s t).
Proof. exact (fun_ext (fun x : A => @lem5786806 A s x t)). Qed.
Lemma lem5786808 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5786809 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term272 A s t) = (term273 A s t).
Proof. exact (MK_COMB (@lem5786808 A) (@lem5786807 A s t)). Qed.
Lemma lem5786810 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term253 A s t) = (term274 A s t).
Proof. exact (MK_COMB (@lem5786805 A s t) (@lem5786809 A s t)). Qed.
Lemma lem5786811 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term252 A s t) = (term253 A s t)) = ((term217 A s t) = (term274 A s t)).
Proof. exact (MK_COMB (@lem5786799 A s t) (@lem5786810 A s t)). Qed.
Lemma lem5786812 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term217 A s t) = (term274 A s t).
Proof. exact (EQ_MP (@lem5786811 A s t) (@lem5786789 A s t)). Qed.
Lemma lem5786909 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term218 A s t) = (term218 A s t).
Proof. exact (eq_refl (term218 A s t)). Qed.
Lemma lem5786910 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term220 A s t) = (term275 A s t).
Proof. exact (MK_COMB (@lem5786909 A s t) (@lem5786812 A s t)). Qed.
Lemma lem5786911 {A : Type'} (s : A -> Prop) : (term235 A s) = (term276 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5786910 A s t)). Qed.
Lemma lem5786912 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5786913 {A : Type'} (s : A -> Prop) : (term250 A s) = (term277 A s).
Proof. exact (MK_COMB (@lem5786912 A) (@lem5786911 A s)). Qed.
Lemma lem5786962 {A : Type'} (s : A -> Prop) : (term247 A s) = (term247 A s).
Proof. exact (eq_refl (term247 A s)). Qed.
Lemma lem5786963 {A : Type'} (s : A -> Prop) : (term251 A s) = (term278 A s).
Proof. exact (MK_COMB (@lem5786962 A s) (@lem5786913 A s)). Qed.
Lemma lem5786964 {A : Type'} (s : A -> Prop) : (term229 A s) = (term278 A s).
Proof. exact (TRANS (@lem5786641 A s) (@lem5786963 A s)). Qed.
Lemma lem5786965 {A : Type'} : (term230 A) = (term279 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5786964 A s)). Qed.
Lemma lem5786966 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5786967 {A : Type'} : (term231 A) = (term280 A).
Proof. exact (MK_COMB (@lem5786966 A) (@lem5786965 A)). Qed.
Lemma lem5786969 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5786970 {A : Type'} (P : type686 A) (Q : type686 A) : (term112 A P Q) = (term113 A P Q).
Proof. exact (@lem5786969 (A -> Prop) P Q). Qed.
Lemma lem5786971 {A : Type'} : (term281 A) = (term282 A).
Proof. exact (@lem5786970 A (term283 A) (term284 A)). Qed.
Lemma lem5786972 {A : Type'} (s : A -> Prop) : (term285 A s) = (term245 A s).
Proof. exact (eq_refl (term285 A s)). Qed.
Lemma lem5786973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5786974 {A : Type'} (s : A -> Prop) : (term286 A s) = (term247 A s).
Proof. exact (MK_COMB (@lem5786973) (@lem5786972 A s)). Qed.
Lemma lem5786975 {A : Type'} (s : A -> Prop) : (term287 A s) = (term277 A s).
Proof. exact (eq_refl (term287 A s)). Qed.
Lemma lem5786976 {A : Type'} (s : A -> Prop) : (term288 A s) = (term278 A s).
Proof. exact (MK_COMB (@lem5786974 A s) (@lem5786975 A s)). Qed.
Lemma lem5786977 {A : Type'} : (term289 A) = (term279 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5786976 A s)). Qed.
Lemma lem5786978 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5786979 {A : Type'} : (term281 A) = (term280 A).
Proof. exact (MK_COMB (@lem5786978 A) (@lem5786977 A)). Qed.
Lemma lem5786980 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5786981 {A : Type'} : (term290 A) = (term291 A).
Proof. exact (MK_COMB (@lem5786980) (@lem5786979 A)). Qed.
Lemma lem5786982 {A : Type'} (s : A -> Prop) : (term285 A s) = (term245 A s).
Proof. exact (eq_refl (term285 A s)). Qed.
Lemma lem5786983 {A : Type'} : (term292 A) = (term283 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5786982 A s)). Qed.
Lemma lem5786984 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5786985 {A : Type'} : (term293 A) = (term294 A).
Proof. exact (MK_COMB (@lem5786984 A) (@lem5786983 A)). Qed.
Lemma lem5786986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5786987 {A : Type'} : (term295 A) = (term296 A).
Proof. exact (MK_COMB (@lem5786986) (@lem5786985 A)). Qed.
Lemma lem5786988 {A : Type'} (s : A -> Prop) : (term287 A s) = (term277 A s).
Proof. exact (eq_refl (term287 A s)). Qed.
Lemma lem5786989 {A : Type'} : (term297 A) = (term284 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5786988 A s)). Qed.
Lemma lem5786990 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5786991 {A : Type'} : (term298 A) = (term299 A).
Proof. exact (MK_COMB (@lem5786990 A) (@lem5786989 A)). Qed.
Lemma lem5786992 {A : Type'} : (term282 A) = (term300 A).
Proof. exact (MK_COMB (@lem5786987 A) (@lem5786991 A)). Qed.
Lemma lem5786993 {A : Type'} : ((term281 A) = (term282 A)) = ((term280 A) = (term300 A)).
Proof. exact (MK_COMB (@lem5786981 A) (@lem5786992 A)). Qed.
Lemma lem5786994 {A : Type'} : (term280 A) = (term300 A).
Proof. exact (EQ_MP (@lem5786993 A) (@lem5786971 A)). Qed.
Lemma lem5787243 {A : Type'} : (term231 A) = (term300 A).
Proof. exact (TRANS (@lem5786967 A) (@lem5786994 A)). Qed.
Lemma lem5787245 {A : Type'} (P : Prop) (Q : A -> Prop) : (term301 A P Q) = (term302 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5787246 {A : Type'} (P : Prop) (Q : A -> Prop) : (term301 A P Q) = (term302 A P Q).
Proof. exact (@lem5787245 A P Q). Qed.
Lemma lem5787247 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term303 A s t) = (term304 A s t).
Proof. exact (@lem5787246 A (s = t) (term214 A s t)). Qed.
Lemma lem5787248 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term305 A s t x) = (term205 A s x t).
Proof. exact (eq_refl (term305 A s t x)). Qed.
Lemma lem5787249 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term306 A s t) = (term214 A s t).
Proof. exact (fun_ext (fun x : A => @lem5787248 A s x t)). Qed.
Lemma lem5787250 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5787251 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term307 A s t) = (term215 A s t).
Proof. exact (MK_COMB (@lem5787250 A) (@lem5787249 A s t)). Qed.
Lemma lem5787252 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term221 A s t) = (term221 A s t).
Proof. exact (eq_refl (term221 A s t)). Qed.
Lemma lem5787253 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term303 A s t) = (term223 A s t).
Proof. exact (MK_COMB (@lem5787252 A s t) (@lem5787251 A s t)). Qed.
Lemma lem5787254 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5787255 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term308 A s t) = (term309 A s t).
Proof. exact (MK_COMB (@lem5787254) (@lem5787253 A s t)). Qed.
Lemma lem5787256 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term305 A s t x) = (term205 A s x t).
Proof. exact (eq_refl (term305 A s t x)). Qed.
Lemma lem5787257 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term221 A s t) = (term221 A s t).
Proof. exact (eq_refl (term221 A s t)). Qed.
Lemma lem5787258 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term310 A s t x) = (term311 A s x t).
Proof. exact (MK_COMB (@lem5787257 A s t) (@lem5787256 A s x t)). Qed.
Lemma lem5787259 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term312 A s t) = (term313 A s t).
Proof. exact (fun_ext (fun x : A => @lem5787258 A s x t)). Qed.
Lemma lem5787260 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5787261 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term304 A s t) = (term314 A s t).
Proof. exact (MK_COMB (@lem5787260 A) (@lem5787259 A s t)). Qed.
Lemma lem5787262 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term303 A s t) = (term304 A s t)) = ((term223 A s t) = (term314 A s t)).
Proof. exact (MK_COMB (@lem5787255 A s t) (@lem5787261 A s t)). Qed.
Lemma lem5787263 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term223 A s t) = (term314 A s t).
Proof. exact (EQ_MP (@lem5787262 A s t) (@lem5787247 A s t)). Qed.
Lemma lem5787264 {A : Type'} (s : A -> Prop) : (term234 A s) = (term315 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5787263 A s t)). Qed.
Lemma lem5787265 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5787266 {A : Type'} (s : A -> Prop) : (term245 A s) = (term316 A s).
Proof. exact (MK_COMB (@lem5787265 A) (@lem5787264 A s)). Qed.
Lemma lem5787268 {A B : Type'} (P : type1413 A B) : (term317 A B P) = (term318 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5787269 {A : Type'} (P : type672 A) : (term319 A P) = (term320 A P).
Proof. exact (@lem5787268 (A -> Prop) A P). Qed.
Lemma lem5787270 {A : Type'} (s : A -> Prop) : (term321 A s) = (term322 A s).
Proof. exact (@lem5787269 A (term323 A s)). Qed.
Lemma lem5787271 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term324 A s t) = (term313 A s t).
Proof. exact (eq_refl (term324 A s t)). Qed.
Lemma lem5787272 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5787273 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term325 A s t x) = (term326 A s t x).
Proof. exact (MK_COMB (@lem5787271 A s t) (@lem5787272 A x)). Qed.
Lemma lem5787274 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term326 A s t x) = (term311 A s x t).
Proof. exact (eq_refl (term326 A s t x)). Qed.
Lemma lem5787275 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term325 A s t x) = (term311 A s x t).
Proof. exact (TRANS (@lem5787273 A s t x) (@lem5787274 A s x t)). Qed.
Lemma lem5787276 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term327 A s t) = (term313 A s t).
Proof. exact (fun_ext (fun x : A => @lem5787275 A s x t)). Qed.
Lemma lem5787277 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5787278 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term328 A s t) = (term314 A s t).
Proof. exact (MK_COMB (@lem5787277 A) (@lem5787276 A s t)). Qed.
Lemma lem5787279 {A : Type'} (s : A -> Prop) : (term329 A s) = (term315 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5787278 A s t)). Qed.
Lemma lem5787280 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5787281 {A : Type'} (s : A -> Prop) : (term321 A s) = (term316 A s).
Proof. exact (MK_COMB (@lem5787280 A) (@lem5787279 A s)). Qed.
Lemma lem5787282 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5787283 {A : Type'} (s : A -> Prop) : (term330 A s) = (term331 A s).
Proof. exact (MK_COMB (@lem5787282) (@lem5787281 A s)). Qed.
Lemma lem5787284 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term324 A s t) = (term313 A s t).
Proof. exact (eq_refl (term324 A s t)). Qed.
Lemma lem5787285 {A : Type'} (x : type684 A) (t : A -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem5787286 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term332 A s x t) = (term333 A s x t).
Proof. exact (MK_COMB (@lem5787284 A s t) (@lem5787285 A x t)). Qed.
Lemma lem5787287 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term333 A s x t) = (term334 A s x t).
Proof. exact (eq_refl (term333 A s x t)). Qed.
Lemma lem5787288 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term332 A s x t) = (term334 A s x t).
Proof. exact (TRANS (@lem5787286 A s x t) (@lem5787287 A s x t)). Qed.
Lemma lem5787289 {A : Type'} (s : A -> Prop) (x : type684 A) : (term335 A s x) = (term336 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5787288 A s x t)). Qed.
Lemma lem5787290 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5787291 {A : Type'} (s : A -> Prop) (x : type684 A) : (term337 A s x) = (term338 A s x).
Proof. exact (MK_COMB (@lem5787290 A) (@lem5787289 A s x)). Qed.
Lemma lem5787292 {A : Type'} (s : A -> Prop) : (term339 A s) = (term340 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem5787291 A s x)). Qed.
Lemma lem5787293 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem5787294 {A : Type'} (s : A -> Prop) : (term322 A s) = (term341 A s).
Proof. exact (MK_COMB (@lem5787293 A) (@lem5787292 A s)). Qed.
Lemma lem5787295 {A : Type'} (s : A -> Prop) : ((term321 A s) = (term322 A s)) = ((term316 A s) = (term341 A s)).
Proof. exact (MK_COMB (@lem5787283 A s) (@lem5787294 A s)). Qed.
Lemma lem5787296 {A : Type'} (s : A -> Prop) : (term316 A s) = (term341 A s).
Proof. exact (EQ_MP (@lem5787295 A s) (@lem5787270 A s)). Qed.
Lemma lem5787297 {A : Type'} (s : A -> Prop) : (term245 A s) = (term341 A s).
Proof. exact (TRANS (@lem5787266 A s) (@lem5787296 A s)). Qed.
Lemma lem5787298 {A : Type'} : (term283 A) = (term342 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5787297 A s)). Qed.
Lemma lem5787299 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5787300 {A : Type'} : (term294 A) = (term343 A).
Proof. exact (MK_COMB (@lem5787299 A) (@lem5787298 A)). Qed.
Lemma lem5787302 {A B : Type'} (P : type1413 A B) : (term317 A B P) = (term318 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5787303 {A : Type'} (P : type597 A) : (term344 A P) = (term345 A P).
Proof. exact (@lem5787302 (A -> Prop) (type684 A) P). Qed.
Lemma lem5787304 {A : Type'} : (term346 A) = (term347 A).
Proof. exact (@lem5787303 A (term348 A)). Qed.
Lemma lem5787305 {A : Type'} (s : A -> Prop) : (term349 A s) = (term340 A s).
Proof. exact (eq_refl (term349 A s)). Qed.
Lemma lem5787306 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5787307 {A : Type'} (s : A -> Prop) (x : type684 A) : (term350 A s x) = (term351 A s x).
Proof. exact (MK_COMB (@lem5787305 A s) (@lem5787306 A x)). Qed.
Lemma lem5787308 {A : Type'} (s : A -> Prop) (x : type684 A) : (term351 A s x) = (term338 A s x).
Proof. exact (eq_refl (term351 A s x)). Qed.
Lemma lem5787309 {A : Type'} (s : A -> Prop) (x : type684 A) : (term350 A s x) = (term338 A s x).
Proof. exact (TRANS (@lem5787307 A s x) (@lem5787308 A s x)). Qed.
Lemma lem5787310 {A : Type'} (s : A -> Prop) : (term352 A s) = (term340 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem5787309 A s x)). Qed.
Lemma lem5787311 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem5787312 {A : Type'} (s : A -> Prop) : (term353 A s) = (term341 A s).
Proof. exact (MK_COMB (@lem5787311 A) (@lem5787310 A s)). Qed.
Lemma lem5787313 {A : Type'} : (term354 A) = (term342 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5787312 A s)). Qed.
Lemma lem5787314 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5787315 {A : Type'} : (term346 A) = (term343 A).
Proof. exact (MK_COMB (@lem5787314 A) (@lem5787313 A)). Qed.
Lemma lem5787316 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5787317 {A : Type'} : (term355 A) = (term356 A).
Proof. exact (MK_COMB (@lem5787316) (@lem5787315 A)). Qed.
Lemma lem5787318 {A : Type'} (s : A -> Prop) : (term349 A s) = (term340 A s).
Proof. exact (eq_refl (term349 A s)). Qed.
Lemma lem5787319 {A : Type'} (x : type638 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5787320 {A : Type'} (x : type638 A) (s : A -> Prop) : (term357 A x s) = (term358 A x s).
Proof. exact (MK_COMB (@lem5787318 A s) (@lem5787319 A x s)). Qed.
Lemma lem5787321 {A : Type'} (x : type638 A) (s : A -> Prop) : (term358 A x s) = (term359 A x s).
Proof. exact (eq_refl (term358 A x s)). Qed.
Lemma lem5787322 {A : Type'} (x : type638 A) (s : A -> Prop) : (term357 A x s) = (term359 A x s).
Proof. exact (TRANS (@lem5787320 A x s) (@lem5787321 A x s)). Qed.
Lemma lem5787323 {A : Type'} (x : type638 A) : (term360 A x) = (term361 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5787322 A x s)). Qed.
Lemma lem5787324 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5787325 {A : Type'} (x : type638 A) : (term362 A x) = (term363 A x).
Proof. exact (MK_COMB (@lem5787324 A) (@lem5787323 A x)). Qed.
Lemma lem5787326 {A : Type'} : (term364 A) = (term365 A).
Proof. exact (fun_ext (fun x : type638 A => @lem5787325 A x)). Qed.
Lemma lem5787327 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem5787328 {A : Type'} : (term347 A) = (term366 A).
Proof. exact (MK_COMB (@lem5787327 A) (@lem5787326 A)). Qed.
Lemma lem5787329 {A : Type'} : ((term346 A) = (term347 A)) = ((term343 A) = (term366 A)).
Proof. exact (MK_COMB (@lem5787317 A) (@lem5787328 A)). Qed.
Lemma lem5787330 {A : Type'} : (term343 A) = (term366 A).
Proof. exact (EQ_MP (@lem5787329 A) (@lem5787304 A)). Qed.
Lemma lem5787331 {A : Type'} : (term294 A) = (term366 A).
Proof. exact (TRANS (@lem5787300 A) (@lem5787330 A)). Qed.
Lemma lem5787332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5787333 {A : Type'} : (term296 A) = (term367 A).
Proof. exact (MK_COMB (@lem5787332) (@lem5787331 A)). Qed.
Lemma lem5787334 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (eq_refl (term299 A)). Qed.
Lemma lem5787335 {A : Type'} : (term300 A) = (term368 A).
Proof. exact (MK_COMB (@lem5787333 A) (@lem5787334 A)). Qed.
Lemma lem5787337 {A : Type'} (P : A -> Prop) (Q : Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5787338 {A : Type'} (P : type139 A) (Q : Prop) : (term371 A P Q) = (term372 A P Q).
Proof. exact (@lem5787337 (type638 A) P Q). Qed.
Lemma lem5787339 {A : Type'} : (term373 A) = (term374 A).
Proof. exact (@lem5787338 A (term365 A) (term299 A)). Qed.
Lemma lem5787340 {A : Type'} (x : type638 A) : (term375 A x) = (term363 A x).
Proof. exact (eq_refl (term375 A x)). Qed.
Lemma lem5787341 {A : Type'} : (term376 A) = (term365 A).
Proof. exact (fun_ext (fun x : type638 A => @lem5787340 A x)). Qed.
Lemma lem5787342 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem5787343 {A : Type'} : (term377 A) = (term366 A).
Proof. exact (MK_COMB (@lem5787342 A) (@lem5787341 A)). Qed.
Lemma lem5787344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5787345 {A : Type'} : (term378 A) = (term367 A).
Proof. exact (MK_COMB (@lem5787344) (@lem5787343 A)). Qed.
Lemma lem5787346 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (eq_refl (term299 A)). Qed.
Lemma lem5787347 {A : Type'} : (term373 A) = (term368 A).
Proof. exact (MK_COMB (@lem5787345 A) (@lem5787346 A)). Qed.
Lemma lem5787348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5787349 {A : Type'} : (term379 A) = (term380 A).
Proof. exact (MK_COMB (@lem5787348) (@lem5787347 A)). Qed.
Lemma lem5787350 {A : Type'} (x : type638 A) : (term375 A x) = (term363 A x).
Proof. exact (eq_refl (term375 A x)). Qed.
Lemma lem5787351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5787352 {A : Type'} (x : type638 A) : (term381 A x) = (term382 A x).
Proof. exact (MK_COMB (@lem5787351) (@lem5787350 A x)). Qed.
Lemma lem5787353 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (eq_refl (term299 A)). Qed.
Lemma lem5787354 {A : Type'} (x : type638 A) : (term383 A x) = (term384 A x).
Proof. exact (MK_COMB (@lem5787352 A x) (@lem5787353 A)). Qed.
Lemma lem5787355 {A : Type'} : (term385 A) = (term386 A).
Proof. exact (fun_ext (fun x : type638 A => @lem5787354 A x)). Qed.
Lemma lem5787356 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem5787357 {A : Type'} : (term374 A) = (term387 A).
Proof. exact (MK_COMB (@lem5787356 A) (@lem5787355 A)). Qed.
Lemma lem5787358 {A : Type'} : ((term373 A) = (term374 A)) = ((term368 A) = (term387 A)).
Proof. exact (MK_COMB (@lem5787349 A) (@lem5787357 A)). Qed.
Lemma lem5787359 {A : Type'} : (term368 A) = (term387 A).
Proof. exact (EQ_MP (@lem5787358 A) (@lem5787339 A)). Qed.
Lemma lem5787360 {A : Type'} : (term300 A) = (term387 A).
Proof. exact (TRANS (@lem5787335 A) (@lem5787359 A)). Qed.
Lemma lem5787361 {A : Type'} : (term231 A) = (term387 A).
Proof. exact (TRANS (@lem5787243 A) (@lem5787360 A)). Qed.
Lemma lem5787362 {A : Type'} : (term4 A) = (term387 A).
Proof. exact (TRANS (@lem5786610 A) (@lem5787361 A)). Qed.
Lemma lem5787363 {A : Type'} (h1 : term4 A) : term387 A.
Proof. exact (EQ_MP (@lem5787362 A) (@lem5784036 A h1)). Qed.
Lemma lem5787364 {A : Type'} (x : type638 A) (h1 : term384 A x) : term384 A x.
Proof. exact (h1). Qed.
Lemma lem5787374 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5787379 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787381 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5787379 A B f x). Qed.
Lemma lem5787386 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787387 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5787386 (type1400 B) B f x). Qed.
Lemma lem5787389 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5787387 B (@neutral B) op). Qed.
Lemma lem5787390 {A B : Type'} (f : A -> B) (x : A) : (term388 A B f x) = (term389 A B f x).
Proof. exact (MK_COMB (@lem5787374 B) (@lem5787381 A B f x)). Qed.
Lemma lem5787391 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : ((f x) = (@neutral B op)) = ((@I (A -> B) f x) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem5787390 A B f x) (@lem5787389 B op)). Qed.
Lemma lem5787392 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5787399 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787400 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5787399 A (type686 A) f x). Qed.
Lemma lem5787401 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5787400 A (@IN A) x). Qed.
Lemma lem5787402 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5787403 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5787401 A x) (@lem5787402 A s)). Qed.
Lemma lem5787405 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787406 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5787405 (A -> Prop) Prop f x). Qed.
Lemma lem5787407 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term390 A x s).
Proof. exact (@lem5787406 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5787409 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term390 A x s).
Proof. exact (TRANS (@lem5787403 A x s) (@lem5787407 A x s)). Qed.
Lemma lem5787410 {A : Type'} (x : A) (s : A -> Prop) : (term391 A x s) = (term392 A x s).
Proof. exact (MK_COMB (@lem5787392) (@lem5787409 A x s)). Qed.
Lemma lem5787411 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5787412 {A : Type'} (x : A) (s : A -> Prop) : (term90 A x s) = (term393 A x s).
Proof. exact (MK_COMB (@lem5787411) (@lem5787410 A x s)). Qed.
Lemma lem5787413 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term86 A B s f x op) = (term394 A B s f x op).
Proof. exact (MK_COMB (@lem5787412 A x s) (@lem5787391 A B f x op)). Qed.
Lemma lem5787414 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term87 A B s f op) = (term395 A B s f op).
Proof. exact (fun_ext (fun x : A => @lem5787413 A B s f x op)). Qed.
Lemma lem5787415 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5787416 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term88 A B s f op) = (term396 A B s f op).
Proof. exact (MK_COMB (@lem5787415 A) (@lem5787414 A B s f op)). Qed.
Lemma lem5787417 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) : term396 A B s f op.
Proof. exact (EQ_MP (@lem5787416 A B s f op) (@lem5784105 A B s f op h1)). Qed.
Lemma lem5787418 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5787419 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem5787428 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787429 {A B : Type'} (f : type748 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5787428 (type1400 B) (type527 A B) f x). Qed.
Lemma lem5787430 {A B : Type'} (op : type1400 B) : (@support A B op) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op).
Proof. exact (@lem5787429 A B (@support A B) op). Qed.
Lemma lem5787431 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5787432 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f).
Proof. exact (MK_COMB (@lem5787430 A B op) (@lem5787431 A B f)). Qed.
Lemma lem5787434 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787435 {A B : Type'} (f : type527 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5787434 (A -> B) (type672 A) f x). Qed.
Lemma lem5787436 {A B : Type'} (op : type1400 B) (f : A -> B) : (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f) = (term397 A B op f).
Proof. exact (@lem5787435 A B (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op) f). Qed.
Lemma lem5787437 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (term397 A B op f).
Proof. exact (TRANS (@lem5787432 A B op f) (@lem5787436 A B op f)). Qed.
Lemma lem5787438 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5787439 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term398 A B op f s).
Proof. exact (MK_COMB (@lem5787437 A B op f) (@lem5787438 A s)). Qed.
Lemma lem5787441 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787442 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5787441 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem5787443 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term398 A B op f s) = (term399 A B op f s).
Proof. exact (@lem5787442 A (term397 A B op f) s). Qed.
Lemma lem5787445 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term399 A B op f s).
Proof. exact (TRANS (@lem5787439 A B op f s) (@lem5787443 A B op f s)). Qed.
Lemma lem5787446 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem5787447 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term400 A B op f s) = (term401 A B op f s).
Proof. exact (MK_COMB (@lem5787419 A) (@lem5787445 A B op f s)). Qed.
Lemma lem5787448 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : ((@support A B op f s) = (@EMPTY A)) = ((term399 A B op f s) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem5787447 A B op f s) (@lem5787446 A)). Qed.
Lemma lem5787449 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term3 A B op f s) = (term402 A B op f s).
Proof. exact (MK_COMB (@lem5787418) (@lem5787448 A B op f s)). Qed.
Lemma lem5787851 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5787852 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5787857 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787859 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5787857 A B f x). Qed.
Lemma lem5787864 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787865 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5787864 (type1400 B) B f x). Qed.
Lemma lem5787867 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5787865 B (@neutral B) op). Qed.
Lemma lem5787868 {A B : Type'} (f : A -> B) (x : A) : (term388 A B f x) = (term389 A B f x).
Proof. exact (MK_COMB (@lem5787852 B) (@lem5787859 A B f x)). Qed.
Lemma lem5787869 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : ((f x) = (@neutral B op)) = ((@I (A -> B) f x) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem5787868 A B f x) (@lem5787867 B op)). Qed.
Lemma lem5787870 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term93 A B f x op) = (term403 A B f x op).
Proof. exact (MK_COMB (@lem5787851) (@lem5787869 A B f x op)). Qed.
Lemma lem5787877 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787878 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5787877 A (type686 A) f x). Qed.
Lemma lem5787879 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5787878 A (@IN A) x). Qed.
Lemma lem5787880 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5787881 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5787879 A x) (@lem5787880 A s)). Qed.
Lemma lem5787883 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787884 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5787883 (A -> Prop) Prop f x). Qed.
Lemma lem5787885 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term390 A x s).
Proof. exact (@lem5787884 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5787887 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term390 A x s).
Proof. exact (TRANS (@lem5787881 A x s) (@lem5787885 A x s)). Qed.
Lemma lem5787888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5787889 {A : Type'} (x : A) (s : A -> Prop) : (term404 A x s) = (term405 A x s).
Proof. exact (MK_COMB (@lem5787888) (@lem5787887 A x s)). Qed.
Lemma lem5787890 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term67 A B s f x op) = (term406 A B s f x op).
Proof. exact (MK_COMB (@lem5787889 A x s) (@lem5787870 A B f x op)). Qed.
Lemma lem5787891 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5787902 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787903 {A B : Type'} (f : type748 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5787902 (type1400 B) (type527 A B) f x). Qed.
Lemma lem5787904 {A B : Type'} (op : type1400 B) : (@support A B op) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op).
Proof. exact (@lem5787903 A B (@support A B) op). Qed.
Lemma lem5787905 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5787906 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f).
Proof. exact (MK_COMB (@lem5787904 A B op) (@lem5787905 A B f)). Qed.
Lemma lem5787908 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787909 {A B : Type'} (f : type527 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5787908 (A -> B) (type672 A) f x). Qed.
Lemma lem5787910 {A B : Type'} (op : type1400 B) (f : A -> B) : (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f) = (term397 A B op f).
Proof. exact (@lem5787909 A B (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op) f). Qed.
Lemma lem5787911 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (term397 A B op f).
Proof. exact (TRANS (@lem5787906 A B op f) (@lem5787910 A B op f)). Qed.
Lemma lem5787912 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5787913 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term398 A B op f s).
Proof. exact (MK_COMB (@lem5787911 A B op f) (@lem5787912 A s)). Qed.
Lemma lem5787915 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787916 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5787915 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem5787917 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term398 A B op f s) = (term399 A B op f s).
Proof. exact (@lem5787916 A (term397 A B op f) s). Qed.
Lemma lem5787919 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term399 A B op f s).
Proof. exact (TRANS (@lem5787913 A B op f s) (@lem5787917 A B op f s)). Qed.
Lemma lem5787920 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5787921 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term66 A B x op f s) = (term407 A B x op f s).
Proof. exact (MK_COMB (@lem5787920 A x) (@lem5787919 A B op f s)). Qed.
Lemma lem5787923 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787924 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5787923 A (type686 A) f x). Qed.
Lemma lem5787925 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5787924 A (@IN A) x). Qed.
Lemma lem5787926 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term399 A B op f s) = (term399 A B op f s).
Proof. exact (eq_refl (term399 A B op f s)). Qed.
Lemma lem5787927 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term407 A B x op f s) = (term408 A B x op f s).
Proof. exact (MK_COMB (@lem5787925 A x) (@lem5787926 A B op f s)). Qed.
Lemma lem5787929 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787930 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5787929 (A -> Prop) Prop f x). Qed.
Lemma lem5787931 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term408 A B x op f s) = (term409 A B x op f s).
Proof. exact (@lem5787930 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) (term399 A B op f s)). Qed.
Lemma lem5787932 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term407 A B x op f s) = (term409 A B x op f s).
Proof. exact (TRANS (@lem5787927 A B x op f s) (@lem5787931 A B x op f s)). Qed.
Lemma lem5787933 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term66 A B x op f s) = (term409 A B x op f s).
Proof. exact (TRANS (@lem5787921 A B x op f s) (@lem5787932 A B x op f s)). Qed.
Lemma lem5787934 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term410 A B x op f s) = (term411 A B x op f s).
Proof. exact (MK_COMB (@lem5787891) (@lem5787933 A B x op f s)). Qed.
Lemma lem5787935 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5787936 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term412 A B x op f s) = (term413 A B x op f s).
Proof. exact (MK_COMB (@lem5787935) (@lem5787934 A B x op f s)). Qed.
Lemma lem5787937 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term94 A B s f x op) = (term414 A B s f x op).
Proof. exact (MK_COMB (@lem5787936 A B x op f s) (@lem5787890 A B s f x op)). Qed.
Lemma lem5787938 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term117 A B f x op) = (term415 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5787937 A B s f x op)). Qed.
Lemma lem5787939 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5787940 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term132 A B f x op) = (term416 A B f x op).
Proof. exact (MK_COMB (@lem5787939 A) (@lem5787938 A B f x op)). Qed.
Lemma lem5787941 {A B : Type'} (f : A -> B) (op : type1400 B) : (term139 A B f op) = (term417 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5787940 A B f x op)). Qed.
Lemma lem5787942 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5787943 {A B : Type'} (f : A -> B) (op : type1400 B) : (term154 A B f op) = (term418 A B f op).
Proof. exact (MK_COMB (@lem5787942 A) (@lem5787941 A B f op)). Qed.
Lemma lem5787944 {A B : Type'} (op : type1400 B) : (term163 A B op) = (term419 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5787943 A B f op)). Qed.
Lemma lem5787945 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5787946 {A B : Type'} (op : type1400 B) : (term178 A B op) = (term420 A B op).
Proof. exact (MK_COMB (@lem5787945 A B) (@lem5787944 A B op)). Qed.
Lemma lem5787947 {A B : Type'} : (term187 A B) = (term421 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5787946 A B op)). Qed.
Lemma lem5787948 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5787949 {A B : Type'} : (term202 A B) = (term422 A B).
Proof. exact (MK_COMB (@lem5787948 B) (@lem5787947 A B)). Qed.
Lemma lem5787950 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5787955 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787957 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5787955 A B f x). Qed.
Lemma lem5787962 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787963 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5787962 (type1400 B) B f x). Qed.
Lemma lem5787965 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5787963 B (@neutral B) op). Qed.
Lemma lem5787966 {A B : Type'} (f : A -> B) (x : A) : (term388 A B f x) = (term389 A B f x).
Proof. exact (MK_COMB (@lem5787950 B) (@lem5787957 A B f x)). Qed.
Lemma lem5787967 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : ((f x) = (@neutral B op)) = ((@I (A -> B) f x) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem5787966 A B f x) (@lem5787965 B op)). Qed.
Lemma lem5787968 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5787975 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787976 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5787975 A (type686 A) f x). Qed.
Lemma lem5787977 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5787976 A (@IN A) x). Qed.
Lemma lem5787978 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5787979 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5787977 A x) (@lem5787978 A s)). Qed.
Lemma lem5787981 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5787982 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5787981 (A -> Prop) Prop f x). Qed.
Lemma lem5787983 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term390 A x s).
Proof. exact (@lem5787982 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5787985 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term390 A x s).
Proof. exact (TRANS (@lem5787979 A x s) (@lem5787983 A x s)). Qed.
Lemma lem5787986 {A : Type'} (x : A) (s : A -> Prop) : (term391 A x s) = (term392 A x s).
Proof. exact (MK_COMB (@lem5787968) (@lem5787985 A x s)). Qed.
Lemma lem5787987 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5787988 {A : Type'} (x : A) (s : A -> Prop) : (term90 A x s) = (term393 A x s).
Proof. exact (MK_COMB (@lem5787987) (@lem5787986 A x s)). Qed.
Lemma lem5787989 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term86 A B s f x op) = (term394 A B s f x op).
Proof. exact (MK_COMB (@lem5787988 A x s) (@lem5787967 A B f x op)). Qed.
Lemma lem5788000 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788001 {A B : Type'} (f : type748 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5788000 (type1400 B) (type527 A B) f x). Qed.
Lemma lem5788002 {A B : Type'} (op : type1400 B) : (@support A B op) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op).
Proof. exact (@lem5788001 A B (@support A B) op). Qed.
Lemma lem5788003 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5788004 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f).
Proof. exact (MK_COMB (@lem5788002 A B op) (@lem5788003 A B f)). Qed.
Lemma lem5788006 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788007 {A B : Type'} (f : type527 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5788006 (A -> B) (type672 A) f x). Qed.
Lemma lem5788008 {A B : Type'} (op : type1400 B) (f : A -> B) : (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f) = (term397 A B op f).
Proof. exact (@lem5788007 A B (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op) f). Qed.
Lemma lem5788009 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (term397 A B op f).
Proof. exact (TRANS (@lem5788004 A B op f) (@lem5788008 A B op f)). Qed.
Lemma lem5788010 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5788011 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term398 A B op f s).
Proof. exact (MK_COMB (@lem5788009 A B op f) (@lem5788010 A s)). Qed.
Lemma lem5788013 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788014 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5788013 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem5788015 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term398 A B op f s) = (term399 A B op f s).
Proof. exact (@lem5788014 A (term397 A B op f) s). Qed.
Lemma lem5788017 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term399 A B op f s).
Proof. exact (TRANS (@lem5788011 A B op f s) (@lem5788015 A B op f s)). Qed.
Lemma lem5788018 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5788019 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term66 A B x op f s) = (term407 A B x op f s).
Proof. exact (MK_COMB (@lem5788018 A x) (@lem5788017 A B op f s)). Qed.
Lemma lem5788021 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788022 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5788021 A (type686 A) f x). Qed.
Lemma lem5788023 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5788022 A (@IN A) x). Qed.
Lemma lem5788024 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term399 A B op f s) = (term399 A B op f s).
Proof. exact (eq_refl (term399 A B op f s)). Qed.
Lemma lem5788025 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term407 A B x op f s) = (term408 A B x op f s).
Proof. exact (MK_COMB (@lem5788023 A x) (@lem5788024 A B op f s)). Qed.
Lemma lem5788027 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788028 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5788027 (A -> Prop) Prop f x). Qed.
Lemma lem5788029 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term408 A B x op f s) = (term409 A B x op f s).
Proof. exact (@lem5788028 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) (term399 A B op f s)). Qed.
Lemma lem5788030 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term407 A B x op f s) = (term409 A B x op f s).
Proof. exact (TRANS (@lem5788025 A B x op f s) (@lem5788029 A B x op f s)). Qed.
Lemma lem5788031 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term66 A B x op f s) = (term409 A B x op f s).
Proof. exact (TRANS (@lem5788019 A B x op f s) (@lem5788030 A B x op f s)). Qed.
Lemma lem5788032 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5788033 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term95 A B x op f s) = (term423 A B x op f s).
Proof. exact (MK_COMB (@lem5788032) (@lem5788031 A B x op f s)). Qed.
Lemma lem5788034 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term97 A B s f x op) = (term424 A B s f x op).
Proof. exact (MK_COMB (@lem5788033 A B x op f s) (@lem5787989 A B s f x op)). Qed.
Lemma lem5788035 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term116 A B f x op) = (term425 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5788034 A B s f x op)). Qed.
Lemma lem5788036 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5788037 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term127 A B f x op) = (term426 A B f x op).
Proof. exact (MK_COMB (@lem5788036 A) (@lem5788035 A B f x op)). Qed.
Lemma lem5788038 {A B : Type'} (f : A -> B) (op : type1400 B) : (term138 A B f op) = (term427 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5788037 A B f x op)). Qed.
Lemma lem5788039 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5788040 {A B : Type'} (f : A -> B) (op : type1400 B) : (term149 A B f op) = (term428 A B f op).
Proof. exact (MK_COMB (@lem5788039 A) (@lem5788038 A B f op)). Qed.
Lemma lem5788041 {A B : Type'} (op : type1400 B) : (term162 A B op) = (term429 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5788040 A B f op)). Qed.
Lemma lem5788042 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5788043 {A B : Type'} (op : type1400 B) : (term173 A B op) = (term430 A B op).
Proof. exact (MK_COMB (@lem5788042 A B) (@lem5788041 A B op)). Qed.
Lemma lem5788044 {A B : Type'} : (term186 A B) = (term431 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5788043 A B op)). Qed.
Lemma lem5788045 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5788046 {A B : Type'} : (term197 A B) = (term432 A B).
Proof. exact (MK_COMB (@lem5788045 B) (@lem5788044 A B)). Qed.
Lemma lem5788047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5788048 {A B : Type'} : (term199 A B) = (term433 A B).
Proof. exact (MK_COMB (@lem5788047) (@lem5788046 A B)). Qed.
Lemma lem5788049 {A B : Type'} : (term203 A B) = (term434 A B).
Proof. exact (MK_COMB (@lem5788048 A B) (@lem5787949 A B)). Qed.
Lemma lem5788050 {A B : Type'} (h1 : term7 A B) : term434 A B.
Proof. exact (EQ_MP (@lem5788049 A B) (@lem5785932 A B h1)). Qed.
Lemma lem5788251 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5788258 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788259 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5788258 A (type686 A) f x). Qed.
Lemma lem5788260 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5788259 A (@IN A) x). Qed.
Lemma lem5788261 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem5788262 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x (@EMPTY A)).
Proof. exact (MK_COMB (@lem5788260 A x) (@lem5788261 A)). Qed.
Lemma lem5788264 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788265 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5788264 (A -> Prop) Prop f x). Qed.
Lemma lem5788266 {A : Type'} (x : A) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x (@EMPTY A)) = (term435 A x).
Proof. exact (@lem5788265 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) (@EMPTY A)). Qed.
Lemma lem5788268 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = (term435 A x).
Proof. exact (TRANS (@lem5788262 A x) (@lem5788266 A x)). Qed.
Lemma lem5788269 {A : Type'} (x : A) : (term55 A x) = (term436 A x).
Proof. exact (MK_COMB (@lem5788251) (@lem5788268 A x)). Qed.
Lemma lem5788270 {A : Type'} : (term56 A) = (term437 A).
Proof. exact (fun_ext (fun x : A => @lem5788269 A x)). Qed.
Lemma lem5788271 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5788272 {A : Type'} : (term5 A) = (term438 A).
Proof. exact (MK_COMB (@lem5788271 A) (@lem5788270 A)). Qed.
Lemma lem5788273 {A : Type'} (h1 : term5 A) : term438 A.
Proof. exact (EQ_MP (@lem5788272 A) (@lem5786552 A h1)). Qed.
Lemma lem5788280 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788281 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5788280 A (type686 A) f x). Qed.
Lemma lem5788282 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5788281 A (@IN A) x). Qed.
Lemma lem5788283 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5788284 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x t).
Proof. exact (MK_COMB (@lem5788282 A x) (@lem5788283 A t)). Qed.
Lemma lem5788286 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788287 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5788286 (A -> Prop) Prop f x). Qed.
Lemma lem5788288 {A : Type'} (x : A) (t : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x t) = (term390 A x t).
Proof. exact (@lem5788287 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) t). Qed.
Lemma lem5788290 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (term390 A x t).
Proof. exact (TRANS (@lem5788284 A x t) (@lem5788288 A x t)). Qed.
Lemma lem5788291 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5788298 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788299 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5788298 A (type686 A) f x). Qed.
Lemma lem5788300 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5788299 A (@IN A) x). Qed.
Lemma lem5788301 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5788302 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5788300 A x) (@lem5788301 A s)). Qed.
Lemma lem5788304 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788305 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5788304 (A -> Prop) Prop f x). Qed.
Lemma lem5788306 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term390 A x s).
Proof. exact (@lem5788305 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5788308 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term390 A x s).
Proof. exact (TRANS (@lem5788302 A x s) (@lem5788306 A x s)). Qed.
Lemma lem5788309 {A : Type'} (x : A) (s : A -> Prop) : (term391 A x s) = (term392 A x s).
Proof. exact (MK_COMB (@lem5788291) (@lem5788308 A x s)). Qed.
Lemma lem5788310 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5788311 {A : Type'} (x : A) (s : A -> Prop) : (term90 A x s) = (term393 A x s).
Proof. exact (MK_COMB (@lem5788310) (@lem5788309 A x s)). Qed.
Lemma lem5788312 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term261 A s x t) = (term439 A s x t).
Proof. exact (MK_COMB (@lem5788311 A x s) (@lem5788290 A x t)). Qed.
Lemma lem5788313 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term255 A s t) = (term440 A s t).
Proof. exact (fun_ext (fun x : A => @lem5788312 A s x t)). Qed.
Lemma lem5788314 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5788315 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term273 A s t) = (term441 A s t).
Proof. exact (MK_COMB (@lem5788314 A) (@lem5788313 A s t)). Qed.
Lemma lem5788316 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5788323 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788324 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5788323 A (type686 A) f x). Qed.
Lemma lem5788325 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5788324 A (@IN A) x). Qed.
Lemma lem5788326 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5788327 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x t).
Proof. exact (MK_COMB (@lem5788325 A x) (@lem5788326 A t)). Qed.
Lemma lem5788329 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788330 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5788329 (A -> Prop) Prop f x). Qed.
Lemma lem5788331 {A : Type'} (x : A) (t : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x t) = (term390 A x t).
Proof. exact (@lem5788330 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) t). Qed.
Lemma lem5788333 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (term390 A x t).
Proof. exact (TRANS (@lem5788327 A x t) (@lem5788331 A x t)). Qed.
Lemma lem5788334 {A : Type'} (x : A) (t : A -> Prop) : (term391 A x t) = (term392 A x t).
Proof. exact (MK_COMB (@lem5788316) (@lem5788333 A x t)). Qed.
Lemma lem5788341 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788342 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5788341 A (type686 A) f x). Qed.
Lemma lem5788343 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5788342 A (@IN A) x). Qed.
Lemma lem5788344 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5788345 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5788343 A x) (@lem5788344 A s)). Qed.
Lemma lem5788347 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788348 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5788347 (A -> Prop) Prop f x). Qed.
Lemma lem5788349 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term390 A x s).
Proof. exact (@lem5788348 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5788351 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term390 A x s).
Proof. exact (TRANS (@lem5788345 A x s) (@lem5788349 A x s)). Qed.
Lemma lem5788352 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5788353 {A : Type'} (x : A) (s : A -> Prop) : (term442 A x s) = (term443 A x s).
Proof. exact (MK_COMB (@lem5788352) (@lem5788351 A x s)). Qed.
Lemma lem5788354 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term257 A s x t) = (term444 A s x t).
Proof. exact (MK_COMB (@lem5788353 A x s) (@lem5788334 A x t)). Qed.
Lemma lem5788355 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term254 A s t) = (term445 A s t).
Proof. exact (fun_ext (fun x : A => @lem5788354 A s x t)). Qed.
Lemma lem5788356 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5788357 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term268 A s t) = (term446 A s t).
Proof. exact (MK_COMB (@lem5788356 A) (@lem5788355 A s t)). Qed.
Lemma lem5788358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5788359 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term270 A s t) = (term447 A s t).
Proof. exact (MK_COMB (@lem5788358) (@lem5788357 A s t)). Qed.
Lemma lem5788360 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term274 A s t) = (term448 A s t).
Proof. exact (MK_COMB (@lem5788359 A s t) (@lem5788315 A s t)). Qed.
Lemma lem5788369 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term218 A s t) = (term218 A s t).
Proof. exact (eq_refl (term218 A s t)). Qed.
Lemma lem5788370 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term275 A s t) = (term449 A s t).
Proof. exact (MK_COMB (@lem5788369 A s t) (@lem5788360 A s t)). Qed.
Lemma lem5788371 {A : Type'} (s : A -> Prop) : (term276 A s) = (term450 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5788370 A s t)). Qed.
Lemma lem5788372 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5788373 {A : Type'} (s : A -> Prop) : (term277 A s) = (term451 A s).
Proof. exact (MK_COMB (@lem5788372 A) (@lem5788371 A s)). Qed.
Lemma lem5788374 {A : Type'} : (term284 A) = (term452 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5788373 A s)). Qed.
Lemma lem5788375 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5788376 {A : Type'} : (term299 A) = (term453 A).
Proof. exact (MK_COMB (@lem5788375 A) (@lem5788374 A)). Qed.
Lemma lem5788377 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5788378 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem5788385 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788386 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem5788385 (A -> Prop) (type684 A) f x). Qed.
Lemma lem5788387 {A : Type'} (x : type638 A) (s : A -> Prop) : (x s) = (@I ((A -> Prop) -> (A -> Prop) -> A) x s).
Proof. exact (@lem5788386 A x s). Qed.
Lemma lem5788388 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5788389 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (x s t) = (@I ((A -> Prop) -> (A -> Prop) -> A) x s t).
Proof. exact (MK_COMB (@lem5788387 A x s) (@lem5788388 A t)). Qed.
Lemma lem5788391 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788392 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem5788391 (A -> Prop) A f x). Qed.
Lemma lem5788393 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A) x s t) = (term454 A x s t).
Proof. exact (@lem5788392 A (@I ((A -> Prop) -> (A -> Prop) -> A) x s) t). Qed.
Lemma lem5788395 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (x s t) = (term454 A x s t).
Proof. exact (TRANS (@lem5788389 A x s t) (@lem5788393 A x s t)). Qed.
Lemma lem5788396 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5788397 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term455 A x s t) = (term456 A x s t).
Proof. exact (MK_COMB (@lem5788378 A) (@lem5788395 A x s t)). Qed.
Lemma lem5788398 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term457 A x s t) = (term458 A x s t).
Proof. exact (MK_COMB (@lem5788397 A x s t) (@lem5788396 A t)). Qed.
Lemma lem5788400 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788401 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5788400 A (type686 A) f x). Qed.
Lemma lem5788402 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term456 A x s t) = (term459 A x s t).
Proof. exact (@lem5788401 A (@IN A) (term454 A x s t)). Qed.
Lemma lem5788403 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5788404 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term458 A x s t) = (term460 A x s t).
Proof. exact (MK_COMB (@lem5788402 A x s t) (@lem5788403 A t)). Qed.
Lemma lem5788406 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788407 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5788406 (A -> Prop) Prop f x). Qed.
Lemma lem5788408 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term460 A x s t) = (term461 A x s t).
Proof. exact (@lem5788407 A (term459 A x s t) t). Qed.
Lemma lem5788409 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term458 A x s t) = (term461 A x s t).
Proof. exact (TRANS (@lem5788404 A x s t) (@lem5788408 A x s t)). Qed.
Lemma lem5788410 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term457 A x s t) = (term461 A x s t).
Proof. exact (TRANS (@lem5788398 A x s t) (@lem5788409 A x s t)). Qed.
Lemma lem5788411 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term462 A x s t) = (term463 A x s t).
Proof. exact (MK_COMB (@lem5788377) (@lem5788410 A x s t)). Qed.
Lemma lem5788412 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5788413 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem5788420 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788421 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem5788420 (A -> Prop) (type684 A) f x). Qed.
Lemma lem5788422 {A : Type'} (x : type638 A) (s : A -> Prop) : (x s) = (@I ((A -> Prop) -> (A -> Prop) -> A) x s).
Proof. exact (@lem5788421 A x s). Qed.
Lemma lem5788423 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5788424 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (x s t) = (@I ((A -> Prop) -> (A -> Prop) -> A) x s t).
Proof. exact (MK_COMB (@lem5788422 A x s) (@lem5788423 A t)). Qed.
Lemma lem5788426 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788427 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem5788426 (A -> Prop) A f x). Qed.
Lemma lem5788428 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A) x s t) = (term454 A x s t).
Proof. exact (@lem5788427 A (@I ((A -> Prop) -> (A -> Prop) -> A) x s) t). Qed.
Lemma lem5788430 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (x s t) = (term454 A x s t).
Proof. exact (TRANS (@lem5788424 A x s t) (@lem5788428 A x s t)). Qed.
Lemma lem5788431 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5788432 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term455 A x s t) = (term456 A x s t).
Proof. exact (MK_COMB (@lem5788413 A) (@lem5788430 A x s t)). Qed.
Lemma lem5788433 {A : Type'} (x : type638 A) (t : A -> Prop) (s : A -> Prop) : (term464 A x t s) = (term465 A x t s).
Proof. exact (MK_COMB (@lem5788432 A x s t) (@lem5788431 A s)). Qed.
Lemma lem5788435 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788436 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5788435 A (type686 A) f x). Qed.
Lemma lem5788437 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term456 A x s t) = (term459 A x s t).
Proof. exact (@lem5788436 A (@IN A) (term454 A x s t)). Qed.
Lemma lem5788438 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5788439 {A : Type'} (x : type638 A) (t : A -> Prop) (s : A -> Prop) : (term465 A x t s) = (term466 A x t s).
Proof. exact (MK_COMB (@lem5788437 A x s t) (@lem5788438 A s)). Qed.
Lemma lem5788441 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788442 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5788441 (A -> Prop) Prop f x). Qed.
Lemma lem5788443 {A : Type'} (x : type638 A) (t : A -> Prop) (s : A -> Prop) : (term466 A x t s) = (term467 A x t s).
Proof. exact (@lem5788442 A (term459 A x s t) s). Qed.
Lemma lem5788444 {A : Type'} (x : type638 A) (t : A -> Prop) (s : A -> Prop) : (term465 A x t s) = (term467 A x t s).
Proof. exact (TRANS (@lem5788439 A x t s) (@lem5788443 A x t s)). Qed.
Lemma lem5788445 {A : Type'} (x : type638 A) (t : A -> Prop) (s : A -> Prop) : (term464 A x t s) = (term467 A x t s).
Proof. exact (TRANS (@lem5788433 A x t s) (@lem5788444 A x t s)). Qed.
Lemma lem5788446 {A : Type'} (x : type638 A) (t : A -> Prop) (s : A -> Prop) : (term468 A x t s) = (term469 A x t s).
Proof. exact (MK_COMB (@lem5788412) (@lem5788445 A x t s)). Qed.
Lemma lem5788447 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5788448 {A : Type'} (x : type638 A) (t : A -> Prop) (s : A -> Prop) : (term470 A x t s) = (term471 A x t s).
Proof. exact (MK_COMB (@lem5788447) (@lem5788446 A x t s)). Qed.
Lemma lem5788449 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term472 A x s t) = (term473 A x s t).
Proof. exact (MK_COMB (@lem5788448 A x t s) (@lem5788411 A x s t)). Qed.
Lemma lem5788450 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem5788457 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788458 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem5788457 (A -> Prop) (type684 A) f x). Qed.
Lemma lem5788459 {A : Type'} (x : type638 A) (s : A -> Prop) : (x s) = (@I ((A -> Prop) -> (A -> Prop) -> A) x s).
Proof. exact (@lem5788458 A x s). Qed.
Lemma lem5788460 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5788461 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (x s t) = (@I ((A -> Prop) -> (A -> Prop) -> A) x s t).
Proof. exact (MK_COMB (@lem5788459 A x s) (@lem5788460 A t)). Qed.
Lemma lem5788463 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788464 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem5788463 (A -> Prop) A f x). Qed.
Lemma lem5788465 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A) x s t) = (term454 A x s t).
Proof. exact (@lem5788464 A (@I ((A -> Prop) -> (A -> Prop) -> A) x s) t). Qed.
Lemma lem5788467 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (x s t) = (term454 A x s t).
Proof. exact (TRANS (@lem5788461 A x s t) (@lem5788465 A x s t)). Qed.
Lemma lem5788468 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5788469 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term455 A x s t) = (term456 A x s t).
Proof. exact (MK_COMB (@lem5788450 A) (@lem5788467 A x s t)). Qed.
Lemma lem5788470 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term457 A x s t) = (term458 A x s t).
Proof. exact (MK_COMB (@lem5788469 A x s t) (@lem5788468 A t)). Qed.
Lemma lem5788472 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788473 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5788472 A (type686 A) f x). Qed.
Lemma lem5788474 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term456 A x s t) = (term459 A x s t).
Proof. exact (@lem5788473 A (@IN A) (term454 A x s t)). Qed.
Lemma lem5788475 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5788476 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term458 A x s t) = (term460 A x s t).
Proof. exact (MK_COMB (@lem5788474 A x s t) (@lem5788475 A t)). Qed.
Lemma lem5788478 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788479 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5788478 (A -> Prop) Prop f x). Qed.
Lemma lem5788480 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term460 A x s t) = (term461 A x s t).
Proof. exact (@lem5788479 A (term459 A x s t) t). Qed.
Lemma lem5788481 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term458 A x s t) = (term461 A x s t).
Proof. exact (TRANS (@lem5788476 A x s t) (@lem5788480 A x s t)). Qed.
Lemma lem5788482 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term457 A x s t) = (term461 A x s t).
Proof. exact (TRANS (@lem5788470 A x s t) (@lem5788481 A x s t)). Qed.
Lemma lem5788483 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem5788490 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788491 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem5788490 (A -> Prop) (type684 A) f x). Qed.
Lemma lem5788492 {A : Type'} (x : type638 A) (s : A -> Prop) : (x s) = (@I ((A -> Prop) -> (A -> Prop) -> A) x s).
Proof. exact (@lem5788491 A x s). Qed.
Lemma lem5788493 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5788494 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (x s t) = (@I ((A -> Prop) -> (A -> Prop) -> A) x s t).
Proof. exact (MK_COMB (@lem5788492 A x s) (@lem5788493 A t)). Qed.
Lemma lem5788496 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788497 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem5788496 (A -> Prop) A f x). Qed.
Lemma lem5788498 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A) x s t) = (term454 A x s t).
Proof. exact (@lem5788497 A (@I ((A -> Prop) -> (A -> Prop) -> A) x s) t). Qed.
Lemma lem5788500 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (x s t) = (term454 A x s t).
Proof. exact (TRANS (@lem5788494 A x s t) (@lem5788498 A x s t)). Qed.
Lemma lem5788501 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5788502 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term455 A x s t) = (term456 A x s t).
Proof. exact (MK_COMB (@lem5788483 A) (@lem5788500 A x s t)). Qed.
Lemma lem5788503 {A : Type'} (x : type638 A) (t : A -> Prop) (s : A -> Prop) : (term464 A x t s) = (term465 A x t s).
Proof. exact (MK_COMB (@lem5788502 A x s t) (@lem5788501 A s)). Qed.
Lemma lem5788505 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788506 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5788505 A (type686 A) f x). Qed.
Lemma lem5788507 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term456 A x s t) = (term459 A x s t).
Proof. exact (@lem5788506 A (@IN A) (term454 A x s t)). Qed.
Lemma lem5788508 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5788509 {A : Type'} (x : type638 A) (t : A -> Prop) (s : A -> Prop) : (term465 A x t s) = (term466 A x t s).
Proof. exact (MK_COMB (@lem5788507 A x s t) (@lem5788508 A s)). Qed.
Lemma lem5788511 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5788512 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5788511 (A -> Prop) Prop f x). Qed.
Lemma lem5788513 {A : Type'} (x : type638 A) (t : A -> Prop) (s : A -> Prop) : (term466 A x t s) = (term467 A x t s).
Proof. exact (@lem5788512 A (term459 A x s t) s). Qed.
Lemma lem5788514 {A : Type'} (x : type638 A) (t : A -> Prop) (s : A -> Prop) : (term465 A x t s) = (term467 A x t s).
Proof. exact (TRANS (@lem5788509 A x t s) (@lem5788513 A x t s)). Qed.
Lemma lem5788515 {A : Type'} (x : type638 A) (t : A -> Prop) (s : A -> Prop) : (term464 A x t s) = (term467 A x t s).
Proof. exact (TRANS (@lem5788503 A x t s) (@lem5788514 A x t s)). Qed.
Lemma lem5788516 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5788517 {A : Type'} (x : type638 A) (t : A -> Prop) (s : A -> Prop) : (term474 A x t s) = (term475 A x t s).
Proof. exact (MK_COMB (@lem5788516) (@lem5788515 A x t s)). Qed.
Lemma lem5788518 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term476 A x s t) = (term477 A x s t).
Proof. exact (MK_COMB (@lem5788517 A x t s) (@lem5788482 A x s t)). Qed.
Lemma lem5788519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5788520 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term478 A x s t) = (term479 A x s t).
Proof. exact (MK_COMB (@lem5788519) (@lem5788518 A x s t)). Qed.
Lemma lem5788521 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term480 A x s t) = (term481 A x s t).
Proof. exact (MK_COMB (@lem5788520 A x s t) (@lem5788449 A x s t)). Qed.
Lemma lem5788528 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term221 A s t) = (term221 A s t).
Proof. exact (eq_refl (term221 A s t)). Qed.
Lemma lem5788529 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term482 A x s t) = (term483 A x s t).
Proof. exact (MK_COMB (@lem5788528 A s t) (@lem5788521 A x s t)). Qed.
Lemma lem5788530 {A : Type'} (x : type638 A) (s : A -> Prop) : (term484 A x s) = (term485 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5788529 A x s t)). Qed.
Lemma lem5788531 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5788532 {A : Type'} (x : type638 A) (s : A -> Prop) : (term359 A x s) = (term486 A x s).
Proof. exact (MK_COMB (@lem5788531 A) (@lem5788530 A x s)). Qed.
Lemma lem5788533 {A : Type'} (x : type638 A) : (term361 A x) = (term487 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5788532 A x s)). Qed.
Lemma lem5788534 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5788535 {A : Type'} (x : type638 A) : (term363 A x) = (term488 A x).
Proof. exact (MK_COMB (@lem5788534 A) (@lem5788533 A x)). Qed.
Lemma lem5788536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5788537 {A : Type'} (x : type638 A) : (term382 A x) = (term489 A x).
Proof. exact (MK_COMB (@lem5788536) (@lem5788535 A x)). Qed.
Lemma lem5788538 {A : Type'} (x : type638 A) : (term384 A x) = (term490 A x).
Proof. exact (MK_COMB (@lem5788537 A x) (@lem5788376 A)). Qed.
Lemma lem5788539 {A : Type'} (x : type638 A) (h1 : term384 A x) : term490 A x.
Proof. exact (EQ_MP (@lem5788538 A x) (@lem5787364 A x h1)). Qed.
Lemma lem5788541 {A : Type'} (x : type638 A) (h1 : term384 A x) : term488 A x.
Proof. exact (proj1 (@lem5788539 A x h1)). Qed.
Lemma lem5788544 {A B : Type'} (h1 : term7 A B) : term422 A B.
Proof. exact (proj2 (@lem5788050 A B h1)). Qed.
Lemma lem5788561 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term394 A B s f x op) = (term394 A B s f x op).
Proof. exact (eq_refl (term394 A B s f x op)). Qed.
Lemma lem5788562 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term395 A B s f op) = (term395 A B s f op).
Proof. exact (fun_ext (fun x : A => @lem5788561 A B s f x op)). Qed.
Lemma lem5788563 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5788565 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term396 A B s f op) = (term396 A B s f op).
Proof. exact (MK_COMB (@lem5788563 A) (@lem5788562 A B s f op)). Qed.
Lemma lem5788566 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) : term396 A B s f op.
Proof. exact (EQ_MP (@lem5788565 A B s f op) (@lem5787417 A B s f op h1)). Qed.
Lemma lem5788572 {A : Type'} (x : A) : (term436 A x) = (term436 A x).
Proof. exact (eq_refl (term436 A x)). Qed.
Lemma lem5788573 {A : Type'} : (term437 A) = (term437 A).
Proof. exact (fun_ext (fun x : A => @lem5788572 A x)). Qed.
Lemma lem5788574 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5788576 {A : Type'} : (term438 A) = (term438 A).
Proof. exact (MK_COMB (@lem5788574 A) (@lem5788573 A)). Qed.
Lemma lem5788577 {A : Type'} (h1 : term5 A) : term438 A.
Proof. exact (EQ_MP (@lem5788576 A) (@lem5788273 A h1)). Qed.
Lemma lem5788607 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term483 A x s t) = (term491 A x s t).
Proof. exact (@lem19490 (term477 A x s t) (s = t) (term473 A x s t)). Qed.
Lemma lem5788608 {A : Type'} (x : type638 A) (s : A -> Prop) : (term485 A x s) = (term492 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5788607 A x s t)). Qed.
Lemma lem5788609 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5788610 {A : Type'} (x : type638 A) (s : A -> Prop) : (term486 A x s) = (term493 A x s).
Proof. exact (MK_COMB (@lem5788609 A) (@lem5788608 A x s)). Qed.
Lemma lem5788611 {A : Type'} (x : type638 A) : (term487 A x) = (term494 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5788610 A x s)). Qed.
Lemma lem5788612 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5788614 {A : Type'} (x : type638 A) : (term488 A x) = (term495 A x).
Proof. exact (MK_COMB (@lem5788612 A) (@lem5788611 A x)). Qed.
Lemma lem5788615 {A : Type'} (x : type638 A) (h1 : term384 A x) : term495 A x.
Proof. exact (EQ_MP (@lem5788614 A x) (@lem5788541 A x h1)). Qed.
Lemma lem5788817 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term414 A B s f x op) = (term496 A B s f x op).
Proof. exact (@lem19490 (term390 A x s) (term411 A B x op f s) (term403 A B f x op)). Qed.
Lemma lem5788818 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term415 A B f x op) = (term497 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5788817 A B s f x op)). Qed.
Lemma lem5788819 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5788820 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term416 A B f x op) = (term498 A B f x op).
Proof. exact (MK_COMB (@lem5788819 A) (@lem5788818 A B f x op)). Qed.
Lemma lem5788821 {A B : Type'} (f : A -> B) (op : type1400 B) : (term417 A B f op) = (term499 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5788820 A B f x op)). Qed.
Lemma lem5788822 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5788823 {A B : Type'} (f : A -> B) (op : type1400 B) : (term418 A B f op) = (term500 A B f op).
Proof. exact (MK_COMB (@lem5788822 A) (@lem5788821 A B f op)). Qed.
Lemma lem5788824 {A B : Type'} (op : type1400 B) : (term419 A B op) = (term501 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5788823 A B f op)). Qed.
Lemma lem5788825 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5788826 {A B : Type'} (op : type1400 B) : (term420 A B op) = (term502 A B op).
Proof. exact (MK_COMB (@lem5788825 A B) (@lem5788824 A B op)). Qed.
Lemma lem5788827 {A B : Type'} : (term421 A B) = (term503 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5788826 A B op)). Qed.
Lemma lem5788828 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5788830 {A B : Type'} : (term422 A B) = (term504 A B).
Proof. exact (MK_COMB (@lem5788828 B) (@lem5788827 A B)). Qed.
Lemma lem5788831 {A B : Type'} (h1 : term7 A B) : term504 A B.
Proof. exact (EQ_MP (@lem5788830 A B) (@lem5788544 A B h1)). Qed.
Lemma lem5788952 {A B : Type'} (_72878 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) : term505 A B s f op _72878.
Proof. exact (@lem5788566 A B s f op h1 _72878). Qed.
Lemma lem5788953 {A B : Type'} (s : A -> Prop) (f : A -> B) (_72878 : A) (op : type1400 B) : (term505 A B s f op _72878) = (term394 A B s f _72878 op).
Proof. exact (eq_refl (term505 A B s f op _72878)). Qed.
Lemma lem5788955 {A : Type'} (_72879 : A) (h1 : term5 A) : term506 A _72879.
Proof. exact (@lem5788577 A h1 _72879). Qed.
Lemma lem5788956 {A : Type'} (_72879 : A) : (term506 A _72879) = (term436 A _72879).
Proof. exact (eq_refl (term506 A _72879)). Qed.
Lemma lem5788958 {A : Type'} (_72880 : A -> Prop) (x : type638 A) (h1 : term384 A x) : term507 A x _72880.
Proof. exact (@lem5788615 A x h1 _72880). Qed.
Lemma lem5788959 {A : Type'} (x : type638 A) (_72880 : A -> Prop) : (term507 A x _72880) = (term493 A x _72880).
Proof. exact (eq_refl (term507 A x _72880)). Qed.
Lemma lem5788960 {A : Type'} (_72880 : A -> Prop) (x : type638 A) (h1 : term384 A x) : term493 A x _72880.
Proof. exact (EQ_MP (@lem5788959 A x _72880) (@lem5788958 A _72880 x h1)). Qed.
Lemma lem5788961 {A : Type'} (_72880 : A -> Prop) (_72881 : A -> Prop) (x : type638 A) (h1 : term384 A x) : term508 A x _72880 _72881.
Proof. exact (@lem5788960 A _72880 x h1 _72881). Qed.
Lemma lem5788962 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : (term508 A x _72880 _72881) = (term491 A x _72880 _72881).
Proof. exact (eq_refl (term508 A x _72880 _72881)). Qed.
Lemma lem5788963 {A : Type'} (_72880 : A -> Prop) (_72881 : A -> Prop) (x : type638 A) (h1 : term384 A x) : term491 A x _72880 _72881.
Proof. exact (EQ_MP (@lem5788962 A x _72880 _72881) (@lem5788961 A _72880 _72881 x h1)). Qed.
Lemma lem5789009 {A B : Type'} (_72897 : type1400 B) (h1 : term7 A B) : term509 A B _72897.
Proof. exact (@lem5788831 A B h1 _72897). Qed.
Lemma lem5789010 {A B : Type'} (_72897 : type1400 B) : (term509 A B _72897) = (term502 A B _72897).
Proof. exact (eq_refl (term509 A B _72897)). Qed.
Lemma lem5789011 {A B : Type'} (_72897 : type1400 B) (h1 : term7 A B) : term502 A B _72897.
Proof. exact (EQ_MP (@lem5789010 A B _72897) (@lem5789009 A B _72897 h1)). Qed.
Lemma lem5789012 {A B : Type'} (_72897 : type1400 B) (_72898 : A -> B) (h1 : term7 A B) : term510 A B _72897 _72898.
Proof. exact (@lem5789011 A B _72897 h1 _72898). Qed.
Lemma lem5789013 {A B : Type'} (_72898 : A -> B) (_72897 : type1400 B) : (term510 A B _72897 _72898) = (term500 A B _72898 _72897).
Proof. exact (eq_refl (term510 A B _72897 _72898)). Qed.
Lemma lem5789014 {A B : Type'} (_72898 : A -> B) (_72897 : type1400 B) (h1 : term7 A B) : term500 A B _72898 _72897.
Proof. exact (EQ_MP (@lem5789013 A B _72898 _72897) (@lem5789012 A B _72897 _72898 h1)). Qed.
Lemma lem5789015 {A B : Type'} (_72898 : A -> B) (_72897 : type1400 B) (_72899 : A) (h1 : term7 A B) : term511 A B _72898 _72897 _72899.
Proof. exact (@lem5789014 A B _72898 _72897 h1 _72899). Qed.
Lemma lem5789016 {A B : Type'} (_72898 : A -> B) (_72899 : A) (_72897 : type1400 B) : (term511 A B _72898 _72897 _72899) = (term498 A B _72898 _72899 _72897).
Proof. exact (eq_refl (term511 A B _72898 _72897 _72899)). Qed.
Lemma lem5789017 {A B : Type'} (_72898 : A -> B) (_72899 : A) (_72897 : type1400 B) (h1 : term7 A B) : term498 A B _72898 _72899 _72897.
Proof. exact (EQ_MP (@lem5789016 A B _72898 _72899 _72897) (@lem5789015 A B _72898 _72897 _72899 h1)). Qed.
Lemma lem5789018 {A B : Type'} (_72898 : A -> B) (_72899 : A) (_72897 : type1400 B) (_72900 : A -> Prop) (h1 : term7 A B) : term512 A B _72898 _72899 _72897 _72900.
Proof. exact (@lem5789017 A B _72898 _72899 _72897 h1 _72900). Qed.
Lemma lem5789019 {A B : Type'} (_72900 : A -> Prop) (_72898 : A -> B) (_72899 : A) (_72897 : type1400 B) : (term512 A B _72898 _72899 _72897 _72900) = (term496 A B _72900 _72898 _72899 _72897).
Proof. exact (eq_refl (term512 A B _72898 _72899 _72897 _72900)). Qed.
Lemma lem5789020 {A B : Type'} (_72900 : A -> Prop) (_72898 : A -> B) (_72899 : A) (_72897 : type1400 B) (h1 : term7 A B) : term496 A B _72900 _72898 _72899 _72897.
Proof. exact (EQ_MP (@lem5789019 A B _72900 _72898 _72899 _72897) (@lem5789018 A B _72898 _72899 _72897 _72900 h1)). Qed.
Lemma lem5789088 {A B : Type'} (_72878 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) : term394 A B s f _72878 op.
Proof. exact (EQ_MP (@lem5788953 A B s f _72878 op) (@lem5788952 A B _72878 s f op h1)). Qed.
Lemma lem5789092 {A : Type'} (_72879 : A) (h1 : term5 A) : term436 A _72879.
Proof. exact (EQ_MP (@lem5788956 A _72879) (@lem5788955 A _72879 h1)). Qed.
Lemma lem5789162 {A B : Type'} (_72897 : type1400 B) (_72898 : A -> B) (_72899 : A) (_72900 : A -> Prop) (h1 : term7 A B) : term513 A B _72897 _72898 _72899 _72900.
Proof. exact (proj1 (@lem5789020 A B _72900 _72898 _72899 _72897 h1)). Qed.
Lemma lem5789168 {A B : Type'} (_72900 : A -> Prop) (_72898 : A -> B) (_72899 : A) (_72897 : type1400 B) (h1 : term7 A B) : term514 A B _72900 _72898 _72899 _72897.
Proof. exact (proj2 (@lem5789020 A B _72900 _72898 _72899 _72897 h1)). Qed.
Lemma lem5789210 {A : Type'} (_72880 : A -> Prop) (_72881 : A -> Prop) (x : type638 A) (h1 : term384 A x) : term515 A x _72880 _72881.
Proof. exact (proj1 (@lem5788963 A _72880 _72881 x h1)). Qed.
Lemma lem5789660 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term3 A B op f s) : term402 A B op f s.
Proof. exact (EQ_MP (@lem5787449 A B op f s) (@lem5784111 A B op f s h1)). Qed.
Lemma lem5789661 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term3 A B op f s) : term516 A B op f s.
Proof. exact (fun h0 : (term399 A B op f s) = (@EMPTY A) => @lem5789660 A B op f s h1). Qed.
Lemma lem5789663 (p : Prop) : (term517 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5789664 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term516 A B op f s) = (term402 A B op f s).
Proof. exact (@lem5789663 ((term399 A B op f s) = (@EMPTY A))). Qed.
Lemma lem5789665 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term3 A B op f s) : term402 A B op f s.
Proof. exact (EQ_MP (@lem5789664 A B op f s) (@lem5789661 A B op f s h1)). Qed.
Lemma lem5789667 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term3 A B op f s) : term402 A B op f s.
Proof. exact (EQ_MP (@lem5787449 A B op f s) (@lem5784111 A B op f s h1)). Qed.
Lemma lem5789668 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term3 A B op f s) : term516 A B op f s.
Proof. exact (fun h0 : (term399 A B op f s) = (@EMPTY A) => @lem5789667 A B op f s h1). Qed.
Lemma lem5789670 (p : Prop) : (term517 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5789671 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term516 A B op f s) = (term402 A B op f s).
Proof. exact (@lem5789670 ((term399 A B op f s) = (@EMPTY A))). Qed.
Lemma lem5789672 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term3 A B op f s) : term402 A B op f s.
Proof. exact (EQ_MP (@lem5789671 A B op f s) (@lem5789668 A B op f s h1)). Qed.
Lemma lem5789675 {A B : Type'} (x : type638 A) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term518 A B x op f s) : term518 A B x op f s.
Proof. exact (h1). Qed.
Lemma lem5789676 {A B : Type'} (x : type638 A) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term518 A B x op f s) : term519 A B x op f s.
Proof. exact (fun h0 : term520 A B x op f s => @lem5789675 A B x op f s h1). Qed.
Lemma lem5789678 (p : Prop) : (term517 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5789679 {A B : Type'} (x : type638 A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term519 A B x op f s) = (term518 A B x op f s).
Proof. exact (@lem5789678 (term520 A B x op f s)). Qed.
Lemma lem5789680 {A B : Type'} (x : type638 A) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term518 A B x op f s) : term518 A B x op f s.
Proof. exact (EQ_MP (@lem5789679 A B x op f s) (@lem5789676 A B x op f s h1)). Qed.
Lemma lem5789703 (q : Prop) (p : Prop) (r : Prop) : (term521 p q r) = (term521 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5789704 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : (term522 A x _72880 _72881) = (term515 A x _72880 _72881).
Proof. exact (@lem5789703 (_72880 = _72881) (term467 A x _72881 _72880) (term461 A x _72880 _72881)). Qed.
Lemma lem5789722 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : (term523 A x _72880 _72881) = (term523 A x _72880 _72881).
Proof. exact (eq_refl (term523 A x _72880 _72881)). Qed.
Lemma lem5789723 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : ((term515 A x _72880 _72881) = (term522 A x _72880 _72881)) = ((term515 A x _72880 _72881) = (term515 A x _72880 _72881)).
Proof. exact (MK_COMB (@lem5789722 A x _72880 _72881) (@lem5789704 A x _72880 _72881)). Qed.
Lemma lem5789725 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5789726 (x : Prop) : (x = x) = True.
Proof. exact (@lem5789725 Prop x). Qed.
Lemma lem5789727 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : ((term515 A x _72880 _72881) = (term515 A x _72880 _72881)) = True.
Proof. exact (@lem5789726 (term515 A x _72880 _72881)). Qed.
Lemma lem5789728 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : ((term515 A x _72880 _72881) = (term522 A x _72880 _72881)) = True.
Proof. exact (TRANS (@lem5789723 A x _72880 _72881) (@lem5789727 A x _72880 _72881)). Qed.
Lemma lem5789729 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : True = ((term515 A x _72880 _72881) = (term522 A x _72880 _72881)).
Proof. exact (SYM (@lem5789728 A x _72880 _72881)). Qed.
Lemma lem5789730 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : (term515 A x _72880 _72881) = (term522 A x _72880 _72881).
Proof. exact (EQ_MP (@lem5789729 A x _72880 _72881) (@lem0)). Qed.
Lemma lem5789731 {A : Type'} (_72880 : A -> Prop) (_72881 : A -> Prop) (x : type638 A) (h1 : term384 A x) : term522 A x _72880 _72881.
Proof. exact (EQ_MP (@lem5789730 A x _72880 _72881) (@lem5789210 A _72880 _72881 x h1)). Qed.
Lemma lem5789733 (b : Prop) (a : Prop) : (a \/ b) = (term524 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5789734 {A : Type'} (x : type638 A) (_72881 : A -> Prop) (_72880 : A -> Prop) : (term522 A x _72880 _72881) = (term525 A x _72881 _72880).
Proof. exact (@lem5789733 (term526 A x _72880 _72881) (term467 A x _72881 _72880)). Qed.
Lemma lem5789736 (a : Prop) (b : Prop) : (term527 a b) = (term528 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5789737 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : (term529 A x _72880 _72881) = (term530 A x _72880 _72881).
Proof. exact (@lem5789736 (_72880 = _72881) (term461 A x _72880 _72881)). Qed.
Lemma lem5789738 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5789739 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : (term531 A x _72880 _72881) = (term532 A x _72880 _72881).
Proof. exact (MK_COMB (@lem5789738) (@lem5789737 A x _72880 _72881)). Qed.
Lemma lem5789740 {A : Type'} (x : type638 A) (_72881 : A -> Prop) (_72880 : A -> Prop) : (term467 A x _72881 _72880) = (term467 A x _72881 _72880).
Proof. exact (eq_refl (term467 A x _72881 _72880)). Qed.
Lemma lem5789741 {A : Type'} (x : type638 A) (_72881 : A -> Prop) (_72880 : A -> Prop) : (term525 A x _72881 _72880) = (term533 A x _72881 _72880).
Proof. exact (MK_COMB (@lem5789739 A x _72880 _72881) (@lem5789740 A x _72881 _72880)). Qed.
Lemma lem5789742 {A : Type'} (x : type638 A) (_72881 : A -> Prop) (_72880 : A -> Prop) : (term522 A x _72880 _72881) = (term533 A x _72881 _72880).
Proof. exact (TRANS (@lem5789734 A x _72881 _72880) (@lem5789741 A x _72881 _72880)). Qed.
Lemma lem5789744 {A B : Type'} (x : type638 A) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term3 A B op f s) (h2 : term518 A B x op f s) : term534 A B x op f s.
Proof. exact (conj (@lem5789672 A B op f s h1) (@lem5789680 A B x op f s h2)). Qed.
Lemma lem5789746 {A : Type'} (_72881 : A -> Prop) (_72880 : A -> Prop) (x : type638 A) (h1 : term384 A x) : term533 A x _72881 _72880.
Proof. exact (EQ_MP (@lem5789742 A x _72881 _72880) (@lem5789731 A _72880 _72881 x h1)). Qed.
Lemma lem5789747 {A : Type'} (_72881 : A -> Prop) (_72880 : A -> Prop) (x : type638 A) (h1 : term384 A x) : term533 A x _72881 _72880.
Proof. exact (@lem5789746 A _72881 _72880 x h1). Qed.
Lemma lem5789748 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term384 A x) : term535 A B x op f s.
Proof. exact (@lem5789747 A (@EMPTY A) (term399 A B op f s) x h1). Qed.
Lemma lem5789751 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term3 A B op f s) (h2 : term518 A B x op f s) (h3 : term384 A x) : term536 A B x op f s.
Proof. exact (@lem5789748 A B op f s x h3 (@lem5789744 A B x op f s h1 h2)). Qed.
Lemma lem5789752 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term3 A B op f s) (h2 : term518 A B x op f s) (h3 : term384 A x) : term537 A B x op f s.
Proof. exact (fun h0 : term538 A B x op f s => @lem5789751 A B op f s x h1 h2 h3). Qed.
Lemma lem5789754 (p : Prop) : (term539 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5789755 {A B : Type'} (x : type638 A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term537 A B x op f s) = (term536 A B x op f s).
Proof. exact (@lem5789754 (term536 A B x op f s)). Qed.
Lemma lem5789756 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term3 A B op f s) (h2 : term518 A B x op f s) (h3 : term384 A x) : term536 A B x op f s.
Proof. exact (EQ_MP (@lem5789755 A B x op f s) (@lem5789752 A B op f s x h1 h2 h3)). Qed.
Lemma lem5789762 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5789763 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) : (term513 A B _72897 _72898 _72899 _72900) = (term540 A B _72899 _72897 _72898 _72900).
Proof. exact (@lem5789762 (term390 A _72899 _72900) (term411 A B _72899 _72897 _72898 _72900)). Qed.
Lemma lem5789769 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5789770 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) : (term541 A B _72897 _72898 _72899 _72900) = (term542 A B _72899 _72897 _72898 _72900).
Proof. exact (MK_COMB (@lem5789769) (@lem5789763 A B _72899 _72897 _72898 _72900)). Qed.
Lemma lem5789776 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) : (term540 A B _72899 _72897 _72898 _72900) = (term540 A B _72899 _72897 _72898 _72900).
Proof. exact (eq_refl (term540 A B _72899 _72897 _72898 _72900)). Qed.
Lemma lem5789777 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) : ((term513 A B _72897 _72898 _72899 _72900) = (term540 A B _72899 _72897 _72898 _72900)) = ((term540 A B _72899 _72897 _72898 _72900) = (term540 A B _72899 _72897 _72898 _72900)).
Proof. exact (MK_COMB (@lem5789770 A B _72899 _72897 _72898 _72900) (@lem5789776 A B _72899 _72897 _72898 _72900)). Qed.
Lemma lem5789779 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5789780 (x : Prop) : (x = x) = True.
Proof. exact (@lem5789779 Prop x). Qed.
Lemma lem5789781 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) : ((term540 A B _72899 _72897 _72898 _72900) = (term540 A B _72899 _72897 _72898 _72900)) = True.
Proof. exact (@lem5789780 (term540 A B _72899 _72897 _72898 _72900)). Qed.
Lemma lem5789782 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) : ((term513 A B _72897 _72898 _72899 _72900) = (term540 A B _72899 _72897 _72898 _72900)) = True.
Proof. exact (TRANS (@lem5789777 A B _72899 _72897 _72898 _72900) (@lem5789781 A B _72899 _72897 _72898 _72900)). Qed.
Lemma lem5789783 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) : True = ((term513 A B _72897 _72898 _72899 _72900) = (term540 A B _72899 _72897 _72898 _72900)).
Proof. exact (SYM (@lem5789782 A B _72899 _72897 _72898 _72900)). Qed.
Lemma lem5789784 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) : (term513 A B _72897 _72898 _72899 _72900) = (term540 A B _72899 _72897 _72898 _72900).
Proof. exact (EQ_MP (@lem5789783 A B _72899 _72897 _72898 _72900) (@lem0)). Qed.
Lemma lem5789785 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) (h1 : term7 A B) : term540 A B _72899 _72897 _72898 _72900.
Proof. exact (EQ_MP (@lem5789784 A B _72899 _72897 _72898 _72900) (@lem5789162 A B _72897 _72898 _72899 _72900 h1)). Qed.
Lemma lem5789787 (b : Prop) (a : Prop) : (a \/ b) = (term524 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5789788 {A B : Type'} (_72897 : type1400 B) (_72898 : A -> B) (_72899 : A) (_72900 : A -> Prop) : (term540 A B _72899 _72897 _72898 _72900) = (term543 A B _72897 _72898 _72899 _72900).
Proof. exact (@lem5789787 (term411 A B _72899 _72897 _72898 _72900) (term390 A _72899 _72900)). Qed.
Lemma lem5789790 (a : Prop) : (term544 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5789791 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) : (term545 A B _72899 _72897 _72898 _72900) = (term409 A B _72899 _72897 _72898 _72900).
Proof. exact (@lem5789790 (term409 A B _72899 _72897 _72898 _72900)). Qed.
Lemma lem5789792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5789793 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) : (term546 A B _72899 _72897 _72898 _72900) = (term547 A B _72899 _72897 _72898 _72900).
Proof. exact (MK_COMB (@lem5789792) (@lem5789791 A B _72899 _72897 _72898 _72900)). Qed.
Lemma lem5789794 {A : Type'} (_72899 : A) (_72900 : A -> Prop) : (term390 A _72899 _72900) = (term390 A _72899 _72900).
Proof. exact (eq_refl (term390 A _72899 _72900)). Qed.
Lemma lem5789795 {A B : Type'} (_72897 : type1400 B) (_72898 : A -> B) (_72899 : A) (_72900 : A -> Prop) : (term543 A B _72897 _72898 _72899 _72900) = (term548 A B _72897 _72898 _72899 _72900).
Proof. exact (MK_COMB (@lem5789793 A B _72899 _72897 _72898 _72900) (@lem5789794 A _72899 _72900)). Qed.
Lemma lem5789796 {A B : Type'} (_72897 : type1400 B) (_72898 : A -> B) (_72899 : A) (_72900 : A -> Prop) : (term540 A B _72899 _72897 _72898 _72900) = (term548 A B _72897 _72898 _72899 _72900).
Proof. exact (TRANS (@lem5789788 A B _72897 _72898 _72899 _72900) (@lem5789795 A B _72897 _72898 _72899 _72900)). Qed.
Lemma lem5789799 {A B : Type'} (_72897 : type1400 B) (_72898 : A -> B) (_72899 : A) (_72900 : A -> Prop) (h1 : term7 A B) : term548 A B _72897 _72898 _72899 _72900.
Proof. exact (EQ_MP (@lem5789796 A B _72897 _72898 _72899 _72900) (@lem5789785 A B _72899 _72897 _72898 _72900 h1)). Qed.
Lemma lem5789800 {A B : Type'} (_72897 : type1400 B) (_72898 : A -> B) (_72899 : A) (_72900 : A -> Prop) (h1 : term7 A B) : term548 A B _72897 _72898 _72899 _72900.
Proof. exact (@lem5789799 A B _72897 _72898 _72899 _72900 h1). Qed.
Lemma lem5789801 {A B : Type'} (x : type638 A) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term7 A B) : term549 A B x op f s.
Proof. exact (@lem5789800 A B op f (term550 A B x op f s) s h1). Qed.
Lemma lem5789804 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term7 A B) (h2 : term3 A B op f s) (h3 : term518 A B x op f s) (h4 : term384 A x) : term551 A B x op f s.
Proof. exact (@lem5789801 A B x op f s h1 (@lem5789756 A B op f s x h2 h3 h4)). Qed.
Lemma lem5789805 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term7 A B) (h2 : term3 A B op f s) (h3 : term518 A B x op f s) (h4 : term384 A x) : term552 A B x op f s.
Proof. exact (fun h0 : term553 A B x op f s => @lem5789804 A B op f s x h1 h2 h3 h4). Qed.
Lemma lem5789807 (p : Prop) : (term539 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5789808 {A B : Type'} (x : type638 A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term552 A B x op f s) = (term551 A B x op f s).
Proof. exact (@lem5789807 (term551 A B x op f s)). Qed.
Lemma lem5789809 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term7 A B) (h2 : term3 A B op f s) (h3 : term518 A B x op f s) (h4 : term384 A x) : term551 A B x op f s.
Proof. exact (EQ_MP (@lem5789808 A B x op f s) (@lem5789805 A B op f s x h1 h2 h3 h4)). Qed.
Lemma lem5789815 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5789816 {A B : Type'} (f : A -> B) (op : type1400 B) (_72878 : A) (s : A -> Prop) : (term394 A B s f _72878 op) = (term554 A B f op _72878 s).
Proof. exact (@lem5789815 ((@I (A -> B) f _72878) = (@I ((B -> B -> B) -> B) (@neutral B) op)) (term392 A _72878 s)). Qed.
Lemma lem5789824 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5789825 {A B : Type'} (f : A -> B) (op : type1400 B) (_72878 : A) (s : A -> Prop) : (term555 A B s f _72878 op) = (term556 A B f op _72878 s).
Proof. exact (MK_COMB (@lem5789824) (@lem5789816 A B f op _72878 s)). Qed.
Lemma lem5789833 {A B : Type'} (f : A -> B) (op : type1400 B) (_72878 : A) (s : A -> Prop) : (term554 A B f op _72878 s) = (term554 A B f op _72878 s).
Proof. exact (eq_refl (term554 A B f op _72878 s)). Qed.
Lemma lem5789834 {A B : Type'} (f : A -> B) (op : type1400 B) (_72878 : A) (s : A -> Prop) : ((term394 A B s f _72878 op) = (term554 A B f op _72878 s)) = ((term554 A B f op _72878 s) = (term554 A B f op _72878 s)).
Proof. exact (MK_COMB (@lem5789825 A B f op _72878 s) (@lem5789833 A B f op _72878 s)). Qed.
Lemma lem5789836 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5789837 (x : Prop) : (x = x) = True.
Proof. exact (@lem5789836 Prop x). Qed.
Lemma lem5789838 {A B : Type'} (f : A -> B) (op : type1400 B) (_72878 : A) (s : A -> Prop) : ((term554 A B f op _72878 s) = (term554 A B f op _72878 s)) = True.
Proof. exact (@lem5789837 (term554 A B f op _72878 s)). Qed.
Lemma lem5789839 {A B : Type'} (f : A -> B) (op : type1400 B) (_72878 : A) (s : A -> Prop) : ((term394 A B s f _72878 op) = (term554 A B f op _72878 s)) = True.
Proof. exact (TRANS (@lem5789834 A B f op _72878 s) (@lem5789838 A B f op _72878 s)). Qed.
Lemma lem5789840 {A B : Type'} (f : A -> B) (op : type1400 B) (_72878 : A) (s : A -> Prop) : True = ((term394 A B s f _72878 op) = (term554 A B f op _72878 s)).
Proof. exact (SYM (@lem5789839 A B f op _72878 s)). Qed.
Lemma lem5789841 {A B : Type'} (f : A -> B) (op : type1400 B) (_72878 : A) (s : A -> Prop) : (term394 A B s f _72878 op) = (term554 A B f op _72878 s).
Proof. exact (EQ_MP (@lem5789840 A B f op _72878 s) (@lem0)). Qed.
Lemma lem5789842 {A B : Type'} (_72878 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) : term554 A B f op _72878 s.
Proof. exact (EQ_MP (@lem5789841 A B f op _72878 s) (@lem5789088 A B _72878 s f op h1)). Qed.
Lemma lem5789844 (b : Prop) (a : Prop) : (a \/ b) = (term524 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5789845 {A B : Type'} (s : A -> Prop) (f : A -> B) (_72878 : A) (op : type1400 B) : (term554 A B f op _72878 s) = (term557 A B s f _72878 op).
Proof. exact (@lem5789844 (term392 A _72878 s) ((@I (A -> B) f _72878) = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem5789847 (a : Prop) : (term544 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5789848 {A : Type'} (_72878 : A) (s : A -> Prop) : (term558 A _72878 s) = (term390 A _72878 s).
Proof. exact (@lem5789847 (term390 A _72878 s)). Qed.
Lemma lem5789849 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5789850 {A : Type'} (_72878 : A) (s : A -> Prop) : (term559 A _72878 s) = (term560 A _72878 s).
Proof. exact (MK_COMB (@lem5789849) (@lem5789848 A _72878 s)). Qed.
Lemma lem5789851 {A B : Type'} (f : A -> B) (_72878 : A) (op : type1400 B) : ((@I (A -> B) f _72878) = (@I ((B -> B -> B) -> B) (@neutral B) op)) = ((@I (A -> B) f _72878) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (eq_refl ((@I (A -> B) f _72878) = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem5789852 {A B : Type'} (s : A -> Prop) (f : A -> B) (_72878 : A) (op : type1400 B) : (term557 A B s f _72878 op) = (term561 A B s f _72878 op).
Proof. exact (MK_COMB (@lem5789850 A _72878 s) (@lem5789851 A B f _72878 op)). Qed.
Lemma lem5789853 {A B : Type'} (s : A -> Prop) (f : A -> B) (_72878 : A) (op : type1400 B) : (term554 A B f op _72878 s) = (term561 A B s f _72878 op).
Proof. exact (TRANS (@lem5789845 A B s f _72878 op) (@lem5789852 A B s f _72878 op)). Qed.
Lemma lem5789856 {A B : Type'} (_72878 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) : term561 A B s f _72878 op.
Proof. exact (EQ_MP (@lem5789853 A B s f _72878 op) (@lem5789842 A B _72878 s f op h1)). Qed.
Lemma lem5789857 {A B : Type'} (_72878 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) : term561 A B s f _72878 op.
Proof. exact (@lem5789856 A B _72878 s f op h1). Qed.
Lemma lem5789858 {A B : Type'} (x : type638 A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) : term562 A B x f s op.
Proof. exact (@lem5789857 A B (term550 A B x op f s) s f op h1). Qed.
Lemma lem5789861 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term0 A B s f op) (h2 : term7 A B) (h3 : term3 A B op f s) (h4 : term518 A B x op f s) (h5 : term384 A x) : (term563 A B x op f s) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5789858 A B x s f op h1 (@lem5789809 A B op f s x h2 h3 h4 h5)). Qed.
Lemma lem5789862 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term0 A B s f op) (h2 : term7 A B) (h3 : term3 A B op f s) (h4 : term518 A B x op f s) (h5 : term384 A x) : term564 A B x f s op.
Proof. exact (fun h0 : term565 A B x f s op => @lem5789861 A B op f s x h1 h2 h3 h4 h5). Qed.
Lemma lem5789864 (p : Prop) : (term539 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5789865 {A B : Type'} (x : type638 A) (f : A -> B) (s : A -> Prop) (op : type1400 B) : (term564 A B x f s op) = ((term563 A B x op f s) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (@lem5789864 ((term563 A B x op f s) = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem5789866 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term0 A B s f op) (h2 : term7 A B) (h3 : term3 A B op f s) (h4 : term518 A B x op f s) (h5 : term384 A x) : (term563 A B x op f s) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (EQ_MP (@lem5789865 A B x f s op) (@lem5789862 A B op f s x h1 h2 h3 h4 h5)). Qed.
Lemma lem5789868 (b : Prop) (a : Prop) : (a \/ b) = (term524 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5789869 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) : (term514 A B _72900 _72898 _72899 _72897) = (term566 A B _72899 _72897 _72898 _72900).
Proof. exact (@lem5789868 (term403 A B _72898 _72899 _72897) (term411 A B _72899 _72897 _72898 _72900)). Qed.
Lemma lem5789871 (a : Prop) : (term544 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5789872 {A B : Type'} (_72898 : A -> B) (_72899 : A) (_72897 : type1400 B) : (term567 A B _72898 _72899 _72897) = ((@I (A -> B) _72898 _72899) = (@I ((B -> B -> B) -> B) (@neutral B) _72897)).
Proof. exact (@lem5789871 ((@I (A -> B) _72898 _72899) = (@I ((B -> B -> B) -> B) (@neutral B) _72897))). Qed.
Lemma lem5789873 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5789874 {A B : Type'} (_72898 : A -> B) (_72899 : A) (_72897 : type1400 B) : (term568 A B _72898 _72899 _72897) = (term569 A B _72898 _72899 _72897).
Proof. exact (MK_COMB (@lem5789873) (@lem5789872 A B _72898 _72899 _72897)). Qed.
Lemma lem5789875 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) : (term411 A B _72899 _72897 _72898 _72900) = (term411 A B _72899 _72897 _72898 _72900).
Proof. exact (eq_refl (term411 A B _72899 _72897 _72898 _72900)). Qed.
Lemma lem5789876 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) : (term566 A B _72899 _72897 _72898 _72900) = (term570 A B _72899 _72897 _72898 _72900).
Proof. exact (MK_COMB (@lem5789874 A B _72898 _72899 _72897) (@lem5789875 A B _72899 _72897 _72898 _72900)). Qed.
Lemma lem5789877 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) : (term514 A B _72900 _72898 _72899 _72897) = (term570 A B _72899 _72897 _72898 _72900).
Proof. exact (TRANS (@lem5789869 A B _72899 _72897 _72898 _72900) (@lem5789876 A B _72899 _72897 _72898 _72900)). Qed.
Lemma lem5789880 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) (h1 : term7 A B) : term570 A B _72899 _72897 _72898 _72900.
Proof. exact (EQ_MP (@lem5789877 A B _72899 _72897 _72898 _72900) (@lem5789168 A B _72900 _72898 _72899 _72897 h1)). Qed.
Lemma lem5789881 {A B : Type'} (_72899 : A) (_72897 : type1400 B) (_72898 : A -> B) (_72900 : A -> Prop) (h1 : term7 A B) : term570 A B _72899 _72897 _72898 _72900.
Proof. exact (@lem5789880 A B _72899 _72897 _72898 _72900 h1). Qed.
Lemma lem5789882 {A B : Type'} (x : type638 A) (s : A -> Prop) (op : type1400 B) (f : A -> B) (_72900 : A -> Prop) (h1 : term7 A B) : term571 A B x s op f _72900.
Proof. exact (@lem5789881 A B (term550 A B x op f s) op f _72900 h1). Qed.
Lemma lem5789885 {A B : Type'} (_72900 : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term0 A B s f op) (h2 : term7 A B) (h3 : term3 A B op f s) (h4 : term518 A B x op f s) (h5 : term384 A x) : term572 A B x s op f _72900.
Proof. exact (@lem5789882 A B x s op f _72900 h2 (@lem5789866 A B op f s x h1 h2 h3 h4 h5)). Qed.
Lemma lem5789886 {A B : Type'} (_72900 : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term0 A B s f op) (h2 : term7 A B) (h3 : term3 A B op f s) (h4 : term518 A B x op f s) (h5 : term384 A x) : term572 A B x s op f _72900.
Proof. exact (@lem5789885 A B _72900 op f s x h1 h2 h3 h4 h5). Qed.
Lemma lem5789887 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term0 A B s f op) (h2 : term7 A B) (h3 : term3 A B op f s) (h4 : term518 A B x op f s) (h5 : term384 A x) : term538 A B x op f s.
Proof. exact (@lem5789886 A B s op f s x h1 h2 h3 h4 h5). Qed.
Lemma lem5789888 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term0 A B s f op) (h2 : term7 A B) (h3 : term3 A B op f s) (h4 : term518 A B x op f s) (h5 : term384 A x) : term573 A B x op f s.
Proof. exact (fun h0 : term536 A B x op f s => @lem5789887 A B op f s x h1 h2 h3 h4 h5). Qed.
Lemma lem5789890 (p : Prop) : (term517 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5789891 {A B : Type'} (x : type638 A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term573 A B x op f s) = (term538 A B x op f s).
Proof. exact (@lem5789890 (term536 A B x op f s)). Qed.
Lemma lem5789892 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term0 A B s f op) (h2 : term7 A B) (h3 : term3 A B op f s) (h4 : term518 A B x op f s) (h5 : term384 A x) : term538 A B x op f s.
Proof. exact (EQ_MP (@lem5789891 A B x op f s) (@lem5789888 A B op f s x h1 h2 h3 h4 h5)). Qed.
Lemma lem5789915 (q : Prop) (p : Prop) (r : Prop) : (term521 p q r) = (term521 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5789916 {A : Type'} (x : type638 A) (_72881 : A -> Prop) (_72880 : A -> Prop) : (term574 A x _72881 _72880) = (term575 A x _72881 _72880).
Proof. exact (@lem5789915 (_72880 = _72881) (term461 A x _72880 _72881) (term467 A x _72881 _72880)). Qed.
Lemma lem5789932 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5789933 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : (term576 A x _72881 _72880) = (term477 A x _72880 _72881).
Proof. exact (@lem5789932 (term467 A x _72881 _72880) (term461 A x _72880 _72881)). Qed.
Lemma lem5789939 {A : Type'} (_72880 : A -> Prop) (_72881 : A -> Prop) : (term221 A _72880 _72881) = (term221 A _72880 _72881).
Proof. exact (eq_refl (term221 A _72880 _72881)). Qed.
Lemma lem5789940 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : (term575 A x _72881 _72880) = (term515 A x _72880 _72881).
Proof. exact (MK_COMB (@lem5789939 A _72880 _72881) (@lem5789933 A x _72880 _72881)). Qed.
Lemma lem5789951 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : (term574 A x _72881 _72880) = (term515 A x _72880 _72881).
Proof. exact (TRANS (@lem5789916 A x _72881 _72880) (@lem5789940 A x _72880 _72881)). Qed.
Lemma lem5789952 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : (term523 A x _72880 _72881) = (term523 A x _72880 _72881).
Proof. exact (eq_refl (term523 A x _72880 _72881)). Qed.
Lemma lem5789953 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : ((term515 A x _72880 _72881) = (term574 A x _72881 _72880)) = ((term515 A x _72880 _72881) = (term515 A x _72880 _72881)).
Proof. exact (MK_COMB (@lem5789952 A x _72880 _72881) (@lem5789951 A x _72880 _72881)). Qed.
Lemma lem5789955 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5789956 (x : Prop) : (x = x) = True.
Proof. exact (@lem5789955 Prop x). Qed.
Lemma lem5789957 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : ((term515 A x _72880 _72881) = (term515 A x _72880 _72881)) = True.
Proof. exact (@lem5789956 (term515 A x _72880 _72881)). Qed.
Lemma lem5789958 {A : Type'} (x : type638 A) (_72881 : A -> Prop) (_72880 : A -> Prop) : ((term515 A x _72880 _72881) = (term574 A x _72881 _72880)) = True.
Proof. exact (TRANS (@lem5789953 A x _72880 _72881) (@lem5789957 A x _72880 _72881)). Qed.
Lemma lem5789959 {A : Type'} (x : type638 A) (_72881 : A -> Prop) (_72880 : A -> Prop) : True = ((term515 A x _72880 _72881) = (term574 A x _72881 _72880)).
Proof. exact (SYM (@lem5789958 A x _72881 _72880)). Qed.
Lemma lem5789960 {A : Type'} (x : type638 A) (_72881 : A -> Prop) (_72880 : A -> Prop) : (term515 A x _72880 _72881) = (term574 A x _72881 _72880).
Proof. exact (EQ_MP (@lem5789959 A x _72881 _72880) (@lem0)). Qed.
Lemma lem5789961 {A : Type'} (_72881 : A -> Prop) (_72880 : A -> Prop) (x : type638 A) (h1 : term384 A x) : term574 A x _72881 _72880.
Proof. exact (EQ_MP (@lem5789960 A x _72881 _72880) (@lem5789210 A _72880 _72881 x h1)). Qed.
Lemma lem5789963 (b : Prop) (a : Prop) : (a \/ b) = (term524 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5789964 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : (term574 A x _72881 _72880) = (term577 A x _72880 _72881).
Proof. exact (@lem5789963 (term578 A x _72881 _72880) (term461 A x _72880 _72881)). Qed.
Lemma lem5789966 (a : Prop) (b : Prop) : (term527 a b) = (term528 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5789967 {A : Type'} (x : type638 A) (_72881 : A -> Prop) (_72880 : A -> Prop) : (term579 A x _72881 _72880) = (term580 A x _72881 _72880).
Proof. exact (@lem5789966 (_72880 = _72881) (term467 A x _72881 _72880)). Qed.
Lemma lem5789968 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5789969 {A : Type'} (x : type638 A) (_72881 : A -> Prop) (_72880 : A -> Prop) : (term581 A x _72881 _72880) = (term582 A x _72881 _72880).
Proof. exact (MK_COMB (@lem5789968) (@lem5789967 A x _72881 _72880)). Qed.
Lemma lem5789970 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : (term461 A x _72880 _72881) = (term461 A x _72880 _72881).
Proof. exact (eq_refl (term461 A x _72880 _72881)). Qed.
Lemma lem5789971 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : (term577 A x _72880 _72881) = (term583 A x _72880 _72881).
Proof. exact (MK_COMB (@lem5789969 A x _72881 _72880) (@lem5789970 A x _72880 _72881)). Qed.
Lemma lem5789972 {A : Type'} (x : type638 A) (_72880 : A -> Prop) (_72881 : A -> Prop) : (term574 A x _72881 _72880) = (term583 A x _72880 _72881).
Proof. exact (TRANS (@lem5789964 A x _72880 _72881) (@lem5789971 A x _72880 _72881)). Qed.
Lemma lem5789974 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term0 A B s f op) (h2 : term7 A B) (h3 : term3 A B op f s) (h4 : term518 A B x op f s) (h5 : term384 A x) : term584 A B x op f s.
Proof. exact (conj (@lem5789665 A B op f s h3) (@lem5789892 A B op f s x h1 h2 h3 h4 h5)). Qed.
Lemma lem5789976 {A : Type'} (_72880 : A -> Prop) (_72881 : A -> Prop) (x : type638 A) (h1 : term384 A x) : term583 A x _72880 _72881.
Proof. exact (EQ_MP (@lem5789972 A x _72880 _72881) (@lem5789961 A _72881 _72880 x h1)). Qed.
Lemma lem5789977 {A : Type'} (_72880 : A -> Prop) (_72881 : A -> Prop) (x : type638 A) (h1 : term384 A x) : term583 A x _72880 _72881.
Proof. exact (@lem5789976 A _72880 _72881 x h1). Qed.
Lemma lem5789978 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term384 A x) : term585 A B x op f s.
Proof. exact (@lem5789977 A (term399 A B op f s) (@EMPTY A) x h1). Qed.
Lemma lem5789981 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term0 A B s f op) (h2 : term7 A B) (h3 : term3 A B op f s) (h4 : term518 A B x op f s) (h5 : term384 A x) : term520 A B x op f s.
Proof. exact (@lem5789978 A B op f s x h5 (@lem5789974 A B op f s x h1 h2 h3 h4 h5)). Qed.
Lemma lem5789982 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term0 A B s f op) (h2 : term7 A B) (h3 : term3 A B op f s) (h4 : term384 A x) : term586 A B x op f s.
Proof. exact (fun h0 : term518 A B x op f s => @lem5789981 A B op f s x h1 h2 h3 h0 h4). Qed.
Lemma lem5789984 (p : Prop) : (term539 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5789985 {A B : Type'} (x : type638 A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term586 A B x op f s) = (term520 A B x op f s).
Proof. exact (@lem5789984 (term520 A B x op f s)). Qed.
Lemma lem5789986 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term0 A B s f op) (h2 : term7 A B) (h3 : term3 A B op f s) (h4 : term384 A x) : term520 A B x op f s.
Proof. exact (EQ_MP (@lem5789985 A B x op f s) (@lem5789982 A B op f s x h1 h2 h3 h4)). Qed.
Lemma lem5789989 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5789991 {A : Type'} (_72879 : A) : (term436 A _72879) = (term587 A _72879).
Proof. exact (@lem5789989 (term435 A _72879)). Qed.
Lemma lem5789994 {A : Type'} (_72879 : A) (h1 : term5 A) : term587 A _72879.
Proof. exact (EQ_MP (@lem5789991 A _72879) (@lem5789092 A _72879 h1)). Qed.
Lemma lem5789995 {A : Type'} (_72879 : A) (h1 : term5 A) : term587 A _72879.
Proof. exact (@lem5789994 A _72879 h1). Qed.
Lemma lem5789996 {A B : Type'} (x : type638 A) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term5 A) : term588 A B x op f s.
Proof. exact (@lem5789995 A (term550 A B x op f s) h1). Qed.
Lemma lem5789999 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term5 A) (h2 : term0 A B s f op) (h3 : term7 A B) (h4 : term3 A B op f s) (h5 : term384 A x) : False.
Proof. exact (@lem5789996 A B x op f s h1 (@lem5789986 A B op f s x h2 h3 h4 h5)). Qed.
Lemma lem5790000 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term5 A) (h2 : term0 A B s f op) (h3 : term7 A B) (h4 : term3 A B op f s) (h5 : term384 A x) : term589.
Proof. exact (fun h0 : ~ False => @lem5789999 A B op f s x h1 h2 h3 h4 h5). Qed.
Lemma lem5790002 (p : Prop) : (term539 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5790003 : term589 = False.
Proof. exact (@lem5790002 False). Qed.
Lemma lem5790004 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (x : type638 A) (h1 : term5 A) (h2 : term0 A B s f op) (h3 : term7 A B) (h4 : term3 A B op f s) (h5 : term384 A x) : False.
Proof. exact (EQ_MP (@lem5790003) (@lem5790000 A B op f s x h1 h2 h3 h4 h5)). Qed.
Lemma lem5790005 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term5 A) (h2 : term0 A B s f op) (h3 : term4 A) (h4 : term7 A B) (h5 : term3 A B op f s) : False.
Proof. exact (ex_elim (@lem5787363 A h3) (fun x : type638 A => fun h0 : term386 A x => @lem5790004 A B op f s x h1 h2 h4 h5 h0)). Qed.
Lemma lem5790006 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term5 A) (h2 : term0 A B s f op) (h3 : term4 A) (h4 : term7 A B) (h5 : term3 A B op f s) : (term5 A) = False.
Proof. exact (prop_ext (fun h6 : term5 A => @lem5790005 A B op f s h1 h2 h3 h4 h5) (fun h6 : False => @lem5786552 A h1)). Qed.
Lemma lem5790007 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term5 A) (h2 : term0 A B s f op) (h3 : term4 A) (h4 : term7 A B) (h5 : term3 A B op f s) : False.
Proof. exact (EQ_MP (@lem5790006 A B op f s h1 h2 h3 h4 h5) (@lem5786552 A h1)). Qed.
Lemma lem5790008 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term5 A) (h2 : term0 A B s f op) (h3 : term4 A) (h4 : term7 A B) (h5 : term3 A B op f s) : (term3 A B op f s) = False.
Proof. exact (prop_ext (fun h6 : term3 A B op f s => @lem5790007 A B op f s h1 h2 h3 h4 h5) (fun h6 : False => @lem5784111 A B op f s h5)). Qed.
Lemma lem5790009 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term5 A) (h2 : term0 A B s f op) (h3 : term4 A) (h4 : term7 A B) (h5 : term3 A B op f s) : False.
Proof. exact (EQ_MP (@lem5790008 A B op f s h1 h2 h3 h4 h5) (@lem5784111 A B op f s h5)). Qed.
Lemma lem5790010 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term5 A) (h2 : term0 A B s f op) (h3 : term7 A B) (h4 : term3 A B op f s) : term13 A.
Proof. exact (fun h0 : term4 A => @lem5790009 A B op f s h1 h2 h0 h3 h4). Qed.
Lemma lem5790011 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (@lem69 (term4 A)). Qed.
Lemma lem5790012 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term5 A) (h2 : term0 A B s f op) (h3 : term7 A B) (h4 : term3 A B op f s) : term14 A.
Proof. exact (EQ_MP (@lem5790011 A) (@lem5790010 A B op f s h1 h2 h3 h4)). Qed.
Lemma lem5790013 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : term7 A B) (h3 : term3 A B op f s) : term17 A.
Proof. exact (fun h0 : term5 A => @lem5790012 A B op f s h0 h1 h2 h3). Qed.
Lemma lem5790014 {_119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : term7 A B) (h3 : term3 A B op f s) : term20 _119829 A.
Proof. exact (fun h0 : term8 _119829 A => @lem5790013 A B op f s h1 h2 h3). Qed.
Lemma lem5790015 {_119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : term3 A B op f s) : term23 _119829 A B.
Proof. exact (fun h0 : term7 A B => @lem5790014 _119829 A B op f s h1 h0 h2). Qed.
Lemma lem5790016 {_119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : term3 A B op f s) : term25 _119829 A B.
Proof. exact (fun h0 : term7 _119829 B => @lem5790015 _119829 A B op f s h1 h2). Qed.
Lemma lem5790017 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : term3 A B op f s) : term28 _119826 _119829 A B.
Proof. exact (fun h0 : term6 _119826 A => @lem5790016 _119829 A B op f s h1 h2). Qed.
Lemma lem5790018 {_119826 _119829 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) : term31 _119826 _119829 A B op f s.
Proof. exact (fun h0 : term3 A B op f s => @lem5790017 _119826 _119829 A B op f s h1 h0). Qed.
Lemma lem5790019 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : term34 _119826 _119829 A B op f s.
Proof. exact (fun h0 : term0 A B s f op => @lem5790018 _119826 _119829 A B s f op h0). Qed.
Lemma lem5790020 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : term36 _119826 _119829 A B op f s.
Proof. exact (fun h0 : @monoidal B op => @lem5790019 _119826 _119829 A B op f s). Qed.
Lemma lem5790025 {_119826 _119829 A B : Type'} (f : A -> B) (s : A -> Prop) : term40 _119826 _119829 A B f s.
Proof. exact (fun op : type1400 B => @lem5790020 _119826 _119829 A B op f s). Qed.
Lemma lem5790030 {_119826 _119829 A B : Type'} (s : A -> Prop) : term44 _119826 _119829 A B s.
Proof. exact (fun f : A -> B => @lem5790025 _119826 _119829 A B f s). Qed.
Lemma lem5790035 {_119826 _119829 A B : Type'} : term48 _119826 _119829 A B.
Proof. exact (fun s : A -> Prop => @lem5790030 _119826 _119829 A B s). Qed.
Lemma lem5790036 {_119826 _119829 A B : Type'} : term47 _119826 _119829 A B.
Proof. exact (EQ_MP (@lem5784027 _119826 _119829 A B) (@lem5790035 _119826 _119829 A B)). Qed.
Lemma lem5790037 {_119826 _119829 A B : Type'} (s : A -> Prop) : term590 _119826 _119829 A B s.
Proof. exact (@lem5790036 _119826 _119829 A B s). Qed.
Lemma lem5790038 {_119826 _119829 A B : Type'} (s : A -> Prop) : (term590 _119826 _119829 A B s) = (term43 _119826 _119829 A B s).
Proof. exact (eq_refl (term590 _119826 _119829 A B s)). Qed.
Lemma lem5790039 {_119826 _119829 A B : Type'} (s : A -> Prop) : term43 _119826 _119829 A B s.
Proof. exact (EQ_MP (@lem5790038 _119826 _119829 A B s) (@lem5790037 _119826 _119829 A B s)). Qed.
Lemma lem5790040 {_119826 _119829 A B : Type'} (s : A -> Prop) (f : A -> B) : term591 _119826 _119829 A B s f.
Proof. exact (@lem5790039 _119826 _119829 A B s f). Qed.
Lemma lem5790041 {_119826 _119829 A B : Type'} (f : A -> B) (s : A -> Prop) : (term591 _119826 _119829 A B s f) = (term39 _119826 _119829 A B f s).
Proof. exact (eq_refl (term591 _119826 _119829 A B s f)). Qed.
Lemma lem5790042 {_119826 _119829 A B : Type'} (f : A -> B) (s : A -> Prop) : term39 _119826 _119829 A B f s.
Proof. exact (EQ_MP (@lem5790041 _119826 _119829 A B f s) (@lem5790040 _119826 _119829 A B s f)). Qed.
Lemma lem5790043 {_119826 _119829 A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) : term592 _119826 _119829 A B f s op.
Proof. exact (@lem5790042 _119826 _119829 A B f s op). Qed.
Lemma lem5790044 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term592 _119826 _119829 A B f s op) = (term9 _119826 _119829 A B op f s).
Proof. exact (eq_refl (term592 _119826 _119829 A B f s op)). Qed.
Lemma lem5790045 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : term9 _119826 _119829 A B op f s.
Proof. exact (EQ_MP (@lem5790044 _119826 _119829 A B op f s) (@lem5790043 _119826 _119829 A B f s op)). Qed.
Lemma lem5790047 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : term9 _119826 _119829 A B op f s.
Proof. exact (@lem5783508 _119826 _119829 A B op f s (@lem5790045 _119826 _119829 A B op f s)). Qed.
Lemma lem5790048 {_119826 _119829 A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term33 _119826 _119829 A B op f s.
Proof. exact (@lem5790047 _119826 _119829 A B op f s (@lem5783476 B op h1)). Qed.
Lemma lem5790049 {_119826 _119829 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) (h2 : @monoidal B op) : term30 _119826 _119829 A B op f s.
Proof. exact (@lem5790048 _119826 _119829 A B f s op h2 (@lem5783477 A B s f op h1)). Qed.
Lemma lem5790050 {_119826 _119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term3 A B op f s) : term27 _119826 _119829 A B.
Proof. exact (@lem5790049 _119826 _119829 A B s f op h1 h2 (@lem5783483 A B op f s h3)). Qed.
Lemma lem5790051 {_119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term3 A B op f s) : term24 _119829 A B.
Proof. exact (@lem5790050 Prop _119829 A B op f s h1 h2 h3 (@lem5783488 Prop A)). Qed.
Lemma lem5790052 {_119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term3 A B op f s) : term22 _119829 A B.
Proof. exact (@lem5790051 _119829 A B op f s h1 h2 h3 (@lem5783490 _119829 B)). Qed.
Lemma lem5790053 {_119829 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term3 A B op f s) : term19 _119829 A.
Proof. exact (@lem5790052 _119829 A B op f s h1 h2 h3 (@lem5783489 A B)). Qed.
Lemma lem5790054 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term3 A B op f s) : term16 A.
Proof. exact (@lem5790053 Prop A B op f s h1 h2 h3 (@lem5783491 Prop A)). Qed.
Lemma lem5790055 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term3 A B op f s) : term13 A.
Proof. exact (@lem5790054 A B op f s h1 h2 h3 (@lem5783486 A)). Qed.
Lemma lem5790056 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term3 A B op f s) : False.
Proof. exact (@lem5790055 A B op f s h1 h2 h3 (@lem5783484 A)). Qed.
Lemma lem5790057 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term3 A B op f s) : (term3 A B op f s) = False.
Proof. exact (prop_ext (fun h4 : term3 A B op f s => @lem5790056 A B op f s h1 h2 h3) (fun h4 : False => @lem5783483 A B op f s h3)). Qed.
Lemma lem5790058 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term3 A B op f s) : False.
Proof. exact (EQ_MP (@lem5790057 A B op f s h1 h2 h3) (@lem5783483 A B op f s h3)). Qed.
Lemma lem5790059 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) (h2 : @monoidal B op) : term2 A B op f s.
Proof. exact (fun h0 : term3 A B op f s => @lem5790058 A B op f s h1 h2 h0). Qed.
Lemma lem5790060 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) (h2 : @monoidal B op) : (@support A B op f s) = (@EMPTY A).
Proof. exact (EQ_MP (@lem5783482 A B op f s) (@lem5790059 A B s f op h1 h2)). Qed.
Lemma lem5790062 (p : Prop) : p = (term1 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5790063 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : ((@iterate B A op s f) = (@neutral B op)) = (term593 A B s f op).
Proof. exact (@lem5790062 ((@iterate B A op s f) = (@neutral B op))). Qed.
Lemma lem5790064 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term593 A B s f op) = ((@iterate B A op s f) = (@neutral B op)).
Proof. exact (SYM (@lem5790063 A B s f op)). Qed.
Lemma lem5790065 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term594 A B s f op) : term594 A B s f op.
Proof. exact (h1). Qed.
Lemma lem5790066 {_120477 _120521 B : Type'} : term595 _120477 _120521 B.
Proof. exact (@lem5753565 _120477 B _120521). Qed.
Lemma lem5790068 {_120477 _120521 A : Type'} : term596 _120477 _120521 A.
Proof. exact (@lem5753565 _120477 (A -> Prop) _120521). Qed.
Lemma lem5790069 {_120521 A B : Type'} : term597 _120521 A B.
Proof. exact (@lem5753565 A B _120521). Qed.
Lemma lem5790070 {_120519 _120521 A : Type'} : term598 _120519 _120521 A.
Proof. exact (@lem5753565 A _120519 _120521). Qed.
Lemma lem5790072 {_120477 A B : Type'} : term595 _120477 A B.
Proof. exact (@lem5753565 _120477 B A). Qed.
Lemma lem5790073 {_120477 _120519 A : Type'} : term599 _120477 _120519 A.
Proof. exact (@lem5753565 _120477 _120519 A). Qed.
Lemma lem5790074 {_120521 : Type'} : term600 _120521.
Proof. exact (@lem3197565 _120521). Qed.
Lemma lem5790075 {A : Type'} : term600 A.
Proof. exact (@lem3197565 A). Qed.
Lemma lem5790077 {_120477 : Type'} : term600 _120477.
Proof. exact (@lem3197565 _120477). Qed.
Lemma lem5790080 {_120308 B : Type'} : term601 _120308 B.
Proof. exact (@lem5737860 B _120308). Qed.
Lemma lem5790081 {_120308 A : Type'} : term602 _120308 A.
Proof. exact (@lem5737860 (A -> Prop) _120308). Qed.
Lemma lem5790082 {_120308 _120519 : Type'} : term601 _120308 _120519.
Proof. exact (@lem5737860 _120519 _120308). Qed.
Lemma lem5790083 {A B : Type'} : term601 A B.
Proof. exact (@lem5737860 B A). Qed.
Lemma lem5790084 {_120477 A : Type'} : term602 _120477 A.
Proof. exact (@lem5737860 (A -> Prop) _120477). Qed.
Lemma lem5790085 {_120521 A : Type'} : term602 _120521 A.
Proof. exact (@lem5737860 (A -> Prop) _120521). Qed.
Lemma lem5790086 {_120521 B : Type'} : term601 _120521 B.
Proof. exact (@lem5737860 B _120521). Qed.
Lemma lem5790087 {_120477 B : Type'} : term601 _120477 B.
Proof. exact (@lem5737860 B _120477). Qed.
Lemma lem5790088 {_120519 A : Type'} : term603 _120519 A.
Proof. exact (@lem5737860 _120519 A). Qed.
Lemma lem5790089 {_120519 _120521 : Type'} : term603 _120519 _120521.
Proof. exact (@lem5737860 _120519 _120521). Qed.
Lemma lem5790090 {_120477 _120519 : Type'} : term601 _120477 _120519.
Proof. exact (@lem5737860 _120519 _120477). Qed.
Lemma lem5790094 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term604 _120308 _120477 _120519 _120521 A B s f op) : term604 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (h1). Qed.
Lemma lem5790095 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term605 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (fun h0 : term604 _120308 _120477 _120519 _120521 A B s f op => @lem5790094 _120308 _120477 _120519 _120521 A B s f op h0). Qed.
Lemma lem5790096 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term605 _120308 _120477 _120519 _120521 A B s f op) : term605 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (h1). Qed.
Lemma lem5790097 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term604 _120308 _120477 _120519 _120521 A B s f op) : term604 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (h1). Qed.
Lemma lem5790098 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term604 _120308 _120477 _120519 _120521 A B s f op) (h2 : term605 _120308 _120477 _120519 _120521 A B s f op) : term604 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (@lem5790096 _120308 _120477 _120519 _120521 A B s f op h2 (@lem5790097 _120308 _120477 _120519 _120521 A B s f op h1)). Qed.
Lemma lem5790099 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term604 _120308 _120477 _120519 _120521 A B s f op) : term606 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (fun h0 : term605 _120308 _120477 _120519 _120521 A B s f op => @lem5790098 _120308 _120477 _120519 _120521 A B s f op h1 h0). Qed.
Lemma lem5790100 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term605 _120308 _120477 _120519 _120521 A B s f op) : term605 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (h1). Qed.
Lemma lem5790101 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term604 _120308 _120477 _120519 _120521 A B s f op) (h2 : term605 _120308 _120477 _120519 _120521 A B s f op) : term604 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (@lem5790099 _120308 _120477 _120519 _120521 A B s f op h1 (@lem5790100 _120308 _120477 _120519 _120521 A B s f op h2)). Qed.
Lemma lem5790102 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term605 _120308 _120477 _120519 _120521 A B s f op) : term605 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (fun h0 : term604 _120308 _120477 _120519 _120521 A B s f op => @lem5790101 _120308 _120477 _120519 _120521 A B s f op h0 h1). Qed.
Lemma lem5790103 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term607 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (fun h0 : term605 _120308 _120477 _120519 _120521 A B s f op => @lem5790102 _120308 _120477 _120519 _120521 A B s f op h0). Qed.
Lemma lem5790106 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term605 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (@lem5790103 _120308 _120477 _120519 _120521 A B s f op (@lem5790095 _120308 _120477 _120519 _120521 A B s f op)). Qed.
Lemma lem5790107 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term605 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (@lem5790106 _120308 _120477 _120519 _120521 A B s f op). Qed.
Lemma lem5790471 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5790472 {_120477 _120521 A : Type'} : (term608 _120477 _120521 A) = (term609 _120477 _120521 A).
Proof. exact (@lem5790471 (term596 _120477 _120521 A)). Qed.
Lemma lem5790499 {_120521 A B : Type'} : (term610 _120521 A B) = (term610 _120521 A B).
Proof. exact (eq_refl (term610 _120521 A B)). Qed.
Lemma lem5790500 {_120477 _120521 A B : Type'} : (term611 _120477 _120521 A B) = (term612 _120477 _120521 A B).
Proof. exact (MK_COMB (@lem5790499 _120521 A B) (@lem5790472 _120477 _120521 A)). Qed.
Lemma lem5790503 {_120477 A B : Type'} : (term613 _120477 A B) = (term613 _120477 A B).
Proof. exact (eq_refl (term613 _120477 A B)). Qed.
Lemma lem5790504 {_120477 _120521 A B : Type'} : (term614 _120477 _120521 A B) = (term615 _120477 _120521 A B).
Proof. exact (MK_COMB (@lem5790503 _120477 A B) (@lem5790500 _120477 _120521 A B)). Qed.
Lemma lem5790507 {_120477 _120521 B : Type'} : (term613 _120477 _120521 B) = (term613 _120477 _120521 B).
Proof. exact (eq_refl (term613 _120477 _120521 B)). Qed.
Lemma lem5790508 {_120477 _120521 A B : Type'} : (term616 _120477 _120521 A B) = (term617 _120477 _120521 A B).
Proof. exact (MK_COMB (@lem5790507 _120477 _120521 B) (@lem5790504 _120477 _120521 A B)). Qed.
Lemma lem5790511 {_120519 _120521 A : Type'} : (term618 _120519 _120521 A) = (term618 _120519 _120521 A).
Proof. exact (eq_refl (term618 _120519 _120521 A)). Qed.
Lemma lem5790512 {_120477 _120519 _120521 A B : Type'} : (term619 _120477 _120519 _120521 A B) = (term620 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790511 _120519 _120521 A) (@lem5790508 _120477 _120521 A B)). Qed.
Lemma lem5790515 {_120477 _120519 A : Type'} : (term621 _120477 _120519 A) = (term621 _120477 _120519 A).
Proof. exact (eq_refl (term621 _120477 _120519 A)). Qed.
Lemma lem5790516 {_120477 _120519 _120521 A B : Type'} : (term622 _120477 _120519 _120521 A B) = (term623 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790515 _120477 _120519 A) (@lem5790512 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790519 {A : Type'} : (term624 A) = (term624 A).
Proof. exact (eq_refl (term624 A)). Qed.
Lemma lem5790520 {_120477 _120519 _120521 A B : Type'} : (term625 _120477 _120519 _120521 A B) = (term626 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790519 A) (@lem5790516 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790523 {_120521 : Type'} : (term624 _120521) = (term624 _120521).
Proof. exact (eq_refl (term624 _120521)). Qed.
Lemma lem5790524 {_120477 _120519 _120521 A B : Type'} : (term627 _120477 _120519 _120521 A B) = (term628 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790523 _120521) (@lem5790520 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790527 {_120477 : Type'} : (term624 _120477) = (term624 _120477).
Proof. exact (eq_refl (term624 _120477)). Qed.
Lemma lem5790528 {_120477 _120519 _120521 A B : Type'} : (term629 _120477 _120519 _120521 A B) = (term630 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790527 _120477) (@lem5790524 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790531 {_120521 A : Type'} : (term631 _120521 A) = (term631 _120521 A).
Proof. exact (eq_refl (term631 _120521 A)). Qed.
Lemma lem5790532 {_120477 _120519 _120521 A B : Type'} : (term632 _120477 _120519 _120521 A B) = (term633 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790531 _120521 A) (@lem5790528 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790535 {_120477 A : Type'} : (term631 _120477 A) = (term631 _120477 A).
Proof. exact (eq_refl (term631 _120477 A)). Qed.
Lemma lem5790536 {_120477 _120519 _120521 A B : Type'} : (term634 _120477 _120519 _120521 A B) = (term635 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790535 _120477 A) (@lem5790532 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790539 {_120308 A : Type'} : (term631 _120308 A) = (term631 _120308 A).
Proof. exact (eq_refl (term631 _120308 A)). Qed.
Lemma lem5790540 {_120308 _120477 _120519 _120521 A B : Type'} : (term636 _120308 _120477 _120519 _120521 A B) = (term637 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790539 _120308 A) (@lem5790536 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790543 {A B : Type'} : (term638 A B) = (term638 A B).
Proof. exact (eq_refl (term638 A B)). Qed.
Lemma lem5790544 {_120308 _120477 _120519 _120521 A B : Type'} : (term639 _120308 _120477 _120519 _120521 A B) = (term640 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790543 A B) (@lem5790540 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790547 {_120521 B : Type'} : (term638 _120521 B) = (term638 _120521 B).
Proof. exact (eq_refl (term638 _120521 B)). Qed.
Lemma lem5790548 {_120308 _120477 _120519 _120521 A B : Type'} : (term641 _120308 _120477 _120519 _120521 A B) = (term642 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790547 _120521 B) (@lem5790544 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790551 {_120477 B : Type'} : (term638 _120477 B) = (term638 _120477 B).
Proof. exact (eq_refl (term638 _120477 B)). Qed.
Lemma lem5790552 {_120308 _120477 _120519 _120521 A B : Type'} : (term643 _120308 _120477 _120519 _120521 A B) = (term644 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790551 _120477 B) (@lem5790548 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790555 {_120308 B : Type'} : (term638 _120308 B) = (term638 _120308 B).
Proof. exact (eq_refl (term638 _120308 B)). Qed.
Lemma lem5790556 {_120308 _120477 _120519 _120521 A B : Type'} : (term645 _120308 _120477 _120519 _120521 A B) = (term646 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790555 _120308 B) (@lem5790552 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790559 {_120519 A : Type'} : (term647 _120519 A) = (term647 _120519 A).
Proof. exact (eq_refl (term647 _120519 A)). Qed.
Lemma lem5790560 {_120308 _120477 _120519 _120521 A B : Type'} : (term648 _120308 _120477 _120519 _120521 A B) = (term649 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790559 _120519 A) (@lem5790556 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790563 {_120519 _120521 : Type'} : (term647 _120519 _120521) = (term647 _120519 _120521).
Proof. exact (eq_refl (term647 _120519 _120521)). Qed.
Lemma lem5790564 {_120308 _120477 _120519 _120521 A B : Type'} : (term650 _120308 _120477 _120519 _120521 A B) = (term651 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790563 _120519 _120521) (@lem5790560 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790567 {_120477 _120519 : Type'} : (term638 _120477 _120519) = (term638 _120477 _120519).
Proof. exact (eq_refl (term638 _120477 _120519)). Qed.
Lemma lem5790568 {_120308 _120477 _120519 _120521 A B : Type'} : (term652 _120308 _120477 _120519 _120521 A B) = (term653 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790567 _120477 _120519) (@lem5790564 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790571 {_120308 _120519 : Type'} : (term638 _120308 _120519) = (term638 _120308 _120519).
Proof. exact (eq_refl (term638 _120308 _120519)). Qed.
Lemma lem5790572 {_120308 _120477 _120519 _120521 A B : Type'} : (term654 _120308 _120477 _120519 _120521 A B) = (term655 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790571 _120308 _120519) (@lem5790568 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790575 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term656 A B s f op) = (term656 A B s f op).
Proof. exact (eq_refl (term656 A B s f op)). Qed.
Lemma lem5790576 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term657 _120308 _120477 _120519 _120521 A B s f op) = (term658 _120308 _120477 _120519 _120521 A B s f op).
Proof. exact (MK_COMB (@lem5790575 A B s f op) (@lem5790572 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790579 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term659 A B op f s) = (term659 A B op f s).
Proof. exact (eq_refl (term659 A B op f s)). Qed.
Lemma lem5790580 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term660 _120308 _120477 _120519 _120521 A B s f op) = (term661 _120308 _120477 _120519 _120521 A B s f op).
Proof. exact (MK_COMB (@lem5790579 A B op f s) (@lem5790576 _120308 _120477 _120519 _120521 A B s f op)). Qed.
Lemma lem5790583 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term32 A B s f op) = (term32 A B s f op).
Proof. exact (eq_refl (term32 A B s f op)). Qed.
Lemma lem5790584 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term662 _120308 _120477 _120519 _120521 A B s f op) = (term663 _120308 _120477 _120519 _120521 A B s f op).
Proof. exact (MK_COMB (@lem5790583 A B s f op) (@lem5790580 _120308 _120477 _120519 _120521 A B s f op)). Qed.
Lemma lem5790587 {B : Type'} (op : type1400 B) : (term35 B op) = (term35 B op).
Proof. exact (eq_refl (term35 B op)). Qed.
Lemma lem5790588 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term604 _120308 _120477 _120519 _120521 A B s f op) = (term664 _120308 _120477 _120519 _120521 A B s f op).
Proof. exact (MK_COMB (@lem5790587 B op) (@lem5790584 _120308 _120477 _120519 _120521 A B s f op)). Qed.
Lemma lem5790591 {_120308 _120477 _120519 _120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term665 _120308 _120477 _120519 _120521 A B f op) = (term666 _120308 _120477 _120519 _120521 A B f op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5790588 _120308 _120477 _120519 _120521 A B s f op)). Qed.
Lemma lem5790592 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5790593 {_120308 _120477 _120519 _120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term667 _120308 _120477 _120519 _120521 A B f op) = (term668 _120308 _120477 _120519 _120521 A B f op).
Proof. exact (MK_COMB (@lem5790592 A) (@lem5790591 _120308 _120477 _120519 _120521 A B f op)). Qed.
Lemma lem5790598 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) : (term669 _120308 _120477 _120519 _120521 A B op) = (term670 _120308 _120477 _120519 _120521 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5790593 _120308 _120477 _120519 _120521 A B f op)). Qed.
Lemma lem5790599 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5790600 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) : (term671 _120308 _120477 _120519 _120521 A B op) = (term672 _120308 _120477 _120519 _120521 A B op).
Proof. exact (MK_COMB (@lem5790599 A B) (@lem5790598 _120308 _120477 _120519 _120521 A B op)). Qed.
Lemma lem5790605 {_120308 _120477 _120519 _120521 A B : Type'} : (term673 _120308 _120477 _120519 _120521 A B) = (term674 _120308 _120477 _120519 _120521 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5790600 _120308 _120477 _120519 _120521 A B op)). Qed.
Lemma lem5790606 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5790615 {_120308 _120477 _120519 _120521 A B : Type'} : (term675 _120308 _120477 _120519 _120521 A B) = (term676 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5790606 B) (@lem5790605 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5790619 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (@IN _120521 x s) = False.
Proof. exact (h1). Qed.
Lemma lem5790620 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem5790621 {_120521 A : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term677 _120521 A x s) = (@COND (A -> Prop) False).
Proof. exact (MK_COMB (@lem5790620 A) (@lem5790619 _120521 x s h1)). Qed.
Lemma lem5790622 {_120521 A : Type'} (op : type636 A) (s : _120521 -> Prop) (f : type1413 _120521 A) : (@iterate (A -> Prop) _120521 op s f) = (@iterate (A -> Prop) _120521 op s f).
Proof. exact (eq_refl (@iterate (A -> Prop) _120521 op s f)). Qed.
Lemma lem5790623 {_120521 A : Type'} (op : type636 A) (f : type1413 _120521 A) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term678 _120521 A x op s f) = (term679 _120521 A op s f).
Proof. exact (MK_COMB (@lem5790621 _120521 A x s h1) (@lem5790622 _120521 A op s f)). Qed.
Lemma lem5790624 {_120521 A : Type'} (x : _120521) (op : type636 A) (s : _120521 -> Prop) (f : type1413 _120521 A) : (term680 _120521 A x op s f) = (term680 _120521 A x op s f).
Proof. exact (eq_refl (term680 _120521 A x op s f)). Qed.
Lemma lem5790625 {_120521 A : Type'} (op : type636 A) (f : type1413 _120521 A) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term681 _120521 A x op s f) = (term682 _120521 A x op s f).
Proof. exact (MK_COMB (@lem5790623 _120521 A op f x s h1) (@lem5790624 _120521 A x op s f)). Qed.
Lemma lem5790627 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5790628 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (@COND (A -> Prop) False t1 t2) = t2.
Proof. exact (@lem5790627 (A -> Prop) t1 t2). Qed.
Lemma lem5790629 {_120521 A : Type'} (x : _120521) (op : type636 A) (s : _120521 -> Prop) (f : type1413 _120521 A) : (term682 _120521 A x op s f) = (term680 _120521 A x op s f).
Proof. exact (@lem5790628 A (@iterate (A -> Prop) _120521 op s f) (term680 _120521 A x op s f)). Qed.
Lemma lem5790630 {_120521 A : Type'} (op : type636 A) (f : type1413 _120521 A) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term681 _120521 A x op s f) = (term680 _120521 A x op s f).
Proof. exact (TRANS (@lem5790625 _120521 A op f x s h1) (@lem5790629 _120521 A x op s f)). Qed.
Lemma lem5790631 {_120521 A : Type'} (op : type636 A) (x : _120521) (s : _120521 -> Prop) (f : type1413 _120521 A) : (term683 _120521 A op x s f) = (term683 _120521 A op x s f).
Proof. exact (eq_refl (term683 _120521 A op x s f)). Qed.
Lemma lem5790632 {_120521 A : Type'} (op : type636 A) (f : type1413 _120521 A) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : ((term684 _120521 A op x s f) = (term681 _120521 A x op s f)) = ((term684 _120521 A op x s f) = (term680 _120521 A x op s f)).
Proof. exact (MK_COMB (@lem5790631 _120521 A op x s f) (@lem5790630 _120521 A op f x s h1)). Qed.
Lemma lem5790635 {_120521 : Type'} (s : _120521 -> Prop) : (term685 _120521 s) = (term685 _120521 s).
Proof. exact (eq_refl (term685 _120521 s)). Qed.
Lemma lem5790636 {_120521 A : Type'} (op : type636 A) (f : type1413 _120521 A) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term686 _120521 A x op s f) = (term687 _120521 A x op s f).
Proof. exact (MK_COMB (@lem5790635 _120521 s) (@lem5790632 _120521 A op f x s h1)). Qed.
Lemma lem5790639 {_120521 A : Type'} (x : _120521) (op : type636 A) (s : _120521 -> Prop) (f : type1413 _120521 A) : term688 _120521 A x op s f.
Proof. exact (fun h0 : (@IN _120521 x s) = False => @lem5790636 _120521 A op f x s h0). Qed.
Lemma lem5790641 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (@IN _120521 x s) = True.
Proof. exact (h1). Qed.
Lemma lem5790642 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem5790643 {_120521 A : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term677 _120521 A x s) = (@COND (A -> Prop) True).
Proof. exact (MK_COMB (@lem5790642 A) (@lem5790641 _120521 x s h1)). Qed.
Lemma lem5790644 {_120521 A : Type'} (op : type636 A) (s : _120521 -> Prop) (f : type1413 _120521 A) : (@iterate (A -> Prop) _120521 op s f) = (@iterate (A -> Prop) _120521 op s f).
Proof. exact (eq_refl (@iterate (A -> Prop) _120521 op s f)). Qed.
Lemma lem5790645 {_120521 A : Type'} (op : type636 A) (f : type1413 _120521 A) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term678 _120521 A x op s f) = (term689 _120521 A op s f).
Proof. exact (MK_COMB (@lem5790643 _120521 A x s h1) (@lem5790644 _120521 A op s f)). Qed.
Lemma lem5790646 {_120521 A : Type'} (x : _120521) (op : type636 A) (s : _120521 -> Prop) (f : type1413 _120521 A) : (term680 _120521 A x op s f) = (term680 _120521 A x op s f).
Proof. exact (eq_refl (term680 _120521 A x op s f)). Qed.
Lemma lem5790647 {_120521 A : Type'} (op : type636 A) (f : type1413 _120521 A) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term681 _120521 A x op s f) = (term690 _120521 A x op s f).
Proof. exact (MK_COMB (@lem5790645 _120521 A op f x s h1) (@lem5790646 _120521 A x op s f)). Qed.
Lemma lem5790649 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5790650 {A : Type'} (t2 : A -> Prop) (t1 : A -> Prop) : (@COND (A -> Prop) True t1 t2) = t1.
Proof. exact (@lem5790649 (A -> Prop) t2 t1). Qed.
Lemma lem5790651 {_120521 A : Type'} (x : _120521) (op : type636 A) (s : _120521 -> Prop) (f : type1413 _120521 A) : (term690 _120521 A x op s f) = (@iterate (A -> Prop) _120521 op s f).
Proof. exact (@lem5790650 A (term680 _120521 A x op s f) (@iterate (A -> Prop) _120521 op s f)). Qed.
Lemma lem5790652 {_120521 A : Type'} (op : type636 A) (f : type1413 _120521 A) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term681 _120521 A x op s f) = (@iterate (A -> Prop) _120521 op s f).
Proof. exact (TRANS (@lem5790647 _120521 A op f x s h1) (@lem5790651 _120521 A x op s f)). Qed.
Lemma lem5790653 {_120521 A : Type'} (op : type636 A) (x : _120521) (s : _120521 -> Prop) (f : type1413 _120521 A) : (term683 _120521 A op x s f) = (term683 _120521 A op x s f).
Proof. exact (eq_refl (term683 _120521 A op x s f)). Qed.
Lemma lem5790654 {_120521 A : Type'} (op : type636 A) (f : type1413 _120521 A) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : ((term684 _120521 A op x s f) = (term681 _120521 A x op s f)) = ((term684 _120521 A op x s f) = (@iterate (A -> Prop) _120521 op s f)).
Proof. exact (MK_COMB (@lem5790653 _120521 A op x s f) (@lem5790652 _120521 A op f x s h1)). Qed.
Lemma lem5790657 {_120521 : Type'} (s : _120521 -> Prop) : (term685 _120521 s) = (term685 _120521 s).
Proof. exact (eq_refl (term685 _120521 s)). Qed.
Lemma lem5790658 {_120521 A : Type'} (op : type636 A) (f : type1413 _120521 A) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term686 _120521 A x op s f) = (term691 _120521 A x op s f).
Proof. exact (MK_COMB (@lem5790657 _120521 s) (@lem5790654 _120521 A op f x s h1)). Qed.
Lemma lem5790661 {_120521 A : Type'} (x : _120521) (op : type636 A) (s : _120521 -> Prop) (f : type1413 _120521 A) : term692 _120521 A x op s f.
Proof. exact (fun h0 : (@IN _120521 x s) = True => @lem5790658 _120521 A op f x s h0). Qed.
Lemma lem5790662 {_120521 A : Type'} (x : _120521) (op : type636 A) (s : _120521 -> Prop) (f : type1413 _120521 A) : term693 _120521 A x op s f.
Proof. exact (conj (@lem5790639 _120521 A x op s f) (@lem5790661 _120521 A x op s f)). Qed.
Lemma lem5790664 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term694 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5790665 {_120521 A : Type'} (x : _120521) (op : type636 A) (s : _120521 -> Prop) (f : type1413 _120521 A) : term695 _120521 A x op s f.
Proof. exact (@lem5790664 (term686 _120521 A x op s f) (term691 _120521 A x op s f) (@IN _120521 x s) (term687 _120521 A x op s f)). Qed.
Lemma lem5790706 {_120521 A : Type'} (x : _120521) (op : type636 A) (s : _120521 -> Prop) (f : type1413 _120521 A) : (term686 _120521 A x op s f) = (term696 _120521 A x op s f).
Proof. exact (@lem5790665 _120521 A x op s f (@lem5790662 _120521 A x op s f)). Qed.
Lemma lem5790707 {_120521 A : Type'} (x : _120521) (op : type636 A) (f : type1413 _120521 A) : (term697 _120521 A x op f) = (term698 _120521 A x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5790706 _120521 A x op s f)). Qed.
Lemma lem5790708 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5790709 {_120521 A : Type'} (x : _120521) (op : type636 A) (f : type1413 _120521 A) : (term699 _120521 A x op f) = (term700 _120521 A x op f).
Proof. exact (MK_COMB (@lem5790708 _120521) (@lem5790707 _120521 A x op f)). Qed.
Lemma lem5790710 {_120521 A : Type'} (op : type636 A) (f : type1413 _120521 A) : (term701 _120521 A op f) = (term702 _120521 A op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5790709 _120521 A x op f)). Qed.
Lemma lem5790711 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5790712 {_120521 A : Type'} (op : type636 A) (f : type1413 _120521 A) : (term703 _120521 A op f) = (term704 _120521 A op f).
Proof. exact (MK_COMB (@lem5790711 _120521) (@lem5790710 _120521 A op f)). Qed.
Lemma lem5790713 {_120521 A : Type'} (op : type636 A) : (term705 _120521 A op) = (term706 _120521 A op).
Proof. exact (fun_ext (fun f : type1413 _120521 A => @lem5790712 _120521 A op f)). Qed.
Lemma lem5790714 {_120521 A : Type'} : (@all (_120521 -> A -> Prop)) = (@all (_120521 -> A -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> A -> Prop))). Qed.
Lemma lem5790715 {_120521 A : Type'} (op : type636 A) : (term707 _120521 A op) = (term708 _120521 A op).
Proof. exact (MK_COMB (@lem5790714 _120521 A) (@lem5790713 _120521 A op)). Qed.
Lemma lem5790716 {_120477 A : Type'} (f : type1413 _120477 A) (op : type636 A) : ((@iterate (A -> Prop) _120477 op (@EMPTY _120477) f) = (@neutral (A -> Prop) op)) = ((@iterate (A -> Prop) _120477 op (@EMPTY _120477) f) = (@neutral (A -> Prop) op)).
Proof. exact (eq_refl ((@iterate (A -> Prop) _120477 op (@EMPTY _120477) f) = (@neutral (A -> Prop) op))). Qed.
Lemma lem5790717 {_120477 A : Type'} (op : type636 A) : (term709 _120477 A op) = (term709 _120477 A op).
Proof. exact (fun_ext (fun f : type1413 _120477 A => @lem5790716 _120477 A f op)). Qed.
Lemma lem5790718 {_120477 A : Type'} : (@all (_120477 -> A -> Prop)) = (@all (_120477 -> A -> Prop)).
Proof. exact (eq_refl (@all (_120477 -> A -> Prop))). Qed.
Lemma lem5790719 {_120477 A : Type'} (op : type636 A) : (term710 _120477 A op) = (term710 _120477 A op).
Proof. exact (MK_COMB (@lem5790718 _120477 A) (@lem5790717 _120477 A op)). Qed.
Lemma lem5790720 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5790721 {_120477 A : Type'} (op : type636 A) : (term711 _120477 A op) = (term711 _120477 A op).
Proof. exact (MK_COMB (@lem5790720) (@lem5790719 _120477 A op)). Qed.
Lemma lem5790722 {_120477 _120521 A : Type'} (op : type636 A) : (term712 _120477 _120521 A op) = (term713 _120477 _120521 A op).
Proof. exact (MK_COMB (@lem5790721 _120477 A op) (@lem5790715 _120521 A op)). Qed.
Lemma lem5790725 {A : Type'} (op : type636 A) : (term714 A op) = (term714 A op).
Proof. exact (eq_refl (term714 A op)). Qed.
Lemma lem5790726 {_120477 _120521 A : Type'} (op : type636 A) : (term715 _120477 _120521 A op) = (term716 _120477 _120521 A op).
Proof. exact (MK_COMB (@lem5790725 A op) (@lem5790722 _120477 _120521 A op)). Qed.
Lemma lem5790727 {_120477 _120521 A : Type'} : (term717 _120477 _120521 A) = (term718 _120477 _120521 A).
Proof. exact (fun_ext (fun op : type636 A => @lem5790726 _120477 _120521 A op)). Qed.
Lemma lem5790728 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem5790729 {_120477 _120521 A : Type'} : (term596 _120477 _120521 A) = (term719 _120477 _120521 A).
Proof. exact (MK_COMB (@lem5790728 A) (@lem5790727 _120477 _120521 A)). Qed.
Lemma lem5790730 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5790731 {_120477 _120521 A : Type'} : (term609 _120477 _120521 A) = (term720 _120477 _120521 A).
Proof. exact (MK_COMB (@lem5790730) (@lem5790729 _120477 _120521 A)). Qed.
Lemma lem5790735 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (@IN _120521 x s) = False.
Proof. exact (h1). Qed.
Lemma lem5790736 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5790737 {_120521 B : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term721 _120521 B x s) = (@COND B False).
Proof. exact (MK_COMB (@lem5790736 B) (@lem5790735 _120521 x s h1)). Qed.
Lemma lem5790738 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (@iterate B _120521 op s f) = (@iterate B _120521 op s f).
Proof. exact (eq_refl (@iterate B _120521 op s f)). Qed.
Lemma lem5790739 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term722 _120521 B x op s f) = (term723 _120521 B op s f).
Proof. exact (MK_COMB (@lem5790737 _120521 B x s h1) (@lem5790738 _120521 B op s f)). Qed.
Lemma lem5790740 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term724 _120521 B x op s f) = (term724 _120521 B x op s f).
Proof. exact (eq_refl (term724 _120521 B x op s f)). Qed.
Lemma lem5790741 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term725 _120521 B x op s f) = (term726 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5790739 _120521 B op f x s h1) (@lem5790740 _120521 B x op s f)). Qed.
Lemma lem5790743 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5790744 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5790743 B t1 t2). Qed.
Lemma lem5790745 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term726 _120521 B x op s f) = (term724 _120521 B x op s f).
Proof. exact (@lem5790744 B (@iterate B _120521 op s f) (term724 _120521 B x op s f)). Qed.
Lemma lem5790746 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term725 _120521 B x op s f) = (term724 _120521 B x op s f).
Proof. exact (TRANS (@lem5790741 _120521 B op f x s h1) (@lem5790745 _120521 B x op s f)). Qed.
Lemma lem5790747 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term727 _120521 B op x s f) = (term727 _120521 B op x s f).
Proof. exact (eq_refl (term727 _120521 B op x s f)). Qed.
Lemma lem5790748 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : ((term728 _120521 B op x s f) = (term725 _120521 B x op s f)) = ((term728 _120521 B op x s f) = (term724 _120521 B x op s f)).
Proof. exact (MK_COMB (@lem5790747 _120521 B op x s f) (@lem5790746 _120521 B op f x s h1)). Qed.
Lemma lem5790751 {_120521 : Type'} (s : _120521 -> Prop) : (term685 _120521 s) = (term685 _120521 s).
Proof. exact (eq_refl (term685 _120521 s)). Qed.
Lemma lem5790752 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term729 _120521 B x op s f) = (term730 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5790751 _120521 s) (@lem5790748 _120521 B op f x s h1)). Qed.
Lemma lem5790755 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term731 _120521 B x op s f.
Proof. exact (fun h0 : (@IN _120521 x s) = False => @lem5790752 _120521 B op f x s h0). Qed.
Lemma lem5790757 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (@IN _120521 x s) = True.
Proof. exact (h1). Qed.
Lemma lem5790758 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5790759 {_120521 B : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term721 _120521 B x s) = (@COND B True).
Proof. exact (MK_COMB (@lem5790758 B) (@lem5790757 _120521 x s h1)). Qed.
Lemma lem5790760 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (@iterate B _120521 op s f) = (@iterate B _120521 op s f).
Proof. exact (eq_refl (@iterate B _120521 op s f)). Qed.
Lemma lem5790761 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term722 _120521 B x op s f) = (term732 _120521 B op s f).
Proof. exact (MK_COMB (@lem5790759 _120521 B x s h1) (@lem5790760 _120521 B op s f)). Qed.
Lemma lem5790762 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term724 _120521 B x op s f) = (term724 _120521 B x op s f).
Proof. exact (eq_refl (term724 _120521 B x op s f)). Qed.
Lemma lem5790763 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term725 _120521 B x op s f) = (term733 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5790761 _120521 B op f x s h1) (@lem5790762 _120521 B x op s f)). Qed.
Lemma lem5790765 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5790766 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5790765 B t2 t1). Qed.
Lemma lem5790767 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term733 _120521 B x op s f) = (@iterate B _120521 op s f).
Proof. exact (@lem5790766 B (term724 _120521 B x op s f) (@iterate B _120521 op s f)). Qed.
Lemma lem5790768 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term725 _120521 B x op s f) = (@iterate B _120521 op s f).
Proof. exact (TRANS (@lem5790763 _120521 B op f x s h1) (@lem5790767 _120521 B x op s f)). Qed.
Lemma lem5790769 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term727 _120521 B op x s f) = (term727 _120521 B op x s f).
Proof. exact (eq_refl (term727 _120521 B op x s f)). Qed.
Lemma lem5790770 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : ((term728 _120521 B op x s f) = (term725 _120521 B x op s f)) = ((term728 _120521 B op x s f) = (@iterate B _120521 op s f)).
Proof. exact (MK_COMB (@lem5790769 _120521 B op x s f) (@lem5790768 _120521 B op f x s h1)). Qed.
Lemma lem5790773 {_120521 : Type'} (s : _120521 -> Prop) : (term685 _120521 s) = (term685 _120521 s).
Proof. exact (eq_refl (term685 _120521 s)). Qed.
Lemma lem5790774 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term729 _120521 B x op s f) = (term734 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5790773 _120521 s) (@lem5790770 _120521 B op f x s h1)). Qed.
Lemma lem5790777 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term735 _120521 B x op s f.
Proof. exact (fun h0 : (@IN _120521 x s) = True => @lem5790774 _120521 B op f x s h0). Qed.
Lemma lem5790778 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term736 _120521 B x op s f.
Proof. exact (conj (@lem5790755 _120521 B x op s f) (@lem5790777 _120521 B x op s f)). Qed.
Lemma lem5790780 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term694 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5790781 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term737 _120521 B x op s f.
Proof. exact (@lem5790780 (term729 _120521 B x op s f) (term734 _120521 B x op s f) (@IN _120521 x s) (term730 _120521 B x op s f)). Qed.
Lemma lem5790822 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term729 _120521 B x op s f) = (term738 _120521 B x op s f).
Proof. exact (@lem5790781 _120521 B x op s f (@lem5790778 _120521 B x op s f)). Qed.
Lemma lem5790823 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term739 _120521 B x op f) = (term740 _120521 B x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5790822 _120521 B x op s f)). Qed.
Lemma lem5790824 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5790825 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term741 _120521 B x op f) = (term742 _120521 B x op f).
Proof. exact (MK_COMB (@lem5790824 _120521) (@lem5790823 _120521 B x op f)). Qed.
Lemma lem5790826 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term743 _120521 B op f) = (term744 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5790825 _120521 B x op f)). Qed.
Lemma lem5790827 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5790828 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term745 _120521 B op f) = (term746 _120521 B op f).
Proof. exact (MK_COMB (@lem5790827 _120521) (@lem5790826 _120521 B op f)). Qed.
Lemma lem5790829 {_120521 B : Type'} (op : type1400 B) : (term747 _120521 B op) = (term748 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5790828 _120521 B op f)). Qed.
Lemma lem5790830 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5790831 {_120521 B : Type'} (op : type1400 B) : (term749 _120521 B op) = (term750 _120521 B op).
Proof. exact (MK_COMB (@lem5790830 _120521 B) (@lem5790829 _120521 B op)). Qed.
Lemma lem5790832 {A B : Type'} (f : A -> B) (op : type1400 B) : ((@iterate B A op (@EMPTY A) f) = (@neutral B op)) = ((@iterate B A op (@EMPTY A) f) = (@neutral B op)).
Proof. exact (eq_refl ((@iterate B A op (@EMPTY A) f) = (@neutral B op))). Qed.
Lemma lem5790833 {A B : Type'} (op : type1400 B) : (term751 A B op) = (term751 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5790832 A B f op)). Qed.
Lemma lem5790834 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5790835 {A B : Type'} (op : type1400 B) : (term752 A B op) = (term752 A B op).
Proof. exact (MK_COMB (@lem5790834 A B) (@lem5790833 A B op)). Qed.
Lemma lem5790836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5790837 {A B : Type'} (op : type1400 B) : (term753 A B op) = (term753 A B op).
Proof. exact (MK_COMB (@lem5790836) (@lem5790835 A B op)). Qed.
Lemma lem5790838 {_120521 A B : Type'} (op : type1400 B) : (term754 _120521 A B op) = (term755 _120521 A B op).
Proof. exact (MK_COMB (@lem5790837 A B op) (@lem5790831 _120521 B op)). Qed.
Lemma lem5790841 {B : Type'} (op : type1400 B) : (term35 B op) = (term35 B op).
Proof. exact (eq_refl (term35 B op)). Qed.
Lemma lem5790842 {_120521 A B : Type'} (op : type1400 B) : (term756 _120521 A B op) = (term757 _120521 A B op).
Proof. exact (MK_COMB (@lem5790841 B op) (@lem5790838 _120521 A B op)). Qed.
Lemma lem5790843 {_120521 A B : Type'} : (term758 _120521 A B) = (term759 _120521 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5790842 _120521 A B op)). Qed.
Lemma lem5790844 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5790845 {_120521 A B : Type'} : (term597 _120521 A B) = (term760 _120521 A B).
Proof. exact (MK_COMB (@lem5790844 B) (@lem5790843 _120521 A B)). Qed.
Lemma lem5790846 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5790847 {_120521 A B : Type'} : (term610 _120521 A B) = (term761 _120521 A B).
Proof. exact (MK_COMB (@lem5790846) (@lem5790845 _120521 A B)). Qed.
Lemma lem5790848 {_120477 _120521 A B : Type'} : (term612 _120477 _120521 A B) = (term762 _120477 _120521 A B).
Proof. exact (MK_COMB (@lem5790847 _120521 A B) (@lem5790731 _120477 _120521 A)). Qed.
Lemma lem5790852 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (@IN A x s) = False.
Proof. exact (h1). Qed.
Lemma lem5790853 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5790854 {A B : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term721 A B x s) = (@COND B False).
Proof. exact (MK_COMB (@lem5790853 B) (@lem5790852 A x s h1)). Qed.
Lemma lem5790855 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (@iterate B A op s f).
Proof. exact (eq_refl (@iterate B A op s f)). Qed.
Lemma lem5790856 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term722 A B x op s f) = (term723 A B op s f).
Proof. exact (MK_COMB (@lem5790854 A B x s h1) (@lem5790855 A B op s f)). Qed.
Lemma lem5790857 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term724 A B x op s f) = (term724 A B x op s f).
Proof. exact (eq_refl (term724 A B x op s f)). Qed.
Lemma lem5790858 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term725 A B x op s f) = (term726 A B x op s f).
Proof. exact (MK_COMB (@lem5790856 A B op f x s h1) (@lem5790857 A B x op s f)). Qed.
Lemma lem5790860 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5790861 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5790860 B t1 t2). Qed.
Lemma lem5790862 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term726 A B x op s f) = (term724 A B x op s f).
Proof. exact (@lem5790861 B (@iterate B A op s f) (term724 A B x op s f)). Qed.
Lemma lem5790863 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term725 A B x op s f) = (term724 A B x op s f).
Proof. exact (TRANS (@lem5790858 A B op f x s h1) (@lem5790862 A B x op s f)). Qed.
Lemma lem5790864 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term727 A B op x s f) = (term727 A B op x s f).
Proof. exact (eq_refl (term727 A B op x s f)). Qed.
Lemma lem5790865 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : ((term728 A B op x s f) = (term725 A B x op s f)) = ((term728 A B op x s f) = (term724 A B x op s f)).
Proof. exact (MK_COMB (@lem5790864 A B op x s f) (@lem5790863 A B op f x s h1)). Qed.
Lemma lem5790868 {A : Type'} (s : A -> Prop) : (term685 A s) = (term685 A s).
Proof. exact (eq_refl (term685 A s)). Qed.
Lemma lem5790869 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term729 A B x op s f) = (term730 A B x op s f).
Proof. exact (MK_COMB (@lem5790868 A s) (@lem5790865 A B op f x s h1)). Qed.
Lemma lem5790872 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term731 A B x op s f.
Proof. exact (fun h0 : (@IN A x s) = False => @lem5790869 A B op f x s h0). Qed.
Lemma lem5790874 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (@IN A x s) = True.
Proof. exact (h1). Qed.
Lemma lem5790875 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5790876 {A B : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term721 A B x s) = (@COND B True).
Proof. exact (MK_COMB (@lem5790875 B) (@lem5790874 A x s h1)). Qed.
Lemma lem5790877 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (@iterate B A op s f).
Proof. exact (eq_refl (@iterate B A op s f)). Qed.
Lemma lem5790878 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term722 A B x op s f) = (term732 A B op s f).
Proof. exact (MK_COMB (@lem5790876 A B x s h1) (@lem5790877 A B op s f)). Qed.
Lemma lem5790879 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term724 A B x op s f) = (term724 A B x op s f).
Proof. exact (eq_refl (term724 A B x op s f)). Qed.
Lemma lem5790880 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term725 A B x op s f) = (term733 A B x op s f).
Proof. exact (MK_COMB (@lem5790878 A B op f x s h1) (@lem5790879 A B x op s f)). Qed.
Lemma lem5790882 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5790883 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5790882 B t2 t1). Qed.
Lemma lem5790884 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term733 A B x op s f) = (@iterate B A op s f).
Proof. exact (@lem5790883 B (term724 A B x op s f) (@iterate B A op s f)). Qed.
Lemma lem5790885 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term725 A B x op s f) = (@iterate B A op s f).
Proof. exact (TRANS (@lem5790880 A B op f x s h1) (@lem5790884 A B x op s f)). Qed.
Lemma lem5790886 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term727 A B op x s f) = (term727 A B op x s f).
Proof. exact (eq_refl (term727 A B op x s f)). Qed.
Lemma lem5790887 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : ((term728 A B op x s f) = (term725 A B x op s f)) = ((term728 A B op x s f) = (@iterate B A op s f)).
Proof. exact (MK_COMB (@lem5790886 A B op x s f) (@lem5790885 A B op f x s h1)). Qed.
Lemma lem5790890 {A : Type'} (s : A -> Prop) : (term685 A s) = (term685 A s).
Proof. exact (eq_refl (term685 A s)). Qed.
Lemma lem5790891 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term729 A B x op s f) = (term734 A B x op s f).
Proof. exact (MK_COMB (@lem5790890 A s) (@lem5790887 A B op f x s h1)). Qed.
Lemma lem5790894 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term735 A B x op s f.
Proof. exact (fun h0 : (@IN A x s) = True => @lem5790891 A B op f x s h0). Qed.
Lemma lem5790895 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term736 A B x op s f.
Proof. exact (conj (@lem5790872 A B x op s f) (@lem5790894 A B x op s f)). Qed.
Lemma lem5790897 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term694 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5790898 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term737 A B x op s f.
Proof. exact (@lem5790897 (term729 A B x op s f) (term734 A B x op s f) (@IN A x s) (term730 A B x op s f)). Qed.
Lemma lem5790939 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term729 A B x op s f) = (term738 A B x op s f).
Proof. exact (@lem5790898 A B x op s f (@lem5790895 A B x op s f)). Qed.
Lemma lem5790940 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term739 A B x op f) = (term740 A B x op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5790939 A B x op s f)). Qed.
Lemma lem5790941 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5790942 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term741 A B x op f) = (term742 A B x op f).
Proof. exact (MK_COMB (@lem5790941 A) (@lem5790940 A B x op f)). Qed.
Lemma lem5790943 {A B : Type'} (op : type1400 B) (f : A -> B) : (term743 A B op f) = (term744 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5790942 A B x op f)). Qed.
Lemma lem5790944 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5790945 {A B : Type'} (op : type1400 B) (f : A -> B) : (term745 A B op f) = (term746 A B op f).
Proof. exact (MK_COMB (@lem5790944 A) (@lem5790943 A B op f)). Qed.
Lemma lem5790946 {A B : Type'} (op : type1400 B) : (term747 A B op) = (term748 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5790945 A B op f)). Qed.
Lemma lem5790947 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5790948 {A B : Type'} (op : type1400 B) : (term749 A B op) = (term750 A B op).
Proof. exact (MK_COMB (@lem5790947 A B) (@lem5790946 A B op)). Qed.
Lemma lem5790949 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op)) = ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op)).
Proof. exact (eq_refl ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op))). Qed.
Lemma lem5790950 {_120477 B : Type'} (op : type1400 B) : (term751 _120477 B op) = (term751 _120477 B op).
Proof. exact (fun_ext (fun f : _120477 -> B => @lem5790949 _120477 B f op)). Qed.
Lemma lem5790951 {_120477 B : Type'} : (@all (_120477 -> B)) = (@all (_120477 -> B)).
Proof. exact (eq_refl (@all (_120477 -> B))). Qed.
Lemma lem5790952 {_120477 B : Type'} (op : type1400 B) : (term752 _120477 B op) = (term752 _120477 B op).
Proof. exact (MK_COMB (@lem5790951 _120477 B) (@lem5790950 _120477 B op)). Qed.
Lemma lem5790953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5790954 {_120477 B : Type'} (op : type1400 B) : (term753 _120477 B op) = (term753 _120477 B op).
Proof. exact (MK_COMB (@lem5790953) (@lem5790952 _120477 B op)). Qed.
Lemma lem5790955 {_120477 A B : Type'} (op : type1400 B) : (term763 _120477 A B op) = (term764 _120477 A B op).
Proof. exact (MK_COMB (@lem5790954 _120477 B op) (@lem5790948 A B op)). Qed.
Lemma lem5790958 {B : Type'} (op : type1400 B) : (term35 B op) = (term35 B op).
Proof. exact (eq_refl (term35 B op)). Qed.
Lemma lem5790959 {_120477 A B : Type'} (op : type1400 B) : (term765 _120477 A B op) = (term766 _120477 A B op).
Proof. exact (MK_COMB (@lem5790958 B op) (@lem5790955 _120477 A B op)). Qed.
Lemma lem5790960 {_120477 A B : Type'} : (term767 _120477 A B) = (term768 _120477 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5790959 _120477 A B op)). Qed.
Lemma lem5790961 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5790962 {_120477 A B : Type'} : (term595 _120477 A B) = (term769 _120477 A B).
Proof. exact (MK_COMB (@lem5790961 B) (@lem5790960 _120477 A B)). Qed.
Lemma lem5790963 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5790964 {_120477 A B : Type'} : (term613 _120477 A B) = (term770 _120477 A B).
Proof. exact (MK_COMB (@lem5790963) (@lem5790962 _120477 A B)). Qed.
Lemma lem5790965 {_120477 _120521 A B : Type'} : (term615 _120477 _120521 A B) = (term771 _120477 _120521 A B).
Proof. exact (MK_COMB (@lem5790964 _120477 A B) (@lem5790848 _120477 _120521 A B)). Qed.
Lemma lem5790969 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (@IN _120521 x s) = False.
Proof. exact (h1). Qed.
Lemma lem5790970 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5790971 {_120521 B : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term721 _120521 B x s) = (@COND B False).
Proof. exact (MK_COMB (@lem5790970 B) (@lem5790969 _120521 x s h1)). Qed.
Lemma lem5790972 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (@iterate B _120521 op s f) = (@iterate B _120521 op s f).
Proof. exact (eq_refl (@iterate B _120521 op s f)). Qed.
Lemma lem5790973 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term722 _120521 B x op s f) = (term723 _120521 B op s f).
Proof. exact (MK_COMB (@lem5790971 _120521 B x s h1) (@lem5790972 _120521 B op s f)). Qed.
Lemma lem5790974 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term724 _120521 B x op s f) = (term724 _120521 B x op s f).
Proof. exact (eq_refl (term724 _120521 B x op s f)). Qed.
Lemma lem5790975 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term725 _120521 B x op s f) = (term726 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5790973 _120521 B op f x s h1) (@lem5790974 _120521 B x op s f)). Qed.
Lemma lem5790977 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5790978 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5790977 B t1 t2). Qed.
Lemma lem5790979 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term726 _120521 B x op s f) = (term724 _120521 B x op s f).
Proof. exact (@lem5790978 B (@iterate B _120521 op s f) (term724 _120521 B x op s f)). Qed.
Lemma lem5790980 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term725 _120521 B x op s f) = (term724 _120521 B x op s f).
Proof. exact (TRANS (@lem5790975 _120521 B op f x s h1) (@lem5790979 _120521 B x op s f)). Qed.
Lemma lem5790981 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term727 _120521 B op x s f) = (term727 _120521 B op x s f).
Proof. exact (eq_refl (term727 _120521 B op x s f)). Qed.
Lemma lem5790982 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : ((term728 _120521 B op x s f) = (term725 _120521 B x op s f)) = ((term728 _120521 B op x s f) = (term724 _120521 B x op s f)).
Proof. exact (MK_COMB (@lem5790981 _120521 B op x s f) (@lem5790980 _120521 B op f x s h1)). Qed.
Lemma lem5790985 {_120521 : Type'} (s : _120521 -> Prop) : (term685 _120521 s) = (term685 _120521 s).
Proof. exact (eq_refl (term685 _120521 s)). Qed.
Lemma lem5790986 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term729 _120521 B x op s f) = (term730 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5790985 _120521 s) (@lem5790982 _120521 B op f x s h1)). Qed.
Lemma lem5790989 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term731 _120521 B x op s f.
Proof. exact (fun h0 : (@IN _120521 x s) = False => @lem5790986 _120521 B op f x s h0). Qed.
Lemma lem5790991 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (@IN _120521 x s) = True.
Proof. exact (h1). Qed.
Lemma lem5790992 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5790993 {_120521 B : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term721 _120521 B x s) = (@COND B True).
Proof. exact (MK_COMB (@lem5790992 B) (@lem5790991 _120521 x s h1)). Qed.
Lemma lem5790994 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (@iterate B _120521 op s f) = (@iterate B _120521 op s f).
Proof. exact (eq_refl (@iterate B _120521 op s f)). Qed.
Lemma lem5790995 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term722 _120521 B x op s f) = (term732 _120521 B op s f).
Proof. exact (MK_COMB (@lem5790993 _120521 B x s h1) (@lem5790994 _120521 B op s f)). Qed.
Lemma lem5790996 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term724 _120521 B x op s f) = (term724 _120521 B x op s f).
Proof. exact (eq_refl (term724 _120521 B x op s f)). Qed.
Lemma lem5790997 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term725 _120521 B x op s f) = (term733 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5790995 _120521 B op f x s h1) (@lem5790996 _120521 B x op s f)). Qed.
Lemma lem5790999 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5791000 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5790999 B t2 t1). Qed.
Lemma lem5791001 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term733 _120521 B x op s f) = (@iterate B _120521 op s f).
Proof. exact (@lem5791000 B (term724 _120521 B x op s f) (@iterate B _120521 op s f)). Qed.
Lemma lem5791002 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term725 _120521 B x op s f) = (@iterate B _120521 op s f).
Proof. exact (TRANS (@lem5790997 _120521 B op f x s h1) (@lem5791001 _120521 B x op s f)). Qed.
Lemma lem5791003 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term727 _120521 B op x s f) = (term727 _120521 B op x s f).
Proof. exact (eq_refl (term727 _120521 B op x s f)). Qed.
Lemma lem5791004 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : ((term728 _120521 B op x s f) = (term725 _120521 B x op s f)) = ((term728 _120521 B op x s f) = (@iterate B _120521 op s f)).
Proof. exact (MK_COMB (@lem5791003 _120521 B op x s f) (@lem5791002 _120521 B op f x s h1)). Qed.
Lemma lem5791007 {_120521 : Type'} (s : _120521 -> Prop) : (term685 _120521 s) = (term685 _120521 s).
Proof. exact (eq_refl (term685 _120521 s)). Qed.
Lemma lem5791008 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term729 _120521 B x op s f) = (term734 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5791007 _120521 s) (@lem5791004 _120521 B op f x s h1)). Qed.
Lemma lem5791011 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term735 _120521 B x op s f.
Proof. exact (fun h0 : (@IN _120521 x s) = True => @lem5791008 _120521 B op f x s h0). Qed.
Lemma lem5791012 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term736 _120521 B x op s f.
Proof. exact (conj (@lem5790989 _120521 B x op s f) (@lem5791011 _120521 B x op s f)). Qed.
Lemma lem5791014 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term694 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5791015 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term737 _120521 B x op s f.
Proof. exact (@lem5791014 (term729 _120521 B x op s f) (term734 _120521 B x op s f) (@IN _120521 x s) (term730 _120521 B x op s f)). Qed.
Lemma lem5791056 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term729 _120521 B x op s f) = (term738 _120521 B x op s f).
Proof. exact (@lem5791015 _120521 B x op s f (@lem5791012 _120521 B x op s f)). Qed.
Lemma lem5791057 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term739 _120521 B x op f) = (term740 _120521 B x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5791056 _120521 B x op s f)). Qed.
Lemma lem5791058 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5791059 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term741 _120521 B x op f) = (term742 _120521 B x op f).
Proof. exact (MK_COMB (@lem5791058 _120521) (@lem5791057 _120521 B x op f)). Qed.
Lemma lem5791060 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term743 _120521 B op f) = (term744 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5791059 _120521 B x op f)). Qed.
Lemma lem5791061 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5791062 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term745 _120521 B op f) = (term746 _120521 B op f).
Proof. exact (MK_COMB (@lem5791061 _120521) (@lem5791060 _120521 B op f)). Qed.
Lemma lem5791063 {_120521 B : Type'} (op : type1400 B) : (term747 _120521 B op) = (term748 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5791062 _120521 B op f)). Qed.
Lemma lem5791064 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5791065 {_120521 B : Type'} (op : type1400 B) : (term749 _120521 B op) = (term750 _120521 B op).
Proof. exact (MK_COMB (@lem5791064 _120521 B) (@lem5791063 _120521 B op)). Qed.
Lemma lem5791066 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op)) = ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op)).
Proof. exact (eq_refl ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op))). Qed.
Lemma lem5791067 {_120477 B : Type'} (op : type1400 B) : (term751 _120477 B op) = (term751 _120477 B op).
Proof. exact (fun_ext (fun f : _120477 -> B => @lem5791066 _120477 B f op)). Qed.
Lemma lem5791068 {_120477 B : Type'} : (@all (_120477 -> B)) = (@all (_120477 -> B)).
Proof. exact (eq_refl (@all (_120477 -> B))). Qed.
Lemma lem5791069 {_120477 B : Type'} (op : type1400 B) : (term752 _120477 B op) = (term752 _120477 B op).
Proof. exact (MK_COMB (@lem5791068 _120477 B) (@lem5791067 _120477 B op)). Qed.
Lemma lem5791070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5791071 {_120477 B : Type'} (op : type1400 B) : (term753 _120477 B op) = (term753 _120477 B op).
Proof. exact (MK_COMB (@lem5791070) (@lem5791069 _120477 B op)). Qed.
Lemma lem5791072 {_120477 _120521 B : Type'} (op : type1400 B) : (term763 _120477 _120521 B op) = (term764 _120477 _120521 B op).
Proof. exact (MK_COMB (@lem5791071 _120477 B op) (@lem5791065 _120521 B op)). Qed.
Lemma lem5791075 {B : Type'} (op : type1400 B) : (term35 B op) = (term35 B op).
Proof. exact (eq_refl (term35 B op)). Qed.
Lemma lem5791076 {_120477 _120521 B : Type'} (op : type1400 B) : (term765 _120477 _120521 B op) = (term766 _120477 _120521 B op).
Proof. exact (MK_COMB (@lem5791075 B op) (@lem5791072 _120477 _120521 B op)). Qed.
Lemma lem5791077 {_120477 _120521 B : Type'} : (term767 _120477 _120521 B) = (term768 _120477 _120521 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5791076 _120477 _120521 B op)). Qed.
Lemma lem5791078 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5791079 {_120477 _120521 B : Type'} : (term595 _120477 _120521 B) = (term769 _120477 _120521 B).
Proof. exact (MK_COMB (@lem5791078 B) (@lem5791077 _120477 _120521 B)). Qed.
Lemma lem5791080 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791081 {_120477 _120521 B : Type'} : (term613 _120477 _120521 B) = (term770 _120477 _120521 B).
Proof. exact (MK_COMB (@lem5791080) (@lem5791079 _120477 _120521 B)). Qed.
Lemma lem5791082 {_120477 _120521 A B : Type'} : (term617 _120477 _120521 A B) = (term772 _120477 _120521 A B).
Proof. exact (MK_COMB (@lem5791081 _120477 _120521 B) (@lem5790965 _120477 _120521 A B)). Qed.
Lemma lem5791086 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (@IN _120521 x s) = False.
Proof. exact (h1). Qed.
Lemma lem5791087 {_120519 : Type'} : (@COND _120519) = (@COND _120519).
Proof. exact (eq_refl (@COND _120519)). Qed.
Lemma lem5791088 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term773 _120519 _120521 x s) = (@COND _120519 False).
Proof. exact (MK_COMB (@lem5791087 _120519) (@lem5791086 _120521 x s h1)). Qed.
Lemma lem5791089 {_120519 _120521 : Type'} (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (@iterate _120519 _120521 op s f) = (@iterate _120519 _120521 op s f).
Proof. exact (eq_refl (@iterate _120519 _120521 op s f)). Qed.
Lemma lem5791090 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term774 _120519 _120521 x op s f) = (term775 _120519 _120521 op s f).
Proof. exact (MK_COMB (@lem5791088 _120519 _120521 x s h1) (@lem5791089 _120519 _120521 op s f)). Qed.
Lemma lem5791091 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term776 _120519 _120521 x op s f) = (term776 _120519 _120521 x op s f).
Proof. exact (eq_refl (term776 _120519 _120521 x op s f)). Qed.
Lemma lem5791092 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term777 _120519 _120521 x op s f) = (term778 _120519 _120521 x op s f).
Proof. exact (MK_COMB (@lem5791090 _120519 _120521 op f x s h1) (@lem5791091 _120519 _120521 x op s f)). Qed.
Lemma lem5791094 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5791095 {_120519 : Type'} (t1 : _120519) (t2 : _120519) : (@COND _120519 False t1 t2) = t2.
Proof. exact (@lem5791094 _120519 t1 t2). Qed.
Lemma lem5791096 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term778 _120519 _120521 x op s f) = (term776 _120519 _120521 x op s f).
Proof. exact (@lem5791095 _120519 (@iterate _120519 _120521 op s f) (term776 _120519 _120521 x op s f)). Qed.
Lemma lem5791097 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term777 _120519 _120521 x op s f) = (term776 _120519 _120521 x op s f).
Proof. exact (TRANS (@lem5791092 _120519 _120521 op f x s h1) (@lem5791096 _120519 _120521 x op s f)). Qed.
Lemma lem5791098 {_120519 _120521 : Type'} (op : type1400 _120519) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term779 _120519 _120521 op x s f) = (term779 _120519 _120521 op x s f).
Proof. exact (eq_refl (term779 _120519 _120521 op x s f)). Qed.
Lemma lem5791099 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : ((term780 _120519 _120521 op x s f) = (term777 _120519 _120521 x op s f)) = ((term780 _120519 _120521 op x s f) = (term776 _120519 _120521 x op s f)).
Proof. exact (MK_COMB (@lem5791098 _120519 _120521 op x s f) (@lem5791097 _120519 _120521 op f x s h1)). Qed.
Lemma lem5791102 {_120521 : Type'} (s : _120521 -> Prop) : (term685 _120521 s) = (term685 _120521 s).
Proof. exact (eq_refl (term685 _120521 s)). Qed.
Lemma lem5791103 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term781 _120519 _120521 x op s f) = (term782 _120519 _120521 x op s f).
Proof. exact (MK_COMB (@lem5791102 _120521 s) (@lem5791099 _120519 _120521 op f x s h1)). Qed.
Lemma lem5791106 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term783 _120519 _120521 x op s f.
Proof. exact (fun h0 : (@IN _120521 x s) = False => @lem5791103 _120519 _120521 op f x s h0). Qed.
Lemma lem5791108 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (@IN _120521 x s) = True.
Proof. exact (h1). Qed.
Lemma lem5791109 {_120519 : Type'} : (@COND _120519) = (@COND _120519).
Proof. exact (eq_refl (@COND _120519)). Qed.
Lemma lem5791110 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term773 _120519 _120521 x s) = (@COND _120519 True).
Proof. exact (MK_COMB (@lem5791109 _120519) (@lem5791108 _120521 x s h1)). Qed.
Lemma lem5791111 {_120519 _120521 : Type'} (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (@iterate _120519 _120521 op s f) = (@iterate _120519 _120521 op s f).
Proof. exact (eq_refl (@iterate _120519 _120521 op s f)). Qed.
Lemma lem5791112 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term774 _120519 _120521 x op s f) = (term784 _120519 _120521 op s f).
Proof. exact (MK_COMB (@lem5791110 _120519 _120521 x s h1) (@lem5791111 _120519 _120521 op s f)). Qed.
Lemma lem5791113 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term776 _120519 _120521 x op s f) = (term776 _120519 _120521 x op s f).
Proof. exact (eq_refl (term776 _120519 _120521 x op s f)). Qed.
Lemma lem5791114 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term777 _120519 _120521 x op s f) = (term785 _120519 _120521 x op s f).
Proof. exact (MK_COMB (@lem5791112 _120519 _120521 op f x s h1) (@lem5791113 _120519 _120521 x op s f)). Qed.
Lemma lem5791116 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5791117 {_120519 : Type'} (t2 : _120519) (t1 : _120519) : (@COND _120519 True t1 t2) = t1.
Proof. exact (@lem5791116 _120519 t2 t1). Qed.
Lemma lem5791118 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term785 _120519 _120521 x op s f) = (@iterate _120519 _120521 op s f).
Proof. exact (@lem5791117 _120519 (term776 _120519 _120521 x op s f) (@iterate _120519 _120521 op s f)). Qed.
Lemma lem5791119 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term777 _120519 _120521 x op s f) = (@iterate _120519 _120521 op s f).
Proof. exact (TRANS (@lem5791114 _120519 _120521 op f x s h1) (@lem5791118 _120519 _120521 x op s f)). Qed.
Lemma lem5791120 {_120519 _120521 : Type'} (op : type1400 _120519) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term779 _120519 _120521 op x s f) = (term779 _120519 _120521 op x s f).
Proof. exact (eq_refl (term779 _120519 _120521 op x s f)). Qed.
Lemma lem5791121 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : ((term780 _120519 _120521 op x s f) = (term777 _120519 _120521 x op s f)) = ((term780 _120519 _120521 op x s f) = (@iterate _120519 _120521 op s f)).
Proof. exact (MK_COMB (@lem5791120 _120519 _120521 op x s f) (@lem5791119 _120519 _120521 op f x s h1)). Qed.
Lemma lem5791124 {_120521 : Type'} (s : _120521 -> Prop) : (term685 _120521 s) = (term685 _120521 s).
Proof. exact (eq_refl (term685 _120521 s)). Qed.
Lemma lem5791125 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term781 _120519 _120521 x op s f) = (term786 _120519 _120521 x op s f).
Proof. exact (MK_COMB (@lem5791124 _120521 s) (@lem5791121 _120519 _120521 op f x s h1)). Qed.
Lemma lem5791128 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term787 _120519 _120521 x op s f.
Proof. exact (fun h0 : (@IN _120521 x s) = True => @lem5791125 _120519 _120521 op f x s h0). Qed.
Lemma lem5791129 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term788 _120519 _120521 x op s f.
Proof. exact (conj (@lem5791106 _120519 _120521 x op s f) (@lem5791128 _120519 _120521 x op s f)). Qed.
Lemma lem5791131 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term694 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5791132 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term789 _120519 _120521 x op s f.
Proof. exact (@lem5791131 (term781 _120519 _120521 x op s f) (term786 _120519 _120521 x op s f) (@IN _120521 x s) (term782 _120519 _120521 x op s f)). Qed.
Lemma lem5791173 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term781 _120519 _120521 x op s f) = (term790 _120519 _120521 x op s f).
Proof. exact (@lem5791132 _120519 _120521 x op s f (@lem5791129 _120519 _120521 x op s f)). Qed.
Lemma lem5791174 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term791 _120519 _120521 x op f) = (term792 _120519 _120521 x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5791173 _120519 _120521 x op s f)). Qed.
Lemma lem5791175 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5791176 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term793 _120519 _120521 x op f) = (term794 _120519 _120521 x op f).
Proof. exact (MK_COMB (@lem5791175 _120521) (@lem5791174 _120519 _120521 x op f)). Qed.
Lemma lem5791177 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term795 _120519 _120521 op f) = (term796 _120519 _120521 op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5791176 _120519 _120521 x op f)). Qed.
Lemma lem5791178 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5791179 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term797 _120519 _120521 op f) = (term798 _120519 _120521 op f).
Proof. exact (MK_COMB (@lem5791178 _120521) (@lem5791177 _120519 _120521 op f)). Qed.
Lemma lem5791180 {_120519 _120521 : Type'} (op : type1400 _120519) : (term799 _120519 _120521 op) = (term800 _120519 _120521 op).
Proof. exact (fun_ext (fun f : _120521 -> _120519 => @lem5791179 _120519 _120521 op f)). Qed.
Lemma lem5791181 {_120519 _120521 : Type'} : (@all (_120521 -> _120519)) = (@all (_120521 -> _120519)).
Proof. exact (eq_refl (@all (_120521 -> _120519))). Qed.
Lemma lem5791182 {_120519 _120521 : Type'} (op : type1400 _120519) : (term801 _120519 _120521 op) = (term802 _120519 _120521 op).
Proof. exact (MK_COMB (@lem5791181 _120519 _120521) (@lem5791180 _120519 _120521 op)). Qed.
Lemma lem5791183 {_120519 A : Type'} (f : A -> _120519) (op : type1400 _120519) : ((@iterate _120519 A op (@EMPTY A) f) = (@neutral _120519 op)) = ((@iterate _120519 A op (@EMPTY A) f) = (@neutral _120519 op)).
Proof. exact (eq_refl ((@iterate _120519 A op (@EMPTY A) f) = (@neutral _120519 op))). Qed.
Lemma lem5791184 {_120519 A : Type'} (op : type1400 _120519) : (term803 _120519 A op) = (term803 _120519 A op).
Proof. exact (fun_ext (fun f : A -> _120519 => @lem5791183 _120519 A f op)). Qed.
Lemma lem5791185 {_120519 A : Type'} : (@all (A -> _120519)) = (@all (A -> _120519)).
Proof. exact (eq_refl (@all (A -> _120519))). Qed.
Lemma lem5791186 {_120519 A : Type'} (op : type1400 _120519) : (term804 _120519 A op) = (term804 _120519 A op).
Proof. exact (MK_COMB (@lem5791185 _120519 A) (@lem5791184 _120519 A op)). Qed.
Lemma lem5791187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5791188 {_120519 A : Type'} (op : type1400 _120519) : (term805 _120519 A op) = (term805 _120519 A op).
Proof. exact (MK_COMB (@lem5791187) (@lem5791186 _120519 A op)). Qed.
Lemma lem5791189 {_120519 _120521 A : Type'} (op : type1400 _120519) : (term806 _120519 _120521 A op) = (term807 _120519 _120521 A op).
Proof. exact (MK_COMB (@lem5791188 _120519 A op) (@lem5791182 _120519 _120521 op)). Qed.
Lemma lem5791192 {_120519 : Type'} (op : type1400 _120519) : (term35 _120519 op) = (term35 _120519 op).
Proof. exact (eq_refl (term35 _120519 op)). Qed.
Lemma lem5791193 {_120519 _120521 A : Type'} (op : type1400 _120519) : (term808 _120519 _120521 A op) = (term809 _120519 _120521 A op).
Proof. exact (MK_COMB (@lem5791192 _120519 op) (@lem5791189 _120519 _120521 A op)). Qed.
Lemma lem5791194 {_120519 _120521 A : Type'} : (term810 _120519 _120521 A) = (term811 _120519 _120521 A).
Proof. exact (fun_ext (fun op : type1400 _120519 => @lem5791193 _120519 _120521 A op)). Qed.
Lemma lem5791195 {_120519 : Type'} : (@all (_120519 -> _120519 -> _120519)) = (@all (_120519 -> _120519 -> _120519)).
Proof. exact (eq_refl (@all (_120519 -> _120519 -> _120519))). Qed.
Lemma lem5791196 {_120519 _120521 A : Type'} : (term598 _120519 _120521 A) = (term812 _120519 _120521 A).
Proof. exact (MK_COMB (@lem5791195 _120519) (@lem5791194 _120519 _120521 A)). Qed.
Lemma lem5791197 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791198 {_120519 _120521 A : Type'} : (term618 _120519 _120521 A) = (term813 _120519 _120521 A).
Proof. exact (MK_COMB (@lem5791197) (@lem5791196 _120519 _120521 A)). Qed.
Lemma lem5791199 {_120477 _120519 _120521 A B : Type'} : (term620 _120477 _120519 _120521 A B) = (term814 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791198 _120519 _120521 A) (@lem5791082 _120477 _120521 A B)). Qed.
Lemma lem5791203 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (@IN A x s) = False.
Proof. exact (h1). Qed.
Lemma lem5791204 {_120519 : Type'} : (@COND _120519) = (@COND _120519).
Proof. exact (eq_refl (@COND _120519)). Qed.
Lemma lem5791205 {_120519 A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term773 _120519 A x s) = (@COND _120519 False).
Proof. exact (MK_COMB (@lem5791204 _120519) (@lem5791203 A x s h1)). Qed.
Lemma lem5791206 {_120519 A : Type'} (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : (@iterate _120519 A op s f) = (@iterate _120519 A op s f).
Proof. exact (eq_refl (@iterate _120519 A op s f)). Qed.
Lemma lem5791207 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term774 _120519 A x op s f) = (term775 _120519 A op s f).
Proof. exact (MK_COMB (@lem5791205 _120519 A x s h1) (@lem5791206 _120519 A op s f)). Qed.
Lemma lem5791208 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : (term776 _120519 A x op s f) = (term776 _120519 A x op s f).
Proof. exact (eq_refl (term776 _120519 A x op s f)). Qed.
Lemma lem5791209 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term777 _120519 A x op s f) = (term778 _120519 A x op s f).
Proof. exact (MK_COMB (@lem5791207 _120519 A op f x s h1) (@lem5791208 _120519 A x op s f)). Qed.
Lemma lem5791211 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5791212 {_120519 : Type'} (t1 : _120519) (t2 : _120519) : (@COND _120519 False t1 t2) = t2.
Proof. exact (@lem5791211 _120519 t1 t2). Qed.
Lemma lem5791213 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : (term778 _120519 A x op s f) = (term776 _120519 A x op s f).
Proof. exact (@lem5791212 _120519 (@iterate _120519 A op s f) (term776 _120519 A x op s f)). Qed.
Lemma lem5791214 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term777 _120519 A x op s f) = (term776 _120519 A x op s f).
Proof. exact (TRANS (@lem5791209 _120519 A op f x s h1) (@lem5791213 _120519 A x op s f)). Qed.
Lemma lem5791215 {_120519 A : Type'} (op : type1400 _120519) (x : A) (s : A -> Prop) (f : A -> _120519) : (term779 _120519 A op x s f) = (term779 _120519 A op x s f).
Proof. exact (eq_refl (term779 _120519 A op x s f)). Qed.
Lemma lem5791216 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : ((term780 _120519 A op x s f) = (term777 _120519 A x op s f)) = ((term780 _120519 A op x s f) = (term776 _120519 A x op s f)).
Proof. exact (MK_COMB (@lem5791215 _120519 A op x s f) (@lem5791214 _120519 A op f x s h1)). Qed.
Lemma lem5791219 {A : Type'} (s : A -> Prop) : (term685 A s) = (term685 A s).
Proof. exact (eq_refl (term685 A s)). Qed.
Lemma lem5791220 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term781 _120519 A x op s f) = (term782 _120519 A x op s f).
Proof. exact (MK_COMB (@lem5791219 A s) (@lem5791216 _120519 A op f x s h1)). Qed.
Lemma lem5791223 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : term783 _120519 A x op s f.
Proof. exact (fun h0 : (@IN A x s) = False => @lem5791220 _120519 A op f x s h0). Qed.
Lemma lem5791225 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (@IN A x s) = True.
Proof. exact (h1). Qed.
Lemma lem5791226 {_120519 : Type'} : (@COND _120519) = (@COND _120519).
Proof. exact (eq_refl (@COND _120519)). Qed.
Lemma lem5791227 {_120519 A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term773 _120519 A x s) = (@COND _120519 True).
Proof. exact (MK_COMB (@lem5791226 _120519) (@lem5791225 A x s h1)). Qed.
Lemma lem5791228 {_120519 A : Type'} (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : (@iterate _120519 A op s f) = (@iterate _120519 A op s f).
Proof. exact (eq_refl (@iterate _120519 A op s f)). Qed.
Lemma lem5791229 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term774 _120519 A x op s f) = (term784 _120519 A op s f).
Proof. exact (MK_COMB (@lem5791227 _120519 A x s h1) (@lem5791228 _120519 A op s f)). Qed.
Lemma lem5791230 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : (term776 _120519 A x op s f) = (term776 _120519 A x op s f).
Proof. exact (eq_refl (term776 _120519 A x op s f)). Qed.
Lemma lem5791231 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term777 _120519 A x op s f) = (term785 _120519 A x op s f).
Proof. exact (MK_COMB (@lem5791229 _120519 A op f x s h1) (@lem5791230 _120519 A x op s f)). Qed.
Lemma lem5791233 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5791234 {_120519 : Type'} (t2 : _120519) (t1 : _120519) : (@COND _120519 True t1 t2) = t1.
Proof. exact (@lem5791233 _120519 t2 t1). Qed.
Lemma lem5791235 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : (term785 _120519 A x op s f) = (@iterate _120519 A op s f).
Proof. exact (@lem5791234 _120519 (term776 _120519 A x op s f) (@iterate _120519 A op s f)). Qed.
Lemma lem5791236 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term777 _120519 A x op s f) = (@iterate _120519 A op s f).
Proof. exact (TRANS (@lem5791231 _120519 A op f x s h1) (@lem5791235 _120519 A x op s f)). Qed.
Lemma lem5791237 {_120519 A : Type'} (op : type1400 _120519) (x : A) (s : A -> Prop) (f : A -> _120519) : (term779 _120519 A op x s f) = (term779 _120519 A op x s f).
Proof. exact (eq_refl (term779 _120519 A op x s f)). Qed.
Lemma lem5791238 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : ((term780 _120519 A op x s f) = (term777 _120519 A x op s f)) = ((term780 _120519 A op x s f) = (@iterate _120519 A op s f)).
Proof. exact (MK_COMB (@lem5791237 _120519 A op x s f) (@lem5791236 _120519 A op f x s h1)). Qed.
Lemma lem5791241 {A : Type'} (s : A -> Prop) : (term685 A s) = (term685 A s).
Proof. exact (eq_refl (term685 A s)). Qed.
Lemma lem5791242 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term781 _120519 A x op s f) = (term786 _120519 A x op s f).
Proof. exact (MK_COMB (@lem5791241 A s) (@lem5791238 _120519 A op f x s h1)). Qed.
Lemma lem5791245 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : term787 _120519 A x op s f.
Proof. exact (fun h0 : (@IN A x s) = True => @lem5791242 _120519 A op f x s h0). Qed.
Lemma lem5791246 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : term788 _120519 A x op s f.
Proof. exact (conj (@lem5791223 _120519 A x op s f) (@lem5791245 _120519 A x op s f)). Qed.
Lemma lem5791248 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term694 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5791249 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : term789 _120519 A x op s f.
Proof. exact (@lem5791248 (term781 _120519 A x op s f) (term786 _120519 A x op s f) (@IN A x s) (term782 _120519 A x op s f)). Qed.
Lemma lem5791290 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : (term781 _120519 A x op s f) = (term790 _120519 A x op s f).
Proof. exact (@lem5791249 _120519 A x op s f (@lem5791246 _120519 A x op s f)). Qed.
Lemma lem5791291 {_120519 A : Type'} (x : A) (op : type1400 _120519) (f : A -> _120519) : (term791 _120519 A x op f) = (term792 _120519 A x op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5791290 _120519 A x op s f)). Qed.
Lemma lem5791292 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5791293 {_120519 A : Type'} (x : A) (op : type1400 _120519) (f : A -> _120519) : (term793 _120519 A x op f) = (term794 _120519 A x op f).
Proof. exact (MK_COMB (@lem5791292 A) (@lem5791291 _120519 A x op f)). Qed.
Lemma lem5791294 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) : (term795 _120519 A op f) = (term796 _120519 A op f).
Proof. exact (fun_ext (fun x : A => @lem5791293 _120519 A x op f)). Qed.
Lemma lem5791295 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5791296 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) : (term797 _120519 A op f) = (term798 _120519 A op f).
Proof. exact (MK_COMB (@lem5791295 A) (@lem5791294 _120519 A op f)). Qed.
Lemma lem5791297 {_120519 A : Type'} (op : type1400 _120519) : (term799 _120519 A op) = (term800 _120519 A op).
Proof. exact (fun_ext (fun f : A -> _120519 => @lem5791296 _120519 A op f)). Qed.
Lemma lem5791298 {_120519 A : Type'} : (@all (A -> _120519)) = (@all (A -> _120519)).
Proof. exact (eq_refl (@all (A -> _120519))). Qed.
Lemma lem5791299 {_120519 A : Type'} (op : type1400 _120519) : (term801 _120519 A op) = (term802 _120519 A op).
Proof. exact (MK_COMB (@lem5791298 _120519 A) (@lem5791297 _120519 A op)). Qed.
Lemma lem5791300 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op))). Qed.
Lemma lem5791301 {_120477 _120519 : Type'} (op : type1400 _120519) : (term751 _120477 _120519 op) = (term751 _120477 _120519 op).
Proof. exact (fun_ext (fun f : _120477 -> _120519 => @lem5791300 _120477 _120519 f op)). Qed.
Lemma lem5791302 {_120477 _120519 : Type'} : (@all (_120477 -> _120519)) = (@all (_120477 -> _120519)).
Proof. exact (eq_refl (@all (_120477 -> _120519))). Qed.
Lemma lem5791303 {_120477 _120519 : Type'} (op : type1400 _120519) : (term752 _120477 _120519 op) = (term752 _120477 _120519 op).
Proof. exact (MK_COMB (@lem5791302 _120477 _120519) (@lem5791301 _120477 _120519 op)). Qed.
Lemma lem5791304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5791305 {_120477 _120519 : Type'} (op : type1400 _120519) : (term753 _120477 _120519 op) = (term753 _120477 _120519 op).
Proof. exact (MK_COMB (@lem5791304) (@lem5791303 _120477 _120519 op)). Qed.
Lemma lem5791306 {_120477 _120519 A : Type'} (op : type1400 _120519) : (term815 _120477 _120519 A op) = (term816 _120477 _120519 A op).
Proof. exact (MK_COMB (@lem5791305 _120477 _120519 op) (@lem5791299 _120519 A op)). Qed.
Lemma lem5791309 {_120519 : Type'} (op : type1400 _120519) : (term35 _120519 op) = (term35 _120519 op).
Proof. exact (eq_refl (term35 _120519 op)). Qed.
Lemma lem5791310 {_120477 _120519 A : Type'} (op : type1400 _120519) : (term817 _120477 _120519 A op) = (term818 _120477 _120519 A op).
Proof. exact (MK_COMB (@lem5791309 _120519 op) (@lem5791306 _120477 _120519 A op)). Qed.
Lemma lem5791311 {_120477 _120519 A : Type'} : (term819 _120477 _120519 A) = (term820 _120477 _120519 A).
Proof. exact (fun_ext (fun op : type1400 _120519 => @lem5791310 _120477 _120519 A op)). Qed.
Lemma lem5791312 {_120519 : Type'} : (@all (_120519 -> _120519 -> _120519)) = (@all (_120519 -> _120519 -> _120519)).
Proof. exact (eq_refl (@all (_120519 -> _120519 -> _120519))). Qed.
Lemma lem5791313 {_120477 _120519 A : Type'} : (term599 _120477 _120519 A) = (term821 _120477 _120519 A).
Proof. exact (MK_COMB (@lem5791312 _120519) (@lem5791311 _120477 _120519 A)). Qed.
Lemma lem5791314 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791315 {_120477 _120519 A : Type'} : (term621 _120477 _120519 A) = (term822 _120477 _120519 A).
Proof. exact (MK_COMB (@lem5791314) (@lem5791313 _120477 _120519 A)). Qed.
Lemma lem5791316 {_120477 _120519 _120521 A B : Type'} : (term623 _120477 _120519 _120521 A B) = (term823 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791315 _120477 _120519 A) (@lem5791199 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791321 {A : Type'} (x : A) (s : A -> Prop) : (term824 A x s) = (term824 A x s).
Proof. exact (eq_refl (term824 A x s)). Qed.
Lemma lem5791322 {A : Type'} (x : A) : (term825 A x) = (term825 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5791321 A x s)). Qed.
Lemma lem5791323 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5791324 {A : Type'} (x : A) : (term826 A x) = (term826 A x).
Proof. exact (MK_COMB (@lem5791323 A) (@lem5791322 A x)). Qed.
Lemma lem5791325 {A : Type'} : (term827 A) = (term827 A).
Proof. exact (fun_ext (fun x : A => @lem5791324 A x)). Qed.
Lemma lem5791326 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5791327 {A : Type'} : (term828 A) = (term828 A).
Proof. exact (MK_COMB (@lem5791326 A) (@lem5791325 A)). Qed.
Lemma lem5791330 {A : Type'} : (term829 A) = (term829 A).
Proof. exact (eq_refl (term829 A)). Qed.
Lemma lem5791331 {A : Type'} : (term600 A) = (term600 A).
Proof. exact (MK_COMB (@lem5791330 A) (@lem5791327 A)). Qed.
Lemma lem5791332 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791333 {A : Type'} : (term624 A) = (term624 A).
Proof. exact (MK_COMB (@lem5791332) (@lem5791331 A)). Qed.
Lemma lem5791334 {_120477 _120519 _120521 A B : Type'} : (term626 _120477 _120519 _120521 A B) = (term830 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791333 A) (@lem5791316 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791339 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (term824 _120521 x s) = (term824 _120521 x s).
Proof. exact (eq_refl (term824 _120521 x s)). Qed.
Lemma lem5791340 {_120521 : Type'} (x : _120521) : (term825 _120521 x) = (term825 _120521 x).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5791339 _120521 x s)). Qed.
Lemma lem5791341 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5791342 {_120521 : Type'} (x : _120521) : (term826 _120521 x) = (term826 _120521 x).
Proof. exact (MK_COMB (@lem5791341 _120521) (@lem5791340 _120521 x)). Qed.
Lemma lem5791343 {_120521 : Type'} : (term827 _120521) = (term827 _120521).
Proof. exact (fun_ext (fun x : _120521 => @lem5791342 _120521 x)). Qed.
Lemma lem5791344 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5791345 {_120521 : Type'} : (term828 _120521) = (term828 _120521).
Proof. exact (MK_COMB (@lem5791344 _120521) (@lem5791343 _120521)). Qed.
Lemma lem5791348 {_120521 : Type'} : (term829 _120521) = (term829 _120521).
Proof. exact (eq_refl (term829 _120521)). Qed.
Lemma lem5791349 {_120521 : Type'} : (term600 _120521) = (term600 _120521).
Proof. exact (MK_COMB (@lem5791348 _120521) (@lem5791345 _120521)). Qed.
Lemma lem5791350 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791351 {_120521 : Type'} : (term624 _120521) = (term624 _120521).
Proof. exact (MK_COMB (@lem5791350) (@lem5791349 _120521)). Qed.
Lemma lem5791352 {_120477 _120519 _120521 A B : Type'} : (term628 _120477 _120519 _120521 A B) = (term831 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791351 _120521) (@lem5791334 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791357 {_120477 : Type'} (x : _120477) (s : _120477 -> Prop) : (term824 _120477 x s) = (term824 _120477 x s).
Proof. exact (eq_refl (term824 _120477 x s)). Qed.
Lemma lem5791358 {_120477 : Type'} (x : _120477) : (term825 _120477 x) = (term825 _120477 x).
Proof. exact (fun_ext (fun s : _120477 -> Prop => @lem5791357 _120477 x s)). Qed.
Lemma lem5791359 {_120477 : Type'} : (@all (_120477 -> Prop)) = (@all (_120477 -> Prop)).
Proof. exact (eq_refl (@all (_120477 -> Prop))). Qed.
Lemma lem5791360 {_120477 : Type'} (x : _120477) : (term826 _120477 x) = (term826 _120477 x).
Proof. exact (MK_COMB (@lem5791359 _120477) (@lem5791358 _120477 x)). Qed.
Lemma lem5791361 {_120477 : Type'} : (term827 _120477) = (term827 _120477).
Proof. exact (fun_ext (fun x : _120477 => @lem5791360 _120477 x)). Qed.
Lemma lem5791362 {_120477 : Type'} : (@all _120477) = (@all _120477).
Proof. exact (eq_refl (@all _120477)). Qed.
Lemma lem5791363 {_120477 : Type'} : (term828 _120477) = (term828 _120477).
Proof. exact (MK_COMB (@lem5791362 _120477) (@lem5791361 _120477)). Qed.
Lemma lem5791366 {_120477 : Type'} : (term829 _120477) = (term829 _120477).
Proof. exact (eq_refl (term829 _120477)). Qed.
Lemma lem5791367 {_120477 : Type'} : (term600 _120477) = (term600 _120477).
Proof. exact (MK_COMB (@lem5791366 _120477) (@lem5791363 _120477)). Qed.
Lemma lem5791368 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791369 {_120477 : Type'} : (term624 _120477) = (term624 _120477).
Proof. exact (MK_COMB (@lem5791368) (@lem5791367 _120477)). Qed.
Lemma lem5791370 {_120477 _120519 _120521 A B : Type'} : (term630 _120477 _120519 _120521 A B) = (term832 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791369 _120477) (@lem5791352 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791371 {_120521 A : Type'} (op : type636 A) (s : _120521 -> Prop) (f : type1413 _120521 A) : ((term833 _120521 A op s f) = (@iterate (A -> Prop) _120521 op s f)) = ((term833 _120521 A op s f) = (@iterate (A -> Prop) _120521 op s f)).
Proof. exact (eq_refl ((term833 _120521 A op s f) = (@iterate (A -> Prop) _120521 op s f))). Qed.
Lemma lem5791372 {_120521 A : Type'} (op : type636 A) (f : type1413 _120521 A) : (term834 _120521 A op f) = (term834 _120521 A op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5791371 _120521 A op s f)). Qed.
Lemma lem5791373 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5791374 {_120521 A : Type'} (op : type636 A) (f : type1413 _120521 A) : (term835 _120521 A op f) = (term835 _120521 A op f).
Proof. exact (MK_COMB (@lem5791373 _120521) (@lem5791372 _120521 A op f)). Qed.
Lemma lem5791375 {_120521 A : Type'} (op : type636 A) : (term836 _120521 A op) = (term836 _120521 A op).
Proof. exact (fun_ext (fun f : type1413 _120521 A => @lem5791374 _120521 A op f)). Qed.
Lemma lem5791376 {_120521 A : Type'} : (@all (_120521 -> A -> Prop)) = (@all (_120521 -> A -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> A -> Prop))). Qed.
Lemma lem5791377 {_120521 A : Type'} (op : type636 A) : (term837 _120521 A op) = (term837 _120521 A op).
Proof. exact (MK_COMB (@lem5791376 _120521 A) (@lem5791375 _120521 A op)). Qed.
Lemma lem5791378 {_120521 A : Type'} : (term838 _120521 A) = (term838 _120521 A).
Proof. exact (fun_ext (fun op : type636 A => @lem5791377 _120521 A op)). Qed.
Lemma lem5791379 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem5791380 {_120521 A : Type'} : (term602 _120521 A) = (term602 _120521 A).
Proof. exact (MK_COMB (@lem5791379 A) (@lem5791378 _120521 A)). Qed.
Lemma lem5791381 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791382 {_120521 A : Type'} : (term631 _120521 A) = (term631 _120521 A).
Proof. exact (MK_COMB (@lem5791381) (@lem5791380 _120521 A)). Qed.
Lemma lem5791383 {_120477 _120519 _120521 A B : Type'} : (term633 _120477 _120519 _120521 A B) = (term839 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791382 _120521 A) (@lem5791370 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791384 {_120477 A : Type'} (op : type636 A) (s : _120477 -> Prop) (f : type1413 _120477 A) : ((term833 _120477 A op s f) = (@iterate (A -> Prop) _120477 op s f)) = ((term833 _120477 A op s f) = (@iterate (A -> Prop) _120477 op s f)).
Proof. exact (eq_refl ((term833 _120477 A op s f) = (@iterate (A -> Prop) _120477 op s f))). Qed.
Lemma lem5791385 {_120477 A : Type'} (op : type636 A) (f : type1413 _120477 A) : (term834 _120477 A op f) = (term834 _120477 A op f).
Proof. exact (fun_ext (fun s : _120477 -> Prop => @lem5791384 _120477 A op s f)). Qed.
Lemma lem5791386 {_120477 : Type'} : (@all (_120477 -> Prop)) = (@all (_120477 -> Prop)).
Proof. exact (eq_refl (@all (_120477 -> Prop))). Qed.
Lemma lem5791387 {_120477 A : Type'} (op : type636 A) (f : type1413 _120477 A) : (term835 _120477 A op f) = (term835 _120477 A op f).
Proof. exact (MK_COMB (@lem5791386 _120477) (@lem5791385 _120477 A op f)). Qed.
Lemma lem5791388 {_120477 A : Type'} (op : type636 A) : (term836 _120477 A op) = (term836 _120477 A op).
Proof. exact (fun_ext (fun f : type1413 _120477 A => @lem5791387 _120477 A op f)). Qed.
Lemma lem5791389 {_120477 A : Type'} : (@all (_120477 -> A -> Prop)) = (@all (_120477 -> A -> Prop)).
Proof. exact (eq_refl (@all (_120477 -> A -> Prop))). Qed.
Lemma lem5791390 {_120477 A : Type'} (op : type636 A) : (term837 _120477 A op) = (term837 _120477 A op).
Proof. exact (MK_COMB (@lem5791389 _120477 A) (@lem5791388 _120477 A op)). Qed.
Lemma lem5791391 {_120477 A : Type'} : (term838 _120477 A) = (term838 _120477 A).
Proof. exact (fun_ext (fun op : type636 A => @lem5791390 _120477 A op)). Qed.
Lemma lem5791392 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem5791393 {_120477 A : Type'} : (term602 _120477 A) = (term602 _120477 A).
Proof. exact (MK_COMB (@lem5791392 A) (@lem5791391 _120477 A)). Qed.
Lemma lem5791394 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791395 {_120477 A : Type'} : (term631 _120477 A) = (term631 _120477 A).
Proof. exact (MK_COMB (@lem5791394) (@lem5791393 _120477 A)). Qed.
Lemma lem5791396 {_120477 _120519 _120521 A B : Type'} : (term635 _120477 _120519 _120521 A B) = (term840 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791395 _120477 A) (@lem5791383 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791397 {_120308 A : Type'} (op : type636 A) (s : _120308 -> Prop) (f : type1413 _120308 A) : ((term833 _120308 A op s f) = (@iterate (A -> Prop) _120308 op s f)) = ((term833 _120308 A op s f) = (@iterate (A -> Prop) _120308 op s f)).
Proof. exact (eq_refl ((term833 _120308 A op s f) = (@iterate (A -> Prop) _120308 op s f))). Qed.
Lemma lem5791398 {_120308 A : Type'} (op : type636 A) (f : type1413 _120308 A) : (term834 _120308 A op f) = (term834 _120308 A op f).
Proof. exact (fun_ext (fun s : _120308 -> Prop => @lem5791397 _120308 A op s f)). Qed.
Lemma lem5791399 {_120308 : Type'} : (@all (_120308 -> Prop)) = (@all (_120308 -> Prop)).
Proof. exact (eq_refl (@all (_120308 -> Prop))). Qed.
Lemma lem5791400 {_120308 A : Type'} (op : type636 A) (f : type1413 _120308 A) : (term835 _120308 A op f) = (term835 _120308 A op f).
Proof. exact (MK_COMB (@lem5791399 _120308) (@lem5791398 _120308 A op f)). Qed.
Lemma lem5791401 {_120308 A : Type'} (op : type636 A) : (term836 _120308 A op) = (term836 _120308 A op).
Proof. exact (fun_ext (fun f : type1413 _120308 A => @lem5791400 _120308 A op f)). Qed.
Lemma lem5791402 {_120308 A : Type'} : (@all (_120308 -> A -> Prop)) = (@all (_120308 -> A -> Prop)).
Proof. exact (eq_refl (@all (_120308 -> A -> Prop))). Qed.
Lemma lem5791403 {_120308 A : Type'} (op : type636 A) : (term837 _120308 A op) = (term837 _120308 A op).
Proof. exact (MK_COMB (@lem5791402 _120308 A) (@lem5791401 _120308 A op)). Qed.
Lemma lem5791404 {_120308 A : Type'} : (term838 _120308 A) = (term838 _120308 A).
Proof. exact (fun_ext (fun op : type636 A => @lem5791403 _120308 A op)). Qed.
Lemma lem5791405 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem5791406 {_120308 A : Type'} : (term602 _120308 A) = (term602 _120308 A).
Proof. exact (MK_COMB (@lem5791405 A) (@lem5791404 _120308 A)). Qed.
Lemma lem5791407 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791408 {_120308 A : Type'} : (term631 _120308 A) = (term631 _120308 A).
Proof. exact (MK_COMB (@lem5791407) (@lem5791406 _120308 A)). Qed.
Lemma lem5791409 {_120308 _120477 _120519 _120521 A B : Type'} : (term637 _120308 _120477 _120519 _120521 A B) = (term841 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791408 _120308 A) (@lem5791396 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791410 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : ((term842 A B op s f) = (@iterate B A op s f)) = ((term842 A B op s f) = (@iterate B A op s f)).
Proof. exact (eq_refl ((term842 A B op s f) = (@iterate B A op s f))). Qed.
Lemma lem5791411 {A B : Type'} (op : type1400 B) (f : A -> B) : (term843 A B op f) = (term843 A B op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5791410 A B op s f)). Qed.
Lemma lem5791412 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5791413 {A B : Type'} (op : type1400 B) (f : A -> B) : (term844 A B op f) = (term844 A B op f).
Proof. exact (MK_COMB (@lem5791412 A) (@lem5791411 A B op f)). Qed.
Lemma lem5791414 {A B : Type'} (op : type1400 B) : (term845 A B op) = (term845 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5791413 A B op f)). Qed.
Lemma lem5791415 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5791416 {A B : Type'} (op : type1400 B) : (term846 A B op) = (term846 A B op).
Proof. exact (MK_COMB (@lem5791415 A B) (@lem5791414 A B op)). Qed.
Lemma lem5791417 {A B : Type'} : (term847 A B) = (term847 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5791416 A B op)). Qed.
Lemma lem5791418 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5791419 {A B : Type'} : (term601 A B) = (term601 A B).
Proof. exact (MK_COMB (@lem5791418 B) (@lem5791417 A B)). Qed.
Lemma lem5791420 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791421 {A B : Type'} : (term638 A B) = (term638 A B).
Proof. exact (MK_COMB (@lem5791420) (@lem5791419 A B)). Qed.
Lemma lem5791422 {_120308 _120477 _120519 _120521 A B : Type'} : (term640 _120308 _120477 _120519 _120521 A B) = (term848 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791421 A B) (@lem5791409 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791423 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : ((term842 _120521 B op s f) = (@iterate B _120521 op s f)) = ((term842 _120521 B op s f) = (@iterate B _120521 op s f)).
Proof. exact (eq_refl ((term842 _120521 B op s f) = (@iterate B _120521 op s f))). Qed.
Lemma lem5791424 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term843 _120521 B op f) = (term843 _120521 B op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5791423 _120521 B op s f)). Qed.
Lemma lem5791425 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5791426 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term844 _120521 B op f) = (term844 _120521 B op f).
Proof. exact (MK_COMB (@lem5791425 _120521) (@lem5791424 _120521 B op f)). Qed.
Lemma lem5791427 {_120521 B : Type'} (op : type1400 B) : (term845 _120521 B op) = (term845 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5791426 _120521 B op f)). Qed.
Lemma lem5791428 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5791429 {_120521 B : Type'} (op : type1400 B) : (term846 _120521 B op) = (term846 _120521 B op).
Proof. exact (MK_COMB (@lem5791428 _120521 B) (@lem5791427 _120521 B op)). Qed.
Lemma lem5791430 {_120521 B : Type'} : (term847 _120521 B) = (term847 _120521 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5791429 _120521 B op)). Qed.
Lemma lem5791431 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5791432 {_120521 B : Type'} : (term601 _120521 B) = (term601 _120521 B).
Proof. exact (MK_COMB (@lem5791431 B) (@lem5791430 _120521 B)). Qed.
Lemma lem5791433 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791434 {_120521 B : Type'} : (term638 _120521 B) = (term638 _120521 B).
Proof. exact (MK_COMB (@lem5791433) (@lem5791432 _120521 B)). Qed.
Lemma lem5791435 {_120308 _120477 _120519 _120521 A B : Type'} : (term642 _120308 _120477 _120519 _120521 A B) = (term849 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791434 _120521 B) (@lem5791422 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791436 {_120477 B : Type'} (op : type1400 B) (s : _120477 -> Prop) (f : _120477 -> B) : ((term842 _120477 B op s f) = (@iterate B _120477 op s f)) = ((term842 _120477 B op s f) = (@iterate B _120477 op s f)).
Proof. exact (eq_refl ((term842 _120477 B op s f) = (@iterate B _120477 op s f))). Qed.
Lemma lem5791437 {_120477 B : Type'} (op : type1400 B) (f : _120477 -> B) : (term843 _120477 B op f) = (term843 _120477 B op f).
Proof. exact (fun_ext (fun s : _120477 -> Prop => @lem5791436 _120477 B op s f)). Qed.
Lemma lem5791438 {_120477 : Type'} : (@all (_120477 -> Prop)) = (@all (_120477 -> Prop)).
Proof. exact (eq_refl (@all (_120477 -> Prop))). Qed.
Lemma lem5791439 {_120477 B : Type'} (op : type1400 B) (f : _120477 -> B) : (term844 _120477 B op f) = (term844 _120477 B op f).
Proof. exact (MK_COMB (@lem5791438 _120477) (@lem5791437 _120477 B op f)). Qed.
Lemma lem5791440 {_120477 B : Type'} (op : type1400 B) : (term845 _120477 B op) = (term845 _120477 B op).
Proof. exact (fun_ext (fun f : _120477 -> B => @lem5791439 _120477 B op f)). Qed.
Lemma lem5791441 {_120477 B : Type'} : (@all (_120477 -> B)) = (@all (_120477 -> B)).
Proof. exact (eq_refl (@all (_120477 -> B))). Qed.
Lemma lem5791442 {_120477 B : Type'} (op : type1400 B) : (term846 _120477 B op) = (term846 _120477 B op).
Proof. exact (MK_COMB (@lem5791441 _120477 B) (@lem5791440 _120477 B op)). Qed.
Lemma lem5791443 {_120477 B : Type'} : (term847 _120477 B) = (term847 _120477 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5791442 _120477 B op)). Qed.
Lemma lem5791444 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5791445 {_120477 B : Type'} : (term601 _120477 B) = (term601 _120477 B).
Proof. exact (MK_COMB (@lem5791444 B) (@lem5791443 _120477 B)). Qed.
Lemma lem5791446 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791447 {_120477 B : Type'} : (term638 _120477 B) = (term638 _120477 B).
Proof. exact (MK_COMB (@lem5791446) (@lem5791445 _120477 B)). Qed.
Lemma lem5791448 {_120308 _120477 _120519 _120521 A B : Type'} : (term644 _120308 _120477 _120519 _120521 A B) = (term850 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791447 _120477 B) (@lem5791435 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791449 {_120308 B : Type'} (op : type1400 B) (s : _120308 -> Prop) (f : _120308 -> B) : ((term842 _120308 B op s f) = (@iterate B _120308 op s f)) = ((term842 _120308 B op s f) = (@iterate B _120308 op s f)).
Proof. exact (eq_refl ((term842 _120308 B op s f) = (@iterate B _120308 op s f))). Qed.
Lemma lem5791450 {_120308 B : Type'} (op : type1400 B) (f : _120308 -> B) : (term843 _120308 B op f) = (term843 _120308 B op f).
Proof. exact (fun_ext (fun s : _120308 -> Prop => @lem5791449 _120308 B op s f)). Qed.
Lemma lem5791451 {_120308 : Type'} : (@all (_120308 -> Prop)) = (@all (_120308 -> Prop)).
Proof. exact (eq_refl (@all (_120308 -> Prop))). Qed.
Lemma lem5791452 {_120308 B : Type'} (op : type1400 B) (f : _120308 -> B) : (term844 _120308 B op f) = (term844 _120308 B op f).
Proof. exact (MK_COMB (@lem5791451 _120308) (@lem5791450 _120308 B op f)). Qed.
Lemma lem5791453 {_120308 B : Type'} (op : type1400 B) : (term845 _120308 B op) = (term845 _120308 B op).
Proof. exact (fun_ext (fun f : _120308 -> B => @lem5791452 _120308 B op f)). Qed.
Lemma lem5791454 {_120308 B : Type'} : (@all (_120308 -> B)) = (@all (_120308 -> B)).
Proof. exact (eq_refl (@all (_120308 -> B))). Qed.
Lemma lem5791455 {_120308 B : Type'} (op : type1400 B) : (term846 _120308 B op) = (term846 _120308 B op).
Proof. exact (MK_COMB (@lem5791454 _120308 B) (@lem5791453 _120308 B op)). Qed.
Lemma lem5791456 {_120308 B : Type'} : (term847 _120308 B) = (term847 _120308 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5791455 _120308 B op)). Qed.
Lemma lem5791457 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5791458 {_120308 B : Type'} : (term601 _120308 B) = (term601 _120308 B).
Proof. exact (MK_COMB (@lem5791457 B) (@lem5791456 _120308 B)). Qed.
Lemma lem5791459 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791460 {_120308 B : Type'} : (term638 _120308 B) = (term638 _120308 B).
Proof. exact (MK_COMB (@lem5791459) (@lem5791458 _120308 B)). Qed.
Lemma lem5791461 {_120308 _120477 _120519 _120521 A B : Type'} : (term646 _120308 _120477 _120519 _120521 A B) = (term851 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791460 _120308 B) (@lem5791448 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791462 {_120519 A : Type'} (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : ((term852 _120519 A op s f) = (@iterate _120519 A op s f)) = ((term852 _120519 A op s f) = (@iterate _120519 A op s f)).
Proof. exact (eq_refl ((term852 _120519 A op s f) = (@iterate _120519 A op s f))). Qed.
Lemma lem5791463 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) : (term853 _120519 A op f) = (term853 _120519 A op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5791462 _120519 A op s f)). Qed.
Lemma lem5791464 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5791465 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) : (term854 _120519 A op f) = (term854 _120519 A op f).
Proof. exact (MK_COMB (@lem5791464 A) (@lem5791463 _120519 A op f)). Qed.
Lemma lem5791466 {_120519 A : Type'} (op : type1400 _120519) : (term855 _120519 A op) = (term855 _120519 A op).
Proof. exact (fun_ext (fun f : A -> _120519 => @lem5791465 _120519 A op f)). Qed.
Lemma lem5791467 {_120519 A : Type'} : (@all (A -> _120519)) = (@all (A -> _120519)).
Proof. exact (eq_refl (@all (A -> _120519))). Qed.
Lemma lem5791468 {_120519 A : Type'} (op : type1400 _120519) : (term856 _120519 A op) = (term856 _120519 A op).
Proof. exact (MK_COMB (@lem5791467 _120519 A) (@lem5791466 _120519 A op)). Qed.
Lemma lem5791469 {_120519 A : Type'} : (term857 _120519 A) = (term857 _120519 A).
Proof. exact (fun_ext (fun op : type1400 _120519 => @lem5791468 _120519 A op)). Qed.
Lemma lem5791470 {_120519 : Type'} : (@all (_120519 -> _120519 -> _120519)) = (@all (_120519 -> _120519 -> _120519)).
Proof. exact (eq_refl (@all (_120519 -> _120519 -> _120519))). Qed.
Lemma lem5791471 {_120519 A : Type'} : (term603 _120519 A) = (term603 _120519 A).
Proof. exact (MK_COMB (@lem5791470 _120519) (@lem5791469 _120519 A)). Qed.
Lemma lem5791472 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791473 {_120519 A : Type'} : (term647 _120519 A) = (term647 _120519 A).
Proof. exact (MK_COMB (@lem5791472) (@lem5791471 _120519 A)). Qed.
Lemma lem5791474 {_120308 _120477 _120519 _120521 A B : Type'} : (term649 _120308 _120477 _120519 _120521 A B) = (term858 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791473 _120519 A) (@lem5791461 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791475 {_120519 _120521 : Type'} (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : ((term852 _120519 _120521 op s f) = (@iterate _120519 _120521 op s f)) = ((term852 _120519 _120521 op s f) = (@iterate _120519 _120521 op s f)).
Proof. exact (eq_refl ((term852 _120519 _120521 op s f) = (@iterate _120519 _120521 op s f))). Qed.
Lemma lem5791476 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term853 _120519 _120521 op f) = (term853 _120519 _120521 op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5791475 _120519 _120521 op s f)). Qed.
Lemma lem5791477 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5791478 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term854 _120519 _120521 op f) = (term854 _120519 _120521 op f).
Proof. exact (MK_COMB (@lem5791477 _120521) (@lem5791476 _120519 _120521 op f)). Qed.
Lemma lem5791479 {_120519 _120521 : Type'} (op : type1400 _120519) : (term855 _120519 _120521 op) = (term855 _120519 _120521 op).
Proof. exact (fun_ext (fun f : _120521 -> _120519 => @lem5791478 _120519 _120521 op f)). Qed.
Lemma lem5791480 {_120519 _120521 : Type'} : (@all (_120521 -> _120519)) = (@all (_120521 -> _120519)).
Proof. exact (eq_refl (@all (_120521 -> _120519))). Qed.
Lemma lem5791481 {_120519 _120521 : Type'} (op : type1400 _120519) : (term856 _120519 _120521 op) = (term856 _120519 _120521 op).
Proof. exact (MK_COMB (@lem5791480 _120519 _120521) (@lem5791479 _120519 _120521 op)). Qed.
Lemma lem5791482 {_120519 _120521 : Type'} : (term857 _120519 _120521) = (term857 _120519 _120521).
Proof. exact (fun_ext (fun op : type1400 _120519 => @lem5791481 _120519 _120521 op)). Qed.
Lemma lem5791483 {_120519 : Type'} : (@all (_120519 -> _120519 -> _120519)) = (@all (_120519 -> _120519 -> _120519)).
Proof. exact (eq_refl (@all (_120519 -> _120519 -> _120519))). Qed.
Lemma lem5791484 {_120519 _120521 : Type'} : (term603 _120519 _120521) = (term603 _120519 _120521).
Proof. exact (MK_COMB (@lem5791483 _120519) (@lem5791482 _120519 _120521)). Qed.
Lemma lem5791485 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791486 {_120519 _120521 : Type'} : (term647 _120519 _120521) = (term647 _120519 _120521).
Proof. exact (MK_COMB (@lem5791485) (@lem5791484 _120519 _120521)). Qed.
Lemma lem5791487 {_120308 _120477 _120519 _120521 A B : Type'} : (term651 _120308 _120477 _120519 _120521 A B) = (term859 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791486 _120519 _120521) (@lem5791474 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791488 {_120477 _120519 : Type'} (op : type1400 _120519) (s : _120477 -> Prop) (f : _120477 -> _120519) : ((term842 _120477 _120519 op s f) = (@iterate _120519 _120477 op s f)) = ((term842 _120477 _120519 op s f) = (@iterate _120519 _120477 op s f)).
Proof. exact (eq_refl ((term842 _120477 _120519 op s f) = (@iterate _120519 _120477 op s f))). Qed.
Lemma lem5791489 {_120477 _120519 : Type'} (op : type1400 _120519) (f : _120477 -> _120519) : (term843 _120477 _120519 op f) = (term843 _120477 _120519 op f).
Proof. exact (fun_ext (fun s : _120477 -> Prop => @lem5791488 _120477 _120519 op s f)). Qed.
Lemma lem5791490 {_120477 : Type'} : (@all (_120477 -> Prop)) = (@all (_120477 -> Prop)).
Proof. exact (eq_refl (@all (_120477 -> Prop))). Qed.
Lemma lem5791491 {_120477 _120519 : Type'} (op : type1400 _120519) (f : _120477 -> _120519) : (term844 _120477 _120519 op f) = (term844 _120477 _120519 op f).
Proof. exact (MK_COMB (@lem5791490 _120477) (@lem5791489 _120477 _120519 op f)). Qed.
Lemma lem5791492 {_120477 _120519 : Type'} (op : type1400 _120519) : (term845 _120477 _120519 op) = (term845 _120477 _120519 op).
Proof. exact (fun_ext (fun f : _120477 -> _120519 => @lem5791491 _120477 _120519 op f)). Qed.
Lemma lem5791493 {_120477 _120519 : Type'} : (@all (_120477 -> _120519)) = (@all (_120477 -> _120519)).
Proof. exact (eq_refl (@all (_120477 -> _120519))). Qed.
Lemma lem5791494 {_120477 _120519 : Type'} (op : type1400 _120519) : (term846 _120477 _120519 op) = (term846 _120477 _120519 op).
Proof. exact (MK_COMB (@lem5791493 _120477 _120519) (@lem5791492 _120477 _120519 op)). Qed.
Lemma lem5791495 {_120477 _120519 : Type'} : (term847 _120477 _120519) = (term847 _120477 _120519).
Proof. exact (fun_ext (fun op : type1400 _120519 => @lem5791494 _120477 _120519 op)). Qed.
Lemma lem5791496 {_120519 : Type'} : (@all (_120519 -> _120519 -> _120519)) = (@all (_120519 -> _120519 -> _120519)).
Proof. exact (eq_refl (@all (_120519 -> _120519 -> _120519))). Qed.
Lemma lem5791497 {_120477 _120519 : Type'} : (term601 _120477 _120519) = (term601 _120477 _120519).
Proof. exact (MK_COMB (@lem5791496 _120519) (@lem5791495 _120477 _120519)). Qed.
Lemma lem5791498 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791499 {_120477 _120519 : Type'} : (term638 _120477 _120519) = (term638 _120477 _120519).
Proof. exact (MK_COMB (@lem5791498) (@lem5791497 _120477 _120519)). Qed.
Lemma lem5791500 {_120308 _120477 _120519 _120521 A B : Type'} : (term653 _120308 _120477 _120519 _120521 A B) = (term860 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791499 _120477 _120519) (@lem5791487 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791501 {_120308 _120519 : Type'} (op : type1400 _120519) (s : _120308 -> Prop) (f : _120308 -> _120519) : ((term842 _120308 _120519 op s f) = (@iterate _120519 _120308 op s f)) = ((term842 _120308 _120519 op s f) = (@iterate _120519 _120308 op s f)).
Proof. exact (eq_refl ((term842 _120308 _120519 op s f) = (@iterate _120519 _120308 op s f))). Qed.
Lemma lem5791502 {_120308 _120519 : Type'} (op : type1400 _120519) (f : _120308 -> _120519) : (term843 _120308 _120519 op f) = (term843 _120308 _120519 op f).
Proof. exact (fun_ext (fun s : _120308 -> Prop => @lem5791501 _120308 _120519 op s f)). Qed.
Lemma lem5791503 {_120308 : Type'} : (@all (_120308 -> Prop)) = (@all (_120308 -> Prop)).
Proof. exact (eq_refl (@all (_120308 -> Prop))). Qed.
Lemma lem5791504 {_120308 _120519 : Type'} (op : type1400 _120519) (f : _120308 -> _120519) : (term844 _120308 _120519 op f) = (term844 _120308 _120519 op f).
Proof. exact (MK_COMB (@lem5791503 _120308) (@lem5791502 _120308 _120519 op f)). Qed.
Lemma lem5791505 {_120308 _120519 : Type'} (op : type1400 _120519) : (term845 _120308 _120519 op) = (term845 _120308 _120519 op).
Proof. exact (fun_ext (fun f : _120308 -> _120519 => @lem5791504 _120308 _120519 op f)). Qed.
Lemma lem5791506 {_120308 _120519 : Type'} : (@all (_120308 -> _120519)) = (@all (_120308 -> _120519)).
Proof. exact (eq_refl (@all (_120308 -> _120519))). Qed.
Lemma lem5791507 {_120308 _120519 : Type'} (op : type1400 _120519) : (term846 _120308 _120519 op) = (term846 _120308 _120519 op).
Proof. exact (MK_COMB (@lem5791506 _120308 _120519) (@lem5791505 _120308 _120519 op)). Qed.
Lemma lem5791508 {_120308 _120519 : Type'} : (term847 _120308 _120519) = (term847 _120308 _120519).
Proof. exact (fun_ext (fun op : type1400 _120519 => @lem5791507 _120308 _120519 op)). Qed.
Lemma lem5791509 {_120519 : Type'} : (@all (_120519 -> _120519 -> _120519)) = (@all (_120519 -> _120519 -> _120519)).
Proof. exact (eq_refl (@all (_120519 -> _120519 -> _120519))). Qed.
Lemma lem5791510 {_120308 _120519 : Type'} : (term601 _120308 _120519) = (term601 _120308 _120519).
Proof. exact (MK_COMB (@lem5791509 _120519) (@lem5791508 _120308 _120519)). Qed.
Lemma lem5791511 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791512 {_120308 _120519 : Type'} : (term638 _120308 _120519) = (term638 _120308 _120519).
Proof. exact (MK_COMB (@lem5791511) (@lem5791510 _120308 _120519)). Qed.
Lemma lem5791513 {_120308 _120477 _120519 _120521 A B : Type'} : (term655 _120308 _120477 _120519 _120521 A B) = (term861 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791512 _120308 _120519) (@lem5791500 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791518 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term656 A B s f op) = (term656 A B s f op).
Proof. exact (eq_refl (term656 A B s f op)). Qed.
Lemma lem5791519 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term658 _120308 _120477 _120519 _120521 A B s f op) = (term862 _120308 _120477 _120519 _120521 A B s f op).
Proof. exact (MK_COMB (@lem5791518 A B s f op) (@lem5791513 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5791522 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term659 A B op f s) = (term659 A B op f s).
Proof. exact (eq_refl (term659 A B op f s)). Qed.
Lemma lem5791523 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term661 _120308 _120477 _120519 _120521 A B s f op) = (term863 _120308 _120477 _120519 _120521 A B s f op).
Proof. exact (MK_COMB (@lem5791522 A B op f s) (@lem5791519 _120308 _120477 _120519 _120521 A B s f op)). Qed.
Lemma lem5791528 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term84 A B s f x op) = (term84 A B s f x op).
Proof. exact (eq_refl (term84 A B s f x op)). Qed.
Lemma lem5791529 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term85 A B s f op) = (term85 A B s f op).
Proof. exact (fun_ext (fun x : A => @lem5791528 A B s f x op)). Qed.
Lemma lem5791530 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5791531 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term0 A B s f op) = (term0 A B s f op).
Proof. exact (MK_COMB (@lem5791530 A) (@lem5791529 A B s f op)). Qed.
Lemma lem5791532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5791533 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term32 A B s f op) = (term32 A B s f op).
Proof. exact (MK_COMB (@lem5791532) (@lem5791531 A B s f op)). Qed.
Lemma lem5791534 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term663 _120308 _120477 _120519 _120521 A B s f op) = (term864 _120308 _120477 _120519 _120521 A B s f op).
Proof. exact (MK_COMB (@lem5791533 A B s f op) (@lem5791523 _120308 _120477 _120519 _120521 A B s f op)). Qed.
Lemma lem5791537 {B : Type'} (op : type1400 B) : (term35 B op) = (term35 B op).
Proof. exact (eq_refl (term35 B op)). Qed.
Lemma lem5791538 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term664 _120308 _120477 _120519 _120521 A B s f op) = (term865 _120308 _120477 _120519 _120521 A B s f op).
Proof. exact (MK_COMB (@lem5791537 B op) (@lem5791534 _120308 _120477 _120519 _120521 A B s f op)). Qed.
Lemma lem5791539 {_120308 _120477 _120519 _120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term666 _120308 _120477 _120519 _120521 A B f op) = (term866 _120308 _120477 _120519 _120521 A B f op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5791538 _120308 _120477 _120519 _120521 A B s f op)). Qed.
Lemma lem5791540 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5791541 {_120308 _120477 _120519 _120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term668 _120308 _120477 _120519 _120521 A B f op) = (term867 _120308 _120477 _120519 _120521 A B f op).
Proof. exact (MK_COMB (@lem5791540 A) (@lem5791539 _120308 _120477 _120519 _120521 A B f op)). Qed.
Lemma lem5791542 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) : (term670 _120308 _120477 _120519 _120521 A B op) = (term868 _120308 _120477 _120519 _120521 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5791541 _120308 _120477 _120519 _120521 A B f op)). Qed.
Lemma lem5791543 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5791544 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) : (term672 _120308 _120477 _120519 _120521 A B op) = (term869 _120308 _120477 _120519 _120521 A B op).
Proof. exact (MK_COMB (@lem5791543 A B) (@lem5791542 _120308 _120477 _120519 _120521 A B op)). Qed.
Lemma lem5791545 {_120308 _120477 _120519 _120521 A B : Type'} : (term674 _120308 _120477 _120519 _120521 A B) = (term870 _120308 _120477 _120519 _120521 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5791544 _120308 _120477 _120519 _120521 A B op)). Qed.
Lemma lem5791546 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5791547 {_120308 _120477 _120519 _120521 A B : Type'} : (term676 _120308 _120477 _120519 _120521 A B) = (term871 _120308 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5791546 B) (@lem5791545 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5792132 {_120308 _120477 _120519 _120521 A B : Type'} : (term675 _120308 _120477 _120519 _120521 A B) = (term871 _120308 _120477 _120519 _120521 A B).
Proof. exact (TRANS (@lem5790615 _120308 _120477 _120519 _120521 A B) (@lem5791547 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5792133 {_120308 _120477 _120519 _120521 A B : Type'} : (term871 _120308 _120477 _120519 _120521 A B) = (term675 _120308 _120477 _120519 _120521 A B).
Proof. exact (SYM (@lem5792132 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5792145 {A B : Type'} (h1 : term601 A B) : term601 A B.
Proof. exact (h1). Qed.
Lemma lem5792156 {_120521 A B : Type'} (h1 : term760 _120521 A B) : term760 _120521 A B.
Proof. exact (h1). Qed.
Lemma lem5792163 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5792232 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : (@support A B op f s) = (@EMPTY A)) : (@support A B op f s) = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5792238 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term594 A B s f op) : term594 A B s f op.
Proof. exact (h1). Qed.
Lemma lem5792428 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : ((term842 A B op s f) = (@iterate B A op s f)) = ((term842 A B op s f) = (@iterate B A op s f)).
Proof. exact (eq_refl ((term842 A B op s f) = (@iterate B A op s f))). Qed.
Lemma lem5792429 {A B : Type'} (op : type1400 B) (f : A -> B) : (term843 A B op f) = (term843 A B op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5792428 A B op s f)). Qed.
Lemma lem5792430 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5792431 {A B : Type'} (op : type1400 B) (f : A -> B) : (term844 A B op f) = (term844 A B op f).
Proof. exact (MK_COMB (@lem5792430 A) (@lem5792429 A B op f)). Qed.
Lemma lem5792432 {A B : Type'} (op : type1400 B) : (term845 A B op) = (term845 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5792431 A B op f)). Qed.
Lemma lem5792433 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5792434 {A B : Type'} (op : type1400 B) : (term846 A B op) = (term846 A B op).
Proof. exact (MK_COMB (@lem5792433 A B) (@lem5792432 A B op)). Qed.
Lemma lem5792435 {A B : Type'} : (term847 A B) = (term847 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5792434 A B op)). Qed.
Lemma lem5792436 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5792453 {A B : Type'} : (term601 A B) = (term601 A B).
Proof. exact (MK_COMB (@lem5792436 B) (@lem5792435 A B)). Qed.
Lemma lem5792454 {A B : Type'} (h1 : term601 A B) : term601 A B.
Proof. exact (EQ_MP (@lem5792453 A B) (@lem5792145 A B h1)). Qed.
Lemma lem5795039 {A B : Type'} (f : A -> B) (op : type1400 B) : ((@iterate B A op (@EMPTY A) f) = (@neutral B op)) = ((@iterate B A op (@EMPTY A) f) = (@neutral B op)).
Proof. exact (eq_refl ((@iterate B A op (@EMPTY A) f) = (@neutral B op))). Qed.
Lemma lem5795040 {A B : Type'} (op : type1400 B) : (term751 A B op) = (term751 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5795039 A B f op)). Qed.
Lemma lem5795041 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5795042 {A B : Type'} (op : type1400 B) : (term752 A B op) = (term752 A B op).
Proof. exact (MK_COMB (@lem5795041 A B) (@lem5795040 A B op)). Qed.
Lemma lem5795050 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term734 _120521 B x op s f) = (term872 _120521 B x op s f).
Proof. exact (@lem17265 (@FINITE _120521 s) ((term728 _120521 B op x s f) = (@iterate B _120521 op s f))). Qed.
Lemma lem5795052 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (term90 _120521 x s) = (term90 _120521 x s).
Proof. exact (eq_refl (term90 _120521 x s)). Qed.
Lemma lem5795053 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term873 _120521 B x op s f) = (term874 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5795052 _120521 x s) (@lem5795050 _120521 B x op s f)). Qed.
Lemma lem5795061 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term730 _120521 B x op s f) = (term875 _120521 B x op s f).
Proof. exact (@lem17265 (@FINITE _120521 s) ((term728 _120521 B op x s f) = (term724 _120521 B x op s f))). Qed.
Lemma lem5795063 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (term442 _120521 x s) = (term442 _120521 x s).
Proof. exact (eq_refl (term442 _120521 x s)). Qed.
Lemma lem5795064 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term876 _120521 B x op s f) = (term877 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5795063 _120521 x s) (@lem5795061 _120521 B x op s f)). Qed.
Lemma lem5795065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5795066 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term878 _120521 B x op s f) = (term879 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5795065) (@lem5795053 _120521 B x op s f)). Qed.
Lemma lem5795067 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term738 _120521 B x op s f) = (term880 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5795066 _120521 B x op s f) (@lem5795064 _120521 B x op s f)). Qed.
Lemma lem5795068 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term740 _120521 B x op f) = (term881 _120521 B x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5795067 _120521 B x op s f)). Qed.
Lemma lem5795069 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5795070 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term742 _120521 B x op f) = (term882 _120521 B x op f).
Proof. exact (MK_COMB (@lem5795069 _120521) (@lem5795068 _120521 B x op f)). Qed.
Lemma lem5795071 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term744 _120521 B op f) = (term883 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5795070 _120521 B x op f)). Qed.
Lemma lem5795072 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5795073 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term746 _120521 B op f) = (term884 _120521 B op f).
Proof. exact (MK_COMB (@lem5795072 _120521) (@lem5795071 _120521 B op f)). Qed.
Lemma lem5795074 {_120521 B : Type'} (op : type1400 B) : (term748 _120521 B op) = (term885 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5795073 _120521 B op f)). Qed.
Lemma lem5795075 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5795076 {_120521 B : Type'} (op : type1400 B) : (term750 _120521 B op) = (term886 _120521 B op).
Proof. exact (MK_COMB (@lem5795075 _120521 B) (@lem5795074 _120521 B op)). Qed.
Lemma lem5795077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5795078 {A B : Type'} (op : type1400 B) : (term753 A B op) = (term753 A B op).
Proof. exact (MK_COMB (@lem5795077) (@lem5795042 A B op)). Qed.
Lemma lem5795079 {_120521 A B : Type'} (op : type1400 B) : (term755 _120521 A B op) = (term887 _120521 A B op).
Proof. exact (MK_COMB (@lem5795078 A B op) (@lem5795076 _120521 B op)). Qed.
Lemma lem5795081 {B : Type'} (op : type1400 B) : (term888 B op) = (term888 B op).
Proof. exact (eq_refl (term888 B op)). Qed.
Lemma lem5795082 {_120521 A B : Type'} (op : type1400 B) : (term889 _120521 A B op) = (term890 _120521 A B op).
Proof. exact (MK_COMB (@lem5795081 B op) (@lem5795079 _120521 A B op)). Qed.
Lemma lem5795083 {_120521 A B : Type'} (op : type1400 B) : (term757 _120521 A B op) = (term889 _120521 A B op).
Proof. exact (@lem17265 (@monoidal B op) (term755 _120521 A B op)). Qed.
Lemma lem5795084 {_120521 A B : Type'} (op : type1400 B) : (term757 _120521 A B op) = (term890 _120521 A B op).
Proof. exact (TRANS (@lem5795083 _120521 A B op) (@lem5795082 _120521 A B op)). Qed.
Lemma lem5795085 {_120521 A B : Type'} : (term759 _120521 A B) = (term891 _120521 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5795084 _120521 A B op)). Qed.
Lemma lem5795086 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5795087 {_120521 A B : Type'} : (term760 _120521 A B) = (term892 _120521 A B).
Proof. exact (MK_COMB (@lem5795086 B) (@lem5795085 _120521 A B)). Qed.
Lemma lem5795149 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5795150 {_120521 : Type'} (P : type686 _120521) (Q : type686 _120521) : (term112 _120521 P Q) = (term113 _120521 P Q).
Proof. exact (@lem5795149 (_120521 -> Prop) P Q). Qed.
Lemma lem5795151 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term893 _120521 B x op f) = (term894 _120521 B x op f).
Proof. exact (@lem5795150 _120521 (term895 _120521 B x op f) (term896 _120521 B x op f)). Qed.
Lemma lem5795152 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term897 _120521 B x op f s) = (term874 _120521 B x op s f).
Proof. exact (eq_refl (term897 _120521 B x op f s)). Qed.
Lemma lem5795153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5795154 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term898 _120521 B x op f s) = (term879 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5795153) (@lem5795152 _120521 B x op s f)). Qed.
Lemma lem5795155 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term899 _120521 B x op f s) = (term877 _120521 B x op s f).
Proof. exact (eq_refl (term899 _120521 B x op f s)). Qed.
Lemma lem5795156 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term900 _120521 B x op f s) = (term880 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5795154 _120521 B x op s f) (@lem5795155 _120521 B x op s f)). Qed.
Lemma lem5795157 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term901 _120521 B x op f) = (term881 _120521 B x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5795156 _120521 B x op s f)). Qed.
Lemma lem5795158 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5795159 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term893 _120521 B x op f) = (term882 _120521 B x op f).
Proof. exact (MK_COMB (@lem5795158 _120521) (@lem5795157 _120521 B x op f)). Qed.
Lemma lem5795160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5795161 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term902 _120521 B x op f) = (term903 _120521 B x op f).
Proof. exact (MK_COMB (@lem5795160) (@lem5795159 _120521 B x op f)). Qed.
Lemma lem5795162 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term897 _120521 B x op f s) = (term874 _120521 B x op s f).
Proof. exact (eq_refl (term897 _120521 B x op f s)). Qed.
Lemma lem5795163 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term904 _120521 B x op f) = (term895 _120521 B x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5795162 _120521 B x op s f)). Qed.
Lemma lem5795164 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5795165 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term905 _120521 B x op f) = (term906 _120521 B x op f).
Proof. exact (MK_COMB (@lem5795164 _120521) (@lem5795163 _120521 B x op f)). Qed.
Lemma lem5795166 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5795167 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term907 _120521 B x op f) = (term908 _120521 B x op f).
Proof. exact (MK_COMB (@lem5795166) (@lem5795165 _120521 B x op f)). Qed.
Lemma lem5795168 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term899 _120521 B x op f s) = (term877 _120521 B x op s f).
Proof. exact (eq_refl (term899 _120521 B x op f s)). Qed.
Lemma lem5795169 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term909 _120521 B x op f) = (term896 _120521 B x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5795168 _120521 B x op s f)). Qed.
Lemma lem5795170 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5795171 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term910 _120521 B x op f) = (term911 _120521 B x op f).
Proof. exact (MK_COMB (@lem5795170 _120521) (@lem5795169 _120521 B x op f)). Qed.
Lemma lem5795172 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term894 _120521 B x op f) = (term912 _120521 B x op f).
Proof. exact (MK_COMB (@lem5795167 _120521 B x op f) (@lem5795171 _120521 B x op f)). Qed.
Lemma lem5795173 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : ((term893 _120521 B x op f) = (term894 _120521 B x op f)) = ((term882 _120521 B x op f) = (term912 _120521 B x op f)).
Proof. exact (MK_COMB (@lem5795161 _120521 B x op f) (@lem5795172 _120521 B x op f)). Qed.
Lemma lem5795174 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term882 _120521 B x op f) = (term912 _120521 B x op f).
Proof. exact (EQ_MP (@lem5795173 _120521 B x op f) (@lem5795151 _120521 B x op f)). Qed.
Lemma lem5795271 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term883 _120521 B op f) = (term913 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5795174 _120521 B x op f)). Qed.
Lemma lem5795272 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5795273 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term884 _120521 B op f) = (term914 _120521 B op f).
Proof. exact (MK_COMB (@lem5795272 _120521) (@lem5795271 _120521 B op f)). Qed.
Lemma lem5795275 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5795276 {_120521 : Type'} (P : _120521 -> Prop) (Q : _120521 -> Prop) : (term110 _120521 P Q) = (term111 _120521 P Q).
Proof. exact (@lem5795275 _120521 P Q). Qed.
Lemma lem5795277 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term915 _120521 B op f) = (term916 _120521 B op f).
Proof. exact (@lem5795276 _120521 (term917 _120521 B op f) (term918 _120521 B op f)). Qed.
Lemma lem5795278 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term919 _120521 B op f x) = (term906 _120521 B x op f).
Proof. exact (eq_refl (term919 _120521 B op f x)). Qed.
Lemma lem5795279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5795280 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term920 _120521 B op f x) = (term908 _120521 B x op f).
Proof. exact (MK_COMB (@lem5795279) (@lem5795278 _120521 B x op f)). Qed.
Lemma lem5795281 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term921 _120521 B op f x) = (term911 _120521 B x op f).
Proof. exact (eq_refl (term921 _120521 B op f x)). Qed.
Lemma lem5795282 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term922 _120521 B op f x) = (term912 _120521 B x op f).
Proof. exact (MK_COMB (@lem5795280 _120521 B x op f) (@lem5795281 _120521 B x op f)). Qed.
Lemma lem5795283 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term923 _120521 B op f) = (term913 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5795282 _120521 B x op f)). Qed.
Lemma lem5795284 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5795285 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term915 _120521 B op f) = (term914 _120521 B op f).
Proof. exact (MK_COMB (@lem5795284 _120521) (@lem5795283 _120521 B op f)). Qed.
Lemma lem5795286 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5795287 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term924 _120521 B op f) = (term925 _120521 B op f).
Proof. exact (MK_COMB (@lem5795286) (@lem5795285 _120521 B op f)). Qed.
Lemma lem5795288 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term919 _120521 B op f x) = (term906 _120521 B x op f).
Proof. exact (eq_refl (term919 _120521 B op f x)). Qed.
Lemma lem5795289 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term926 _120521 B op f) = (term917 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5795288 _120521 B x op f)). Qed.
Lemma lem5795290 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5795291 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term927 _120521 B op f) = (term928 _120521 B op f).
Proof. exact (MK_COMB (@lem5795290 _120521) (@lem5795289 _120521 B op f)). Qed.
Lemma lem5795292 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5795293 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term929 _120521 B op f) = (term930 _120521 B op f).
Proof. exact (MK_COMB (@lem5795292) (@lem5795291 _120521 B op f)). Qed.
Lemma lem5795294 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term921 _120521 B op f x) = (term911 _120521 B x op f).
Proof. exact (eq_refl (term921 _120521 B op f x)). Qed.
Lemma lem5795295 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term931 _120521 B op f) = (term918 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5795294 _120521 B x op f)). Qed.
Lemma lem5795296 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5795297 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term932 _120521 B op f) = (term933 _120521 B op f).
Proof. exact (MK_COMB (@lem5795296 _120521) (@lem5795295 _120521 B op f)). Qed.
Lemma lem5795298 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term916 _120521 B op f) = (term934 _120521 B op f).
Proof. exact (MK_COMB (@lem5795293 _120521 B op f) (@lem5795297 _120521 B op f)). Qed.
Lemma lem5795299 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : ((term915 _120521 B op f) = (term916 _120521 B op f)) = ((term914 _120521 B op f) = (term934 _120521 B op f)).
Proof. exact (MK_COMB (@lem5795287 _120521 B op f) (@lem5795298 _120521 B op f)). Qed.
Lemma lem5795300 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term914 _120521 B op f) = (term934 _120521 B op f).
Proof. exact (EQ_MP (@lem5795299 _120521 B op f) (@lem5795277 _120521 B op f)). Qed.
Lemma lem5795405 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term884 _120521 B op f) = (term934 _120521 B op f).
Proof. exact (TRANS (@lem5795273 _120521 B op f) (@lem5795300 _120521 B op f)). Qed.
Lemma lem5795406 {_120521 B : Type'} (op : type1400 B) : (term885 _120521 B op) = (term935 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5795405 _120521 B op f)). Qed.
Lemma lem5795407 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5795408 {_120521 B : Type'} (op : type1400 B) : (term886 _120521 B op) = (term936 _120521 B op).
Proof. exact (MK_COMB (@lem5795407 _120521 B) (@lem5795406 _120521 B op)). Qed.
Lemma lem5795410 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5795411 {_120521 B : Type'} (P : type572 _120521 B) (Q : type572 _120521 B) : (term158 _120521 B P Q) = (term159 _120521 B P Q).
Proof. exact (@lem5795410 (_120521 -> B) P Q). Qed.
Lemma lem5795412 {_120521 B : Type'} (op : type1400 B) : (term937 _120521 B op) = (term938 _120521 B op).
Proof. exact (@lem5795411 _120521 B (term939 _120521 B op) (term940 _120521 B op)). Qed.
Lemma lem5795413 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term941 _120521 B op f) = (term928 _120521 B op f).
Proof. exact (eq_refl (term941 _120521 B op f)). Qed.
Lemma lem5795414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5795415 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term942 _120521 B op f) = (term930 _120521 B op f).
Proof. exact (MK_COMB (@lem5795414) (@lem5795413 _120521 B op f)). Qed.
Lemma lem5795416 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term943 _120521 B op f) = (term933 _120521 B op f).
Proof. exact (eq_refl (term943 _120521 B op f)). Qed.
Lemma lem5795417 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term944 _120521 B op f) = (term934 _120521 B op f).
Proof. exact (MK_COMB (@lem5795415 _120521 B op f) (@lem5795416 _120521 B op f)). Qed.
Lemma lem5795418 {_120521 B : Type'} (op : type1400 B) : (term945 _120521 B op) = (term935 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5795417 _120521 B op f)). Qed.
Lemma lem5795419 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5795420 {_120521 B : Type'} (op : type1400 B) : (term937 _120521 B op) = (term936 _120521 B op).
Proof. exact (MK_COMB (@lem5795419 _120521 B) (@lem5795418 _120521 B op)). Qed.
Lemma lem5795421 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5795422 {_120521 B : Type'} (op : type1400 B) : (term946 _120521 B op) = (term947 _120521 B op).
Proof. exact (MK_COMB (@lem5795421) (@lem5795420 _120521 B op)). Qed.
Lemma lem5795423 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term941 _120521 B op f) = (term928 _120521 B op f).
Proof. exact (eq_refl (term941 _120521 B op f)). Qed.
Lemma lem5795424 {_120521 B : Type'} (op : type1400 B) : (term948 _120521 B op) = (term939 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5795423 _120521 B op f)). Qed.
Lemma lem5795425 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5795426 {_120521 B : Type'} (op : type1400 B) : (term949 _120521 B op) = (term950 _120521 B op).
Proof. exact (MK_COMB (@lem5795425 _120521 B) (@lem5795424 _120521 B op)). Qed.
Lemma lem5795427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5795428 {_120521 B : Type'} (op : type1400 B) : (term951 _120521 B op) = (term952 _120521 B op).
Proof. exact (MK_COMB (@lem5795427) (@lem5795426 _120521 B op)). Qed.
Lemma lem5795429 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term943 _120521 B op f) = (term933 _120521 B op f).
Proof. exact (eq_refl (term943 _120521 B op f)). Qed.
Lemma lem5795430 {_120521 B : Type'} (op : type1400 B) : (term953 _120521 B op) = (term940 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5795429 _120521 B op f)). Qed.
Lemma lem5795431 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5795432 {_120521 B : Type'} (op : type1400 B) : (term954 _120521 B op) = (term955 _120521 B op).
Proof. exact (MK_COMB (@lem5795431 _120521 B) (@lem5795430 _120521 B op)). Qed.
Lemma lem5795433 {_120521 B : Type'} (op : type1400 B) : (term938 _120521 B op) = (term956 _120521 B op).
Proof. exact (MK_COMB (@lem5795428 _120521 B op) (@lem5795432 _120521 B op)). Qed.
Lemma lem5795434 {_120521 B : Type'} (op : type1400 B) : ((term937 _120521 B op) = (term938 _120521 B op)) = ((term936 _120521 B op) = (term956 _120521 B op)).
Proof. exact (MK_COMB (@lem5795422 _120521 B op) (@lem5795433 _120521 B op)). Qed.
Lemma lem5795435 {_120521 B : Type'} (op : type1400 B) : (term936 _120521 B op) = (term956 _120521 B op).
Proof. exact (EQ_MP (@lem5795434 _120521 B op) (@lem5795412 _120521 B op)). Qed.
Lemma lem5795548 {_120521 B : Type'} (op : type1400 B) : (term886 _120521 B op) = (term956 _120521 B op).
Proof. exact (TRANS (@lem5795408 _120521 B op) (@lem5795435 _120521 B op)). Qed.
Lemma lem5795549 {A B : Type'} (op : type1400 B) : (term753 A B op) = (term753 A B op).
Proof. exact (eq_refl (term753 A B op)). Qed.
Lemma lem5795550 {_120521 A B : Type'} (op : type1400 B) : (term887 _120521 A B op) = (term957 _120521 A B op).
Proof. exact (MK_COMB (@lem5795549 A B op) (@lem5795548 _120521 B op)). Qed.
Lemma lem5795551 {B : Type'} (op : type1400 B) : (term888 B op) = (term888 B op).
Proof. exact (eq_refl (term888 B op)). Qed.
Lemma lem5795552 {_120521 A B : Type'} (op : type1400 B) : (term890 _120521 A B op) = (term958 _120521 A B op).
Proof. exact (MK_COMB (@lem5795551 B op) (@lem5795550 _120521 A B op)). Qed.
Lemma lem5795553 {_120521 A B : Type'} : (term891 _120521 A B) = (term959 _120521 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5795552 _120521 A B op)). Qed.
Lemma lem5795554 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5795605 {_120521 A B : Type'} : (term892 _120521 A B) = (term960 _120521 A B).
Proof. exact (MK_COMB (@lem5795554 B) (@lem5795553 _120521 A B)). Qed.
Lemma lem5795606 {_120521 A B : Type'} : (term760 _120521 A B) = (term960 _120521 A B).
Proof. exact (TRANS (@lem5795087 _120521 A B) (@lem5795605 _120521 A B)). Qed.
Lemma lem5795607 {_120521 A B : Type'} (h1 : term760 _120521 A B) : term960 _120521 A B.
Proof. exact (EQ_MP (@lem5795606 _120521 A B) (@lem5792156 _120521 A B h1)). Qed.
Lemma lem5796182 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796183 {B : Type'} (f : type403 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> Prop) f x).
Proof. exact (@lem5796182 (type1400 B) Prop f x). Qed.
Lemma lem5796185 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@I ((B -> B -> B) -> Prop) (@monoidal B) op).
Proof. exact (@lem5796183 B (@monoidal B) op). Qed.
Lemma lem5796231 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem5796240 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796241 {A B : Type'} (f : type748 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5796240 (type1400 B) (type527 A B) f x). Qed.
Lemma lem5796242 {A B : Type'} (op : type1400 B) : (@support A B op) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op).
Proof. exact (@lem5796241 A B (@support A B) op). Qed.
Lemma lem5796243 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5796244 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f).
Proof. exact (MK_COMB (@lem5796242 A B op) (@lem5796243 A B f)). Qed.
Lemma lem5796246 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796247 {A B : Type'} (f : type527 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5796246 (A -> B) (type672 A) f x). Qed.
Lemma lem5796248 {A B : Type'} (op : type1400 B) (f : A -> B) : (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f) = (term397 A B op f).
Proof. exact (@lem5796247 A B (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op) f). Qed.
Lemma lem5796249 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (term397 A B op f).
Proof. exact (TRANS (@lem5796244 A B op f) (@lem5796248 A B op f)). Qed.
Lemma lem5796250 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5796251 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term398 A B op f s).
Proof. exact (MK_COMB (@lem5796249 A B op f) (@lem5796250 A s)). Qed.
Lemma lem5796253 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796254 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5796253 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem5796255 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term398 A B op f s) = (term399 A B op f s).
Proof. exact (@lem5796254 A (term397 A B op f) s). Qed.
Lemma lem5796257 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term399 A B op f s).
Proof. exact (TRANS (@lem5796251 A B op f s) (@lem5796255 A B op f s)). Qed.
Lemma lem5796258 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem5796259 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term400 A B op f s) = (term401 A B op f s).
Proof. exact (MK_COMB (@lem5796231 A) (@lem5796257 A B op f s)). Qed.
Lemma lem5796260 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : ((@support A B op f s) = (@EMPTY A)) = ((term399 A B op f s) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem5796259 A B op f s) (@lem5796258 A)). Qed.
Lemma lem5796262 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5796263 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5796272 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796273 {A B : Type'} (f : type750 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5796272 (type1400 B) (type632 A B) f x). Qed.
Lemma lem5796274 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op).
Proof. exact (@lem5796273 A B (@iterate B A) op). Qed.
Lemma lem5796275 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5796276 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (@iterate B A op s) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op s).
Proof. exact (MK_COMB (@lem5796274 A B op) (@lem5796275 A s)). Qed.
Lemma lem5796278 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796279 {A B : Type'} (f : type632 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5796278 (A -> Prop) (type570 A B) f x). Qed.
Lemma lem5796280 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op s) = (term961 A B op s).
Proof. exact (@lem5796279 A B (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) s). Qed.
Lemma lem5796281 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (@iterate B A op s) = (term961 A B op s).
Proof. exact (TRANS (@lem5796276 A B op s) (@lem5796280 A B op s)). Qed.
Lemma lem5796282 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5796283 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term962 A B op s f).
Proof. exact (MK_COMB (@lem5796281 A B op s) (@lem5796282 A B f)). Qed.
Lemma lem5796285 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796286 {A B : Type'} (f : type570 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> B) f x).
Proof. exact (@lem5796285 (A -> B) B f x). Qed.
Lemma lem5796287 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term962 A B op s f) = (term963 A B op s f).
Proof. exact (@lem5796286 A B (term961 A B op s) f). Qed.
Lemma lem5796289 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term963 A B op s f).
Proof. exact (TRANS (@lem5796283 A B op s f) (@lem5796287 A B op s f)). Qed.
Lemma lem5796294 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796295 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5796294 (type1400 B) B f x). Qed.
Lemma lem5796297 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5796295 B (@neutral B) op). Qed.
Lemma lem5796298 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term964 A B op s f) = (term965 A B op s f).
Proof. exact (MK_COMB (@lem5796263 B) (@lem5796289 A B op s f)). Qed.
Lemma lem5796299 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : ((@iterate B A op s f) = (@neutral B op)) = ((term963 A B op s f) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem5796298 A B op s f) (@lem5796297 B op)). Qed.
Lemma lem5796300 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term594 A B s f op) = (term966 A B s f op).
Proof. exact (MK_COMB (@lem5796262) (@lem5796299 A B s f op)). Qed.
Lemma lem5796932 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5796943 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796944 {A B : Type'} (f : type748 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5796943 (type1400 B) (type527 A B) f x). Qed.
Lemma lem5796945 {A B : Type'} (op : type1400 B) : (@support A B op) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op).
Proof. exact (@lem5796944 A B (@support A B) op). Qed.
Lemma lem5796946 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5796947 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f).
Proof. exact (MK_COMB (@lem5796945 A B op) (@lem5796946 A B f)). Qed.
Lemma lem5796949 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796950 {A B : Type'} (f : type527 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5796949 (A -> B) (type672 A) f x). Qed.
Lemma lem5796951 {A B : Type'} (op : type1400 B) (f : A -> B) : (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f) = (term397 A B op f).
Proof. exact (@lem5796950 A B (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op) f). Qed.
Lemma lem5796952 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (term397 A B op f).
Proof. exact (TRANS (@lem5796947 A B op f) (@lem5796951 A B op f)). Qed.
Lemma lem5796953 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5796954 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term398 A B op f s).
Proof. exact (MK_COMB (@lem5796952 A B op f) (@lem5796953 A s)). Qed.
Lemma lem5796956 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796957 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5796956 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem5796958 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term398 A B op f s) = (term399 A B op f s).
Proof. exact (@lem5796957 A (term397 A B op f) s). Qed.
Lemma lem5796960 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term399 A B op f s).
Proof. exact (TRANS (@lem5796954 A B op f s) (@lem5796958 A B op f s)). Qed.
Lemma lem5796961 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5796962 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5796963 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term967 A B op f s) = (term968 A B op f s).
Proof. exact (MK_COMB (@lem5796962 A B op) (@lem5796960 A B op f s)). Qed.
Lemma lem5796964 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term842 A B op s f) = (term969 A B op s f).
Proof. exact (MK_COMB (@lem5796963 A B op f s) (@lem5796961 A B f)). Qed.
Lemma lem5796966 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796967 {A B : Type'} (f : type750 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5796966 (type1400 B) (type632 A B) f x). Qed.
Lemma lem5796968 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op).
Proof. exact (@lem5796967 A B (@iterate B A) op). Qed.
Lemma lem5796969 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term399 A B op f s) = (term399 A B op f s).
Proof. exact (eq_refl (term399 A B op f s)). Qed.
Lemma lem5796970 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term968 A B op f s) = (term970 A B op f s).
Proof. exact (MK_COMB (@lem5796968 A B op) (@lem5796969 A B op f s)). Qed.
Lemma lem5796972 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796973 {A B : Type'} (f : type632 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5796972 (A -> Prop) (type570 A B) f x). Qed.
Lemma lem5796974 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term970 A B op f s) = (term971 A B op f s).
Proof. exact (@lem5796973 A B (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) (term399 A B op f s)). Qed.
Lemma lem5796975 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term968 A B op f s) = (term971 A B op f s).
Proof. exact (TRANS (@lem5796970 A B op f s) (@lem5796974 A B op f s)). Qed.
Lemma lem5796976 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5796977 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term969 A B op s f) = (term972 A B op s f).
Proof. exact (MK_COMB (@lem5796975 A B op f s) (@lem5796976 A B f)). Qed.
Lemma lem5796979 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796980 {A B : Type'} (f : type570 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> B) f x).
Proof. exact (@lem5796979 (A -> B) B f x). Qed.
Lemma lem5796981 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term972 A B op s f) = (term973 A B op s f).
Proof. exact (@lem5796980 A B (term971 A B op f s) f). Qed.
Lemma lem5796982 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term969 A B op s f) = (term973 A B op s f).
Proof. exact (TRANS (@lem5796977 A B op s f) (@lem5796981 A B op s f)). Qed.
Lemma lem5796983 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term842 A B op s f) = (term973 A B op s f).
Proof. exact (TRANS (@lem5796964 A B op s f) (@lem5796982 A B op s f)). Qed.
Lemma lem5796992 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796993 {A B : Type'} (f : type750 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5796992 (type1400 B) (type632 A B) f x). Qed.
Lemma lem5796994 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op).
Proof. exact (@lem5796993 A B (@iterate B A) op). Qed.
Lemma lem5796995 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5796996 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (@iterate B A op s) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op s).
Proof. exact (MK_COMB (@lem5796994 A B op) (@lem5796995 A s)). Qed.
Lemma lem5796998 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5796999 {A B : Type'} (f : type632 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5796998 (A -> Prop) (type570 A B) f x). Qed.
Lemma lem5797000 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op s) = (term961 A B op s).
Proof. exact (@lem5796999 A B (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) s). Qed.
Lemma lem5797001 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (@iterate B A op s) = (term961 A B op s).
Proof. exact (TRANS (@lem5796996 A B op s) (@lem5797000 A B op s)). Qed.
Lemma lem5797002 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5797003 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term962 A B op s f).
Proof. exact (MK_COMB (@lem5797001 A B op s) (@lem5797002 A B f)). Qed.
Lemma lem5797005 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5797006 {A B : Type'} (f : type570 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> B) f x).
Proof. exact (@lem5797005 (A -> B) B f x). Qed.
Lemma lem5797007 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term962 A B op s f) = (term963 A B op s f).
Proof. exact (@lem5797006 A B (term961 A B op s) f). Qed.
Lemma lem5797009 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term963 A B op s f).
Proof. exact (TRANS (@lem5797003 A B op s f) (@lem5797007 A B op s f)). Qed.
Lemma lem5797010 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term974 A B op s f) = (term975 A B op s f).
Proof. exact (MK_COMB (@lem5796932 B) (@lem5796983 A B op s f)). Qed.
Lemma lem5797011 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : ((term842 A B op s f) = (@iterate B A op s f)) = ((term973 A B op s f) = (term963 A B op s f)).
Proof. exact (MK_COMB (@lem5797010 A B op s f) (@lem5797009 A B op s f)). Qed.
Lemma lem5797012 {A B : Type'} (op : type1400 B) (f : A -> B) : (term843 A B op f) = (term976 A B op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5797011 A B op s f)). Qed.
Lemma lem5797013 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5797014 {A B : Type'} (op : type1400 B) (f : A -> B) : (term844 A B op f) = (term977 A B op f).
Proof. exact (MK_COMB (@lem5797013 A) (@lem5797012 A B op f)). Qed.
Lemma lem5797015 {A B : Type'} (op : type1400 B) : (term845 A B op) = (term978 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5797014 A B op f)). Qed.
Lemma lem5797016 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5797017 {A B : Type'} (op : type1400 B) : (term846 A B op) = (term979 A B op).
Proof. exact (MK_COMB (@lem5797016 A B) (@lem5797015 A B op)). Qed.
Lemma lem5797018 {A B : Type'} : (term847 A B) = (term980 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5797017 A B op)). Qed.
Lemma lem5797019 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5797020 {A B : Type'} : (term601 A B) = (term981 A B).
Proof. exact (MK_COMB (@lem5797019 B) (@lem5797018 A B)). Qed.
Lemma lem5797021 {A B : Type'} (h1 : term601 A B) : term981 A B.
Proof. exact (EQ_MP (@lem5797020 A B) (@lem5792454 A B h1)). Qed.
Lemma lem5798709 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5798718 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798719 {_120521 : Type'} (f : type1363 _120521) (x : _120521) : (f x) = (@I (_120521 -> (_120521 -> Prop) -> _120521 -> Prop) f x).
Proof. exact (@lem5798718 _120521 (type672 _120521) f x). Qed.
Lemma lem5798720 {_120521 : Type'} (x : _120521) : (@INSERT _120521 x) = (@I (_120521 -> (_120521 -> Prop) -> _120521 -> Prop) (@INSERT _120521) x).
Proof. exact (@lem5798719 _120521 (@INSERT _120521) x). Qed.
Lemma lem5798721 {_120521 : Type'} (s : _120521 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5798722 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (@INSERT _120521 x s) = (@I (_120521 -> (_120521 -> Prop) -> _120521 -> Prop) (@INSERT _120521) x s).
Proof. exact (MK_COMB (@lem5798720 _120521 x) (@lem5798721 _120521 s)). Qed.
Lemma lem5798724 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798725 {_120521 : Type'} (f : type672 _120521) (x : _120521 -> Prop) : (f x) = (@I ((_120521 -> Prop) -> _120521 -> Prop) f x).
Proof. exact (@lem5798724 (_120521 -> Prop) (_120521 -> Prop) f x). Qed.
Lemma lem5798726 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (@I (_120521 -> (_120521 -> Prop) -> _120521 -> Prop) (@INSERT _120521) x s) = (term982 _120521 x s).
Proof. exact (@lem5798725 _120521 (@I (_120521 -> (_120521 -> Prop) -> _120521 -> Prop) (@INSERT _120521) x) s). Qed.
Lemma lem5798728 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (@INSERT _120521 x s) = (term982 _120521 x s).
Proof. exact (TRANS (@lem5798722 _120521 x s) (@lem5798726 _120521 x s)). Qed.
Lemma lem5798729 {_120521 B : Type'} (f : _120521 -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5798730 {_120521 B : Type'} (op : type1400 B) : (@iterate B _120521 op) = (@iterate B _120521 op).
Proof. exact (eq_refl (@iterate B _120521 op)). Qed.
Lemma lem5798731 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) : (term983 _120521 B op x s) = (term984 _120521 B op x s).
Proof. exact (MK_COMB (@lem5798730 _120521 B op) (@lem5798728 _120521 x s)). Qed.
Lemma lem5798732 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term728 _120521 B op x s f) = (term985 _120521 B op x s f).
Proof. exact (MK_COMB (@lem5798731 _120521 B op x s) (@lem5798729 _120521 B f)). Qed.
Lemma lem5798734 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798735 {_120521 B : Type'} (f : type750 _120521 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) f x).
Proof. exact (@lem5798734 (type1400 B) (type632 _120521 B) f x). Qed.
Lemma lem5798736 {_120521 B : Type'} (op : type1400 B) : (@iterate B _120521 op) = (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) (@iterate B _120521) op).
Proof. exact (@lem5798735 _120521 B (@iterate B _120521) op). Qed.
Lemma lem5798737 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (term982 _120521 x s) = (term982 _120521 x s).
Proof. exact (eq_refl (term982 _120521 x s)). Qed.
Lemma lem5798738 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) : (term984 _120521 B op x s) = (term986 _120521 B op x s).
Proof. exact (MK_COMB (@lem5798736 _120521 B op) (@lem5798737 _120521 x s)). Qed.
Lemma lem5798740 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798741 {_120521 B : Type'} (f : type632 _120521 B) (x : _120521 -> Prop) : (f x) = (@I ((_120521 -> Prop) -> (_120521 -> B) -> B) f x).
Proof. exact (@lem5798740 (_120521 -> Prop) (type570 _120521 B) f x). Qed.
Lemma lem5798742 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) : (term986 _120521 B op x s) = (term987 _120521 B op x s).
Proof. exact (@lem5798741 _120521 B (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) (@iterate B _120521) op) (term982 _120521 x s)). Qed.
Lemma lem5798743 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) : (term984 _120521 B op x s) = (term987 _120521 B op x s).
Proof. exact (TRANS (@lem5798738 _120521 B op x s) (@lem5798742 _120521 B op x s)). Qed.
Lemma lem5798744 {_120521 B : Type'} (f : _120521 -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5798745 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term985 _120521 B op x s f) = (term988 _120521 B op x s f).
Proof. exact (MK_COMB (@lem5798743 _120521 B op x s) (@lem5798744 _120521 B f)). Qed.
Lemma lem5798747 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798748 {_120521 B : Type'} (f : type570 _120521 B) (x : _120521 -> B) : (f x) = (@I ((_120521 -> B) -> B) f x).
Proof. exact (@lem5798747 (_120521 -> B) B f x). Qed.
Lemma lem5798749 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term988 _120521 B op x s f) = (term989 _120521 B op x s f).
Proof. exact (@lem5798748 _120521 B (term987 _120521 B op x s) f). Qed.
Lemma lem5798750 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term985 _120521 B op x s f) = (term989 _120521 B op x s f).
Proof. exact (TRANS (@lem5798745 _120521 B op x s f) (@lem5798749 _120521 B op x s f)). Qed.
Lemma lem5798751 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term728 _120521 B op x s f) = (term989 _120521 B op x s f).
Proof. exact (TRANS (@lem5798732 _120521 B op x s f) (@lem5798750 _120521 B op x s f)). Qed.
Lemma lem5798752 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5798757 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798759 {_120521 B : Type'} (f : _120521 -> B) (x : _120521) : (f x) = (@I (_120521 -> B) f x).
Proof. exact (@lem5798757 _120521 B f x). Qed.
Lemma lem5798768 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798769 {_120521 B : Type'} (f : type750 _120521 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) f x).
Proof. exact (@lem5798768 (type1400 B) (type632 _120521 B) f x). Qed.
Lemma lem5798770 {_120521 B : Type'} (op : type1400 B) : (@iterate B _120521 op) = (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) (@iterate B _120521) op).
Proof. exact (@lem5798769 _120521 B (@iterate B _120521) op). Qed.
Lemma lem5798771 {_120521 : Type'} (s : _120521 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5798772 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) : (@iterate B _120521 op s) = (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) (@iterate B _120521) op s).
Proof. exact (MK_COMB (@lem5798770 _120521 B op) (@lem5798771 _120521 s)). Qed.
Lemma lem5798774 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798775 {_120521 B : Type'} (f : type632 _120521 B) (x : _120521 -> Prop) : (f x) = (@I ((_120521 -> Prop) -> (_120521 -> B) -> B) f x).
Proof. exact (@lem5798774 (_120521 -> Prop) (type570 _120521 B) f x). Qed.
Lemma lem5798776 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) : (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) (@iterate B _120521) op s) = (term961 _120521 B op s).
Proof. exact (@lem5798775 _120521 B (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) (@iterate B _120521) op) s). Qed.
Lemma lem5798777 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) : (@iterate B _120521 op s) = (term961 _120521 B op s).
Proof. exact (TRANS (@lem5798772 _120521 B op s) (@lem5798776 _120521 B op s)). Qed.
Lemma lem5798778 {_120521 B : Type'} (f : _120521 -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5798779 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (@iterate B _120521 op s f) = (term962 _120521 B op s f).
Proof. exact (MK_COMB (@lem5798777 _120521 B op s) (@lem5798778 _120521 B f)). Qed.
Lemma lem5798781 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798782 {_120521 B : Type'} (f : type570 _120521 B) (x : _120521 -> B) : (f x) = (@I ((_120521 -> B) -> B) f x).
Proof. exact (@lem5798781 (_120521 -> B) B f x). Qed.
Lemma lem5798783 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term962 _120521 B op s f) = (term963 _120521 B op s f).
Proof. exact (@lem5798782 _120521 B (term961 _120521 B op s) f). Qed.
Lemma lem5798785 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (@iterate B _120521 op s f) = (term963 _120521 B op s f).
Proof. exact (TRANS (@lem5798779 _120521 B op s f) (@lem5798783 _120521 B op s f)). Qed.
Lemma lem5798786 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) : (term990 _120521 B op f x) = (term991 _120521 B op f x).
Proof. exact (MK_COMB (@lem5798752 B op) (@lem5798759 _120521 B f x)). Qed.
Lemma lem5798787 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term724 _120521 B x op s f) = (term992 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5798786 _120521 B op f x) (@lem5798785 _120521 B op s f)). Qed.
Lemma lem5798789 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798790 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5798789 B (B -> B) f x). Qed.
Lemma lem5798791 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) : (term991 _120521 B op f x) = (term993 _120521 B op f x).
Proof. exact (@lem5798790 B op (@I (_120521 -> B) f x)). Qed.
Lemma lem5798792 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term963 _120521 B op s f) = (term963 _120521 B op s f).
Proof. exact (eq_refl (term963 _120521 B op s f)). Qed.
Lemma lem5798793 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term992 _120521 B x op s f) = (term994 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5798791 _120521 B op f x) (@lem5798792 _120521 B op s f)). Qed.
Lemma lem5798795 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798796 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5798795 B B f x). Qed.
Lemma lem5798797 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term994 _120521 B x op s f) = (term995 _120521 B x op s f).
Proof. exact (@lem5798796 B (term993 _120521 B op f x) (term963 _120521 B op s f)). Qed.
Lemma lem5798798 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term992 _120521 B x op s f) = (term995 _120521 B x op s f).
Proof. exact (TRANS (@lem5798793 _120521 B x op s f) (@lem5798797 _120521 B x op s f)). Qed.
Lemma lem5798799 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term724 _120521 B x op s f) = (term995 _120521 B x op s f).
Proof. exact (TRANS (@lem5798787 _120521 B x op s f) (@lem5798798 _120521 B x op s f)). Qed.
Lemma lem5798800 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term727 _120521 B op x s f) = (term996 _120521 B op x s f).
Proof. exact (MK_COMB (@lem5798709 B) (@lem5798751 _120521 B op x s f)). Qed.
Lemma lem5798801 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : ((term728 _120521 B op x s f) = (term724 _120521 B x op s f)) = ((term989 _120521 B op x s f) = (term995 _120521 B x op s f)).
Proof. exact (MK_COMB (@lem5798800 _120521 B op x s f) (@lem5798799 _120521 B x op s f)). Qed.
Lemma lem5798802 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5798807 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798808 {_120521 : Type'} (f : type686 _120521) (x : _120521 -> Prop) : (f x) = (@I ((_120521 -> Prop) -> Prop) f x).
Proof. exact (@lem5798807 (_120521 -> Prop) Prop f x). Qed.
Lemma lem5798810 {_120521 : Type'} (s : _120521 -> Prop) : (@FINITE _120521 s) = (@I ((_120521 -> Prop) -> Prop) (@FINITE _120521) s).
Proof. exact (@lem5798808 _120521 (@FINITE _120521) s). Qed.
Lemma lem5798811 {_120521 : Type'} (s : _120521 -> Prop) : (term997 _120521 s) = (term998 _120521 s).
Proof. exact (MK_COMB (@lem5798802) (@lem5798810 _120521 s)). Qed.
Lemma lem5798812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5798813 {_120521 : Type'} (s : _120521 -> Prop) : (term999 _120521 s) = (term1000 _120521 s).
Proof. exact (MK_COMB (@lem5798812) (@lem5798811 _120521 s)). Qed.
Lemma lem5798814 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term875 _120521 B x op s f) = (term1001 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5798813 _120521 s) (@lem5798801 _120521 B x op s f)). Qed.
Lemma lem5798821 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798822 {_120521 : Type'} (f : type1364 _120521) (x : _120521) : (f x) = (@I (_120521 -> (_120521 -> Prop) -> Prop) f x).
Proof. exact (@lem5798821 _120521 (type686 _120521) f x). Qed.
Lemma lem5798823 {_120521 : Type'} (x : _120521) : (@IN _120521 x) = (@I (_120521 -> (_120521 -> Prop) -> Prop) (@IN _120521) x).
Proof. exact (@lem5798822 _120521 (@IN _120521) x). Qed.
Lemma lem5798824 {_120521 : Type'} (s : _120521 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5798825 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (@IN _120521 x s) = (@I (_120521 -> (_120521 -> Prop) -> Prop) (@IN _120521) x s).
Proof. exact (MK_COMB (@lem5798823 _120521 x) (@lem5798824 _120521 s)). Qed.
Lemma lem5798827 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798828 {_120521 : Type'} (f : type686 _120521) (x : _120521 -> Prop) : (f x) = (@I ((_120521 -> Prop) -> Prop) f x).
Proof. exact (@lem5798827 (_120521 -> Prop) Prop f x). Qed.
Lemma lem5798829 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (@I (_120521 -> (_120521 -> Prop) -> Prop) (@IN _120521) x s) = (term390 _120521 x s).
Proof. exact (@lem5798828 _120521 (@I (_120521 -> (_120521 -> Prop) -> Prop) (@IN _120521) x) s). Qed.
Lemma lem5798831 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (@IN _120521 x s) = (term390 _120521 x s).
Proof. exact (TRANS (@lem5798825 _120521 x s) (@lem5798829 _120521 x s)). Qed.
Lemma lem5798832 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5798833 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (term442 _120521 x s) = (term443 _120521 x s).
Proof. exact (MK_COMB (@lem5798832) (@lem5798831 _120521 x s)). Qed.
Lemma lem5798834 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term877 _120521 B x op s f) = (term1002 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5798833 _120521 x s) (@lem5798814 _120521 B x op s f)). Qed.
Lemma lem5798835 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term896 _120521 B x op f) = (term1003 _120521 B x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5798834 _120521 B x op s f)). Qed.
Lemma lem5798836 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5798837 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term911 _120521 B x op f) = (term1004 _120521 B x op f).
Proof. exact (MK_COMB (@lem5798836 _120521) (@lem5798835 _120521 B x op f)). Qed.
Lemma lem5798838 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term918 _120521 B op f) = (term1005 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5798837 _120521 B x op f)). Qed.
Lemma lem5798839 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5798840 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term933 _120521 B op f) = (term1006 _120521 B op f).
Proof. exact (MK_COMB (@lem5798839 _120521) (@lem5798838 _120521 B op f)). Qed.
Lemma lem5798841 {_120521 B : Type'} (op : type1400 B) : (term940 _120521 B op) = (term1007 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5798840 _120521 B op f)). Qed.
Lemma lem5798842 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5798843 {_120521 B : Type'} (op : type1400 B) : (term955 _120521 B op) = (term1008 _120521 B op).
Proof. exact (MK_COMB (@lem5798842 _120521 B) (@lem5798841 _120521 B op)). Qed.
Lemma lem5798844 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5798853 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798854 {_120521 : Type'} (f : type1363 _120521) (x : _120521) : (f x) = (@I (_120521 -> (_120521 -> Prop) -> _120521 -> Prop) f x).
Proof. exact (@lem5798853 _120521 (type672 _120521) f x). Qed.
Lemma lem5798855 {_120521 : Type'} (x : _120521) : (@INSERT _120521 x) = (@I (_120521 -> (_120521 -> Prop) -> _120521 -> Prop) (@INSERT _120521) x).
Proof. exact (@lem5798854 _120521 (@INSERT _120521) x). Qed.
Lemma lem5798856 {_120521 : Type'} (s : _120521 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5798857 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (@INSERT _120521 x s) = (@I (_120521 -> (_120521 -> Prop) -> _120521 -> Prop) (@INSERT _120521) x s).
Proof. exact (MK_COMB (@lem5798855 _120521 x) (@lem5798856 _120521 s)). Qed.
Lemma lem5798859 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798860 {_120521 : Type'} (f : type672 _120521) (x : _120521 -> Prop) : (f x) = (@I ((_120521 -> Prop) -> _120521 -> Prop) f x).
Proof. exact (@lem5798859 (_120521 -> Prop) (_120521 -> Prop) f x). Qed.
Lemma lem5798861 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (@I (_120521 -> (_120521 -> Prop) -> _120521 -> Prop) (@INSERT _120521) x s) = (term982 _120521 x s).
Proof. exact (@lem5798860 _120521 (@I (_120521 -> (_120521 -> Prop) -> _120521 -> Prop) (@INSERT _120521) x) s). Qed.
Lemma lem5798863 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (@INSERT _120521 x s) = (term982 _120521 x s).
Proof. exact (TRANS (@lem5798857 _120521 x s) (@lem5798861 _120521 x s)). Qed.
Lemma lem5798864 {_120521 B : Type'} (f : _120521 -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5798865 {_120521 B : Type'} (op : type1400 B) : (@iterate B _120521 op) = (@iterate B _120521 op).
Proof. exact (eq_refl (@iterate B _120521 op)). Qed.
Lemma lem5798866 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) : (term983 _120521 B op x s) = (term984 _120521 B op x s).
Proof. exact (MK_COMB (@lem5798865 _120521 B op) (@lem5798863 _120521 x s)). Qed.
Lemma lem5798867 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term728 _120521 B op x s f) = (term985 _120521 B op x s f).
Proof. exact (MK_COMB (@lem5798866 _120521 B op x s) (@lem5798864 _120521 B f)). Qed.
Lemma lem5798869 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798870 {_120521 B : Type'} (f : type750 _120521 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) f x).
Proof. exact (@lem5798869 (type1400 B) (type632 _120521 B) f x). Qed.
Lemma lem5798871 {_120521 B : Type'} (op : type1400 B) : (@iterate B _120521 op) = (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) (@iterate B _120521) op).
Proof. exact (@lem5798870 _120521 B (@iterate B _120521) op). Qed.
Lemma lem5798872 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (term982 _120521 x s) = (term982 _120521 x s).
Proof. exact (eq_refl (term982 _120521 x s)). Qed.
Lemma lem5798873 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) : (term984 _120521 B op x s) = (term986 _120521 B op x s).
Proof. exact (MK_COMB (@lem5798871 _120521 B op) (@lem5798872 _120521 x s)). Qed.
Lemma lem5798875 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798876 {_120521 B : Type'} (f : type632 _120521 B) (x : _120521 -> Prop) : (f x) = (@I ((_120521 -> Prop) -> (_120521 -> B) -> B) f x).
Proof. exact (@lem5798875 (_120521 -> Prop) (type570 _120521 B) f x). Qed.
Lemma lem5798877 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) : (term986 _120521 B op x s) = (term987 _120521 B op x s).
Proof. exact (@lem5798876 _120521 B (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) (@iterate B _120521) op) (term982 _120521 x s)). Qed.
Lemma lem5798878 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) : (term984 _120521 B op x s) = (term987 _120521 B op x s).
Proof. exact (TRANS (@lem5798873 _120521 B op x s) (@lem5798877 _120521 B op x s)). Qed.
Lemma lem5798879 {_120521 B : Type'} (f : _120521 -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5798880 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term985 _120521 B op x s f) = (term988 _120521 B op x s f).
Proof. exact (MK_COMB (@lem5798878 _120521 B op x s) (@lem5798879 _120521 B f)). Qed.
Lemma lem5798882 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798883 {_120521 B : Type'} (f : type570 _120521 B) (x : _120521 -> B) : (f x) = (@I ((_120521 -> B) -> B) f x).
Proof. exact (@lem5798882 (_120521 -> B) B f x). Qed.
Lemma lem5798884 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term988 _120521 B op x s f) = (term989 _120521 B op x s f).
Proof. exact (@lem5798883 _120521 B (term987 _120521 B op x s) f). Qed.
Lemma lem5798885 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term985 _120521 B op x s f) = (term989 _120521 B op x s f).
Proof. exact (TRANS (@lem5798880 _120521 B op x s f) (@lem5798884 _120521 B op x s f)). Qed.
Lemma lem5798886 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term728 _120521 B op x s f) = (term989 _120521 B op x s f).
Proof. exact (TRANS (@lem5798867 _120521 B op x s f) (@lem5798885 _120521 B op x s f)). Qed.
Lemma lem5798895 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798896 {_120521 B : Type'} (f : type750 _120521 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) f x).
Proof. exact (@lem5798895 (type1400 B) (type632 _120521 B) f x). Qed.
Lemma lem5798897 {_120521 B : Type'} (op : type1400 B) : (@iterate B _120521 op) = (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) (@iterate B _120521) op).
Proof. exact (@lem5798896 _120521 B (@iterate B _120521) op). Qed.
Lemma lem5798898 {_120521 : Type'} (s : _120521 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5798899 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) : (@iterate B _120521 op s) = (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) (@iterate B _120521) op s).
Proof. exact (MK_COMB (@lem5798897 _120521 B op) (@lem5798898 _120521 s)). Qed.
Lemma lem5798901 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798902 {_120521 B : Type'} (f : type632 _120521 B) (x : _120521 -> Prop) : (f x) = (@I ((_120521 -> Prop) -> (_120521 -> B) -> B) f x).
Proof. exact (@lem5798901 (_120521 -> Prop) (type570 _120521 B) f x). Qed.
Lemma lem5798903 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) : (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) (@iterate B _120521) op s) = (term961 _120521 B op s).
Proof. exact (@lem5798902 _120521 B (@I ((B -> B -> B) -> (_120521 -> Prop) -> (_120521 -> B) -> B) (@iterate B _120521) op) s). Qed.
Lemma lem5798904 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) : (@iterate B _120521 op s) = (term961 _120521 B op s).
Proof. exact (TRANS (@lem5798899 _120521 B op s) (@lem5798903 _120521 B op s)). Qed.
Lemma lem5798905 {_120521 B : Type'} (f : _120521 -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5798906 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (@iterate B _120521 op s f) = (term962 _120521 B op s f).
Proof. exact (MK_COMB (@lem5798904 _120521 B op s) (@lem5798905 _120521 B f)). Qed.
Lemma lem5798908 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798909 {_120521 B : Type'} (f : type570 _120521 B) (x : _120521 -> B) : (f x) = (@I ((_120521 -> B) -> B) f x).
Proof. exact (@lem5798908 (_120521 -> B) B f x). Qed.
Lemma lem5798910 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term962 _120521 B op s f) = (term963 _120521 B op s f).
Proof. exact (@lem5798909 _120521 B (term961 _120521 B op s) f). Qed.
Lemma lem5798912 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (@iterate B _120521 op s f) = (term963 _120521 B op s f).
Proof. exact (TRANS (@lem5798906 _120521 B op s f) (@lem5798910 _120521 B op s f)). Qed.
Lemma lem5798913 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term727 _120521 B op x s f) = (term996 _120521 B op x s f).
Proof. exact (MK_COMB (@lem5798844 B) (@lem5798886 _120521 B op x s f)). Qed.
Lemma lem5798914 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : ((term728 _120521 B op x s f) = (@iterate B _120521 op s f)) = ((term989 _120521 B op x s f) = (term963 _120521 B op s f)).
Proof. exact (MK_COMB (@lem5798913 _120521 B op x s f) (@lem5798912 _120521 B op s f)). Qed.
Lemma lem5798915 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5798920 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798921 {_120521 : Type'} (f : type686 _120521) (x : _120521 -> Prop) : (f x) = (@I ((_120521 -> Prop) -> Prop) f x).
Proof. exact (@lem5798920 (_120521 -> Prop) Prop f x). Qed.
Lemma lem5798923 {_120521 : Type'} (s : _120521 -> Prop) : (@FINITE _120521 s) = (@I ((_120521 -> Prop) -> Prop) (@FINITE _120521) s).
Proof. exact (@lem5798921 _120521 (@FINITE _120521) s). Qed.
Lemma lem5798924 {_120521 : Type'} (s : _120521 -> Prop) : (term997 _120521 s) = (term998 _120521 s).
Proof. exact (MK_COMB (@lem5798915) (@lem5798923 _120521 s)). Qed.
Lemma lem5798925 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5798926 {_120521 : Type'} (s : _120521 -> Prop) : (term999 _120521 s) = (term1000 _120521 s).
Proof. exact (MK_COMB (@lem5798925) (@lem5798924 _120521 s)). Qed.
Lemma lem5798927 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term872 _120521 B x op s f) = (term1009 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5798926 _120521 s) (@lem5798914 _120521 B x op s f)). Qed.
Lemma lem5798928 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5798935 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798936 {_120521 : Type'} (f : type1364 _120521) (x : _120521) : (f x) = (@I (_120521 -> (_120521 -> Prop) -> Prop) f x).
Proof. exact (@lem5798935 _120521 (type686 _120521) f x). Qed.
Lemma lem5798937 {_120521 : Type'} (x : _120521) : (@IN _120521 x) = (@I (_120521 -> (_120521 -> Prop) -> Prop) (@IN _120521) x).
Proof. exact (@lem5798936 _120521 (@IN _120521) x). Qed.
Lemma lem5798938 {_120521 : Type'} (s : _120521 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5798939 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (@IN _120521 x s) = (@I (_120521 -> (_120521 -> Prop) -> Prop) (@IN _120521) x s).
Proof. exact (MK_COMB (@lem5798937 _120521 x) (@lem5798938 _120521 s)). Qed.
Lemma lem5798941 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798942 {_120521 : Type'} (f : type686 _120521) (x : _120521 -> Prop) : (f x) = (@I ((_120521 -> Prop) -> Prop) f x).
Proof. exact (@lem5798941 (_120521 -> Prop) Prop f x). Qed.
Lemma lem5798943 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (@I (_120521 -> (_120521 -> Prop) -> Prop) (@IN _120521) x s) = (term390 _120521 x s).
Proof. exact (@lem5798942 _120521 (@I (_120521 -> (_120521 -> Prop) -> Prop) (@IN _120521) x) s). Qed.
Lemma lem5798945 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (@IN _120521 x s) = (term390 _120521 x s).
Proof. exact (TRANS (@lem5798939 _120521 x s) (@lem5798943 _120521 x s)). Qed.
Lemma lem5798946 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (term391 _120521 x s) = (term392 _120521 x s).
Proof. exact (MK_COMB (@lem5798928) (@lem5798945 _120521 x s)). Qed.
Lemma lem5798947 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5798948 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (term90 _120521 x s) = (term393 _120521 x s).
Proof. exact (MK_COMB (@lem5798947) (@lem5798946 _120521 x s)). Qed.
Lemma lem5798949 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term874 _120521 B x op s f) = (term1010 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5798948 _120521 x s) (@lem5798927 _120521 B x op s f)). Qed.
Lemma lem5798950 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term895 _120521 B x op f) = (term1011 _120521 B x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5798949 _120521 B x op s f)). Qed.
Lemma lem5798951 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5798952 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term906 _120521 B x op f) = (term1012 _120521 B x op f).
Proof. exact (MK_COMB (@lem5798951 _120521) (@lem5798950 _120521 B x op f)). Qed.
Lemma lem5798953 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term917 _120521 B op f) = (term1013 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5798952 _120521 B x op f)). Qed.
Lemma lem5798954 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5798955 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term928 _120521 B op f) = (term1014 _120521 B op f).
Proof. exact (MK_COMB (@lem5798954 _120521) (@lem5798953 _120521 B op f)). Qed.
Lemma lem5798956 {_120521 B : Type'} (op : type1400 B) : (term939 _120521 B op) = (term1015 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5798955 _120521 B op f)). Qed.
Lemma lem5798957 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5798958 {_120521 B : Type'} (op : type1400 B) : (term950 _120521 B op) = (term1016 _120521 B op).
Proof. exact (MK_COMB (@lem5798957 _120521 B) (@lem5798956 _120521 B op)). Qed.
Lemma lem5798959 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5798960 {_120521 B : Type'} (op : type1400 B) : (term952 _120521 B op) = (term1017 _120521 B op).
Proof. exact (MK_COMB (@lem5798959) (@lem5798958 _120521 B op)). Qed.
Lemma lem5798961 {_120521 B : Type'} (op : type1400 B) : (term956 _120521 B op) = (term1018 _120521 B op).
Proof. exact (MK_COMB (@lem5798960 _120521 B op) (@lem5798843 _120521 B op)). Qed.
Lemma lem5798962 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5798971 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798972 {A B : Type'} (f : type750 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5798971 (type1400 B) (type632 A B) f x). Qed.
Lemma lem5798973 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op).
Proof. exact (@lem5798972 A B (@iterate B A) op). Qed.
Lemma lem5798974 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem5798975 {A B : Type'} (op : type1400 B) : (@iterate B A op (@EMPTY A)) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op (@EMPTY A)).
Proof. exact (MK_COMB (@lem5798973 A B op) (@lem5798974 A)). Qed.
Lemma lem5798977 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798978 {A B : Type'} (f : type632 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5798977 (A -> Prop) (type570 A B) f x). Qed.
Lemma lem5798979 {A B : Type'} (op : type1400 B) : (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op (@EMPTY A)) = (term1019 A B op).
Proof. exact (@lem5798978 A B (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) (@EMPTY A)). Qed.
Lemma lem5798980 {A B : Type'} (op : type1400 B) : (@iterate B A op (@EMPTY A)) = (term1019 A B op).
Proof. exact (TRANS (@lem5798975 A B op) (@lem5798979 A B op)). Qed.
Lemma lem5798981 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5798982 {A B : Type'} (op : type1400 B) (f : A -> B) : (@iterate B A op (@EMPTY A) f) = (term1020 A B op f).
Proof. exact (MK_COMB (@lem5798980 A B op) (@lem5798981 A B f)). Qed.
Lemma lem5798984 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798985 {A B : Type'} (f : type570 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> B) f x).
Proof. exact (@lem5798984 (A -> B) B f x). Qed.
Lemma lem5798986 {A B : Type'} (op : type1400 B) (f : A -> B) : (term1020 A B op f) = (term1021 A B op f).
Proof. exact (@lem5798985 A B (term1019 A B op) f). Qed.
Lemma lem5798988 {A B : Type'} (op : type1400 B) (f : A -> B) : (@iterate B A op (@EMPTY A) f) = (term1021 A B op f).
Proof. exact (TRANS (@lem5798982 A B op f) (@lem5798986 A B op f)). Qed.
Lemma lem5798993 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5798994 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5798993 (type1400 B) B f x). Qed.
Lemma lem5798996 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5798994 B (@neutral B) op). Qed.
Lemma lem5798997 {A B : Type'} (op : type1400 B) (f : A -> B) : (term1022 A B op f) = (term1023 A B op f).
Proof. exact (MK_COMB (@lem5798962 B) (@lem5798988 A B op f)). Qed.
Lemma lem5798998 {A B : Type'} (f : A -> B) (op : type1400 B) : ((@iterate B A op (@EMPTY A) f) = (@neutral B op)) = ((term1021 A B op f) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem5798997 A B op f) (@lem5798996 B op)). Qed.
Lemma lem5798999 {A B : Type'} (op : type1400 B) : (term751 A B op) = (term1024 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5798998 A B f op)). Qed.
Lemma lem5799000 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5799001 {A B : Type'} (op : type1400 B) : (term752 A B op) = (term1025 A B op).
Proof. exact (MK_COMB (@lem5799000 A B) (@lem5798999 A B op)). Qed.
Lemma lem5799002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5799003 {A B : Type'} (op : type1400 B) : (term753 A B op) = (term1026 A B op).
Proof. exact (MK_COMB (@lem5799002) (@lem5799001 A B op)). Qed.
Lemma lem5799004 {_120521 A B : Type'} (op : type1400 B) : (term957 _120521 A B op) = (term1027 _120521 A B op).
Proof. exact (MK_COMB (@lem5799003 A B op) (@lem5798961 _120521 B op)). Qed.
Lemma lem5799005 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5799010 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5799011 {B : Type'} (f : type403 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> Prop) f x).
Proof. exact (@lem5799010 (type1400 B) Prop f x). Qed.
Lemma lem5799013 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@I ((B -> B -> B) -> Prop) (@monoidal B) op).
Proof. exact (@lem5799011 B (@monoidal B) op). Qed.
Lemma lem5799014 {B : Type'} (op : type1400 B) : (term1028 B op) = (term1029 B op).
Proof. exact (MK_COMB (@lem5799005) (@lem5799013 B op)). Qed.
Lemma lem5799015 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5799016 {B : Type'} (op : type1400 B) : (term888 B op) = (term1030 B op).
Proof. exact (MK_COMB (@lem5799015) (@lem5799014 B op)). Qed.
Lemma lem5799017 {_120521 A B : Type'} (op : type1400 B) : (term958 _120521 A B op) = (term1031 _120521 A B op).
Proof. exact (MK_COMB (@lem5799016 B op) (@lem5799004 _120521 A B op)). Qed.
Lemma lem5799018 {_120521 A B : Type'} : (term959 _120521 A B) = (term1032 _120521 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5799017 _120521 A B op)). Qed.
Lemma lem5799019 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5799020 {_120521 A B : Type'} : (term960 _120521 A B) = (term1033 _120521 A B).
Proof. exact (MK_COMB (@lem5799019 B) (@lem5799018 _120521 A B)). Qed.
Lemma lem5799021 {_120521 A B : Type'} (h1 : term760 _120521 A B) : term1033 _120521 A B.
Proof. exact (EQ_MP (@lem5799020 _120521 A B) (@lem5795607 _120521 A B h1)). Qed.
Lemma lem5799458 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : ((term973 A B op s f) = (term963 A B op s f)) = ((term973 A B op s f) = (term963 A B op s f)).
Proof. exact (eq_refl ((term973 A B op s f) = (term963 A B op s f))). Qed.
Lemma lem5799459 {A B : Type'} (op : type1400 B) (f : A -> B) : (term976 A B op f) = (term976 A B op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5799458 A B op s f)). Qed.
Lemma lem5799460 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5799461 {A B : Type'} (op : type1400 B) (f : A -> B) : (term977 A B op f) = (term977 A B op f).
Proof. exact (MK_COMB (@lem5799460 A) (@lem5799459 A B op f)). Qed.
Lemma lem5799462 {A B : Type'} (op : type1400 B) : (term978 A B op) = (term978 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5799461 A B op f)). Qed.
Lemma lem5799463 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5799464 {A B : Type'} (op : type1400 B) : (term979 A B op) = (term979 A B op).
Proof. exact (MK_COMB (@lem5799463 A B) (@lem5799462 A B op)). Qed.
Lemma lem5799465 {A B : Type'} : (term980 A B) = (term980 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5799464 A B op)). Qed.
Lemma lem5799466 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5799468 {A B : Type'} : (term981 A B) = (term981 A B).
Proof. exact (MK_COMB (@lem5799466 B) (@lem5799465 A B)). Qed.
Lemma lem5799469 {A B : Type'} (h1 : term601 A B) : term981 A B.
Proof. exact (EQ_MP (@lem5799468 A B) (@lem5797021 A B h1)). Qed.
Lemma lem5800934 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term111 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5800935 {_120521 B : Type'} (P : type572 _120521 B) (Q : type572 _120521 B) : (term159 _120521 B P Q) = (term158 _120521 B P Q).
Proof. exact (@lem5800934 (_120521 -> B) P Q). Qed.
Lemma lem5800936 {_120521 B : Type'} (op : type1400 B) : (term1034 _120521 B op) = (term1035 _120521 B op).
Proof. exact (@lem5800935 _120521 B (term1015 _120521 B op) (term1007 _120521 B op)). Qed.
Lemma lem5800937 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1036 _120521 B op f) = (term1014 _120521 B op f).
Proof. exact (eq_refl (term1036 _120521 B op f)). Qed.
Lemma lem5800938 {_120521 B : Type'} (op : type1400 B) : (term1037 _120521 B op) = (term1015 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5800937 _120521 B op f)). Qed.
Lemma lem5800939 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5800940 {_120521 B : Type'} (op : type1400 B) : (term1038 _120521 B op) = (term1016 _120521 B op).
Proof. exact (MK_COMB (@lem5800939 _120521 B) (@lem5800938 _120521 B op)). Qed.
Lemma lem5800941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5800942 {_120521 B : Type'} (op : type1400 B) : (term1039 _120521 B op) = (term1017 _120521 B op).
Proof. exact (MK_COMB (@lem5800941) (@lem5800940 _120521 B op)). Qed.
Lemma lem5800943 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1040 _120521 B op f) = (term1006 _120521 B op f).
Proof. exact (eq_refl (term1040 _120521 B op f)). Qed.
Lemma lem5800944 {_120521 B : Type'} (op : type1400 B) : (term1041 _120521 B op) = (term1007 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5800943 _120521 B op f)). Qed.
Lemma lem5800945 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5800946 {_120521 B : Type'} (op : type1400 B) : (term1042 _120521 B op) = (term1008 _120521 B op).
Proof. exact (MK_COMB (@lem5800945 _120521 B) (@lem5800944 _120521 B op)). Qed.
Lemma lem5800947 {_120521 B : Type'} (op : type1400 B) : (term1034 _120521 B op) = (term1018 _120521 B op).
Proof. exact (MK_COMB (@lem5800942 _120521 B op) (@lem5800946 _120521 B op)). Qed.
Lemma lem5800948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5800949 {_120521 B : Type'} (op : type1400 B) : (term1043 _120521 B op) = (term1044 _120521 B op).
Proof. exact (MK_COMB (@lem5800948) (@lem5800947 _120521 B op)). Qed.
Lemma lem5800950 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1036 _120521 B op f) = (term1014 _120521 B op f).
Proof. exact (eq_refl (term1036 _120521 B op f)). Qed.
Lemma lem5800951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5800952 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1045 _120521 B op f) = (term1046 _120521 B op f).
Proof. exact (MK_COMB (@lem5800951) (@lem5800950 _120521 B op f)). Qed.
Lemma lem5800953 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1040 _120521 B op f) = (term1006 _120521 B op f).
Proof. exact (eq_refl (term1040 _120521 B op f)). Qed.
Lemma lem5800954 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1047 _120521 B op f) = (term1048 _120521 B op f).
Proof. exact (MK_COMB (@lem5800952 _120521 B op f) (@lem5800953 _120521 B op f)). Qed.
Lemma lem5800955 {_120521 B : Type'} (op : type1400 B) : (term1049 _120521 B op) = (term1050 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5800954 _120521 B op f)). Qed.
Lemma lem5800956 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5800957 {_120521 B : Type'} (op : type1400 B) : (term1035 _120521 B op) = (term1051 _120521 B op).
Proof. exact (MK_COMB (@lem5800956 _120521 B) (@lem5800955 _120521 B op)). Qed.
Lemma lem5800958 {_120521 B : Type'} (op : type1400 B) : ((term1034 _120521 B op) = (term1035 _120521 B op)) = ((term1018 _120521 B op) = (term1051 _120521 B op)).
Proof. exact (MK_COMB (@lem5800949 _120521 B op) (@lem5800957 _120521 B op)). Qed.
Lemma lem5800959 {_120521 B : Type'} (op : type1400 B) : (term1018 _120521 B op) = (term1051 _120521 B op).
Proof. exact (EQ_MP (@lem5800958 _120521 B op) (@lem5800936 _120521 B op)). Qed.
Lemma lem5800961 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term111 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5800962 {_120521 : Type'} (P : _120521 -> Prop) (Q : _120521 -> Prop) : (term111 _120521 P Q) = (term110 _120521 P Q).
Proof. exact (@lem5800961 _120521 P Q). Qed.
Lemma lem5800963 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1052 _120521 B op f) = (term1053 _120521 B op f).
Proof. exact (@lem5800962 _120521 (term1013 _120521 B op f) (term1005 _120521 B op f)). Qed.
Lemma lem5800964 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1054 _120521 B op f x) = (term1012 _120521 B x op f).
Proof. exact (eq_refl (term1054 _120521 B op f x)). Qed.
Lemma lem5800965 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1055 _120521 B op f) = (term1013 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5800964 _120521 B x op f)). Qed.
Lemma lem5800966 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5800967 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1056 _120521 B op f) = (term1014 _120521 B op f).
Proof. exact (MK_COMB (@lem5800966 _120521) (@lem5800965 _120521 B op f)). Qed.
Lemma lem5800968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5800969 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1057 _120521 B op f) = (term1046 _120521 B op f).
Proof. exact (MK_COMB (@lem5800968) (@lem5800967 _120521 B op f)). Qed.
Lemma lem5800970 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1058 _120521 B op f x) = (term1004 _120521 B x op f).
Proof. exact (eq_refl (term1058 _120521 B op f x)). Qed.
Lemma lem5800971 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1059 _120521 B op f) = (term1005 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5800970 _120521 B x op f)). Qed.
Lemma lem5800972 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5800973 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1060 _120521 B op f) = (term1006 _120521 B op f).
Proof. exact (MK_COMB (@lem5800972 _120521) (@lem5800971 _120521 B op f)). Qed.
Lemma lem5800974 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1052 _120521 B op f) = (term1048 _120521 B op f).
Proof. exact (MK_COMB (@lem5800969 _120521 B op f) (@lem5800973 _120521 B op f)). Qed.
Lemma lem5800975 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5800976 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1061 _120521 B op f) = (term1062 _120521 B op f).
Proof. exact (MK_COMB (@lem5800975) (@lem5800974 _120521 B op f)). Qed.
Lemma lem5800977 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1054 _120521 B op f x) = (term1012 _120521 B x op f).
Proof. exact (eq_refl (term1054 _120521 B op f x)). Qed.
Lemma lem5800978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5800979 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1063 _120521 B op f x) = (term1064 _120521 B x op f).
Proof. exact (MK_COMB (@lem5800978) (@lem5800977 _120521 B x op f)). Qed.
Lemma lem5800980 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1058 _120521 B op f x) = (term1004 _120521 B x op f).
Proof. exact (eq_refl (term1058 _120521 B op f x)). Qed.
Lemma lem5800981 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1065 _120521 B op f x) = (term1066 _120521 B x op f).
Proof. exact (MK_COMB (@lem5800979 _120521 B x op f) (@lem5800980 _120521 B x op f)). Qed.
Lemma lem5800982 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1067 _120521 B op f) = (term1068 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5800981 _120521 B x op f)). Qed.
Lemma lem5800983 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5800984 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1053 _120521 B op f) = (term1069 _120521 B op f).
Proof. exact (MK_COMB (@lem5800983 _120521) (@lem5800982 _120521 B op f)). Qed.
Lemma lem5800985 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : ((term1052 _120521 B op f) = (term1053 _120521 B op f)) = ((term1048 _120521 B op f) = (term1069 _120521 B op f)).
Proof. exact (MK_COMB (@lem5800976 _120521 B op f) (@lem5800984 _120521 B op f)). Qed.
Lemma lem5800986 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1048 _120521 B op f) = (term1069 _120521 B op f).
Proof. exact (EQ_MP (@lem5800985 _120521 B op f) (@lem5800963 _120521 B op f)). Qed.
Lemma lem5800988 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term111 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5800989 {_120521 : Type'} (P : type686 _120521) (Q : type686 _120521) : (term113 _120521 P Q) = (term112 _120521 P Q).
Proof. exact (@lem5800988 (_120521 -> Prop) P Q). Qed.
Lemma lem5800990 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1070 _120521 B x op f) = (term1071 _120521 B x op f).
Proof. exact (@lem5800989 _120521 (term1011 _120521 B x op f) (term1003 _120521 B x op f)). Qed.
Lemma lem5800991 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term1072 _120521 B x op f s) = (term1010 _120521 B x op s f).
Proof. exact (eq_refl (term1072 _120521 B x op f s)). Qed.
Lemma lem5800992 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1073 _120521 B x op f) = (term1011 _120521 B x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5800991 _120521 B x op s f)). Qed.
Lemma lem5800993 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5800994 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1074 _120521 B x op f) = (term1012 _120521 B x op f).
Proof. exact (MK_COMB (@lem5800993 _120521) (@lem5800992 _120521 B x op f)). Qed.
Lemma lem5800995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5800996 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1075 _120521 B x op f) = (term1064 _120521 B x op f).
Proof. exact (MK_COMB (@lem5800995) (@lem5800994 _120521 B x op f)). Qed.
Lemma lem5800997 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term1076 _120521 B x op f s) = (term1002 _120521 B x op s f).
Proof. exact (eq_refl (term1076 _120521 B x op f s)). Qed.
Lemma lem5800998 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1077 _120521 B x op f) = (term1003 _120521 B x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5800997 _120521 B x op s f)). Qed.
Lemma lem5800999 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5801000 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1078 _120521 B x op f) = (term1004 _120521 B x op f).
Proof. exact (MK_COMB (@lem5800999 _120521) (@lem5800998 _120521 B x op f)). Qed.
Lemma lem5801001 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1070 _120521 B x op f) = (term1066 _120521 B x op f).
Proof. exact (MK_COMB (@lem5800996 _120521 B x op f) (@lem5801000 _120521 B x op f)). Qed.
Lemma lem5801002 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5801003 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1079 _120521 B x op f) = (term1080 _120521 B x op f).
Proof. exact (MK_COMB (@lem5801002) (@lem5801001 _120521 B x op f)). Qed.
Lemma lem5801004 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term1072 _120521 B x op f s) = (term1010 _120521 B x op s f).
Proof. exact (eq_refl (term1072 _120521 B x op f s)). Qed.
Lemma lem5801005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5801006 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term1081 _120521 B x op f s) = (term1082 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5801005) (@lem5801004 _120521 B x op s f)). Qed.
Lemma lem5801007 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term1076 _120521 B x op f s) = (term1002 _120521 B x op s f).
Proof. exact (eq_refl (term1076 _120521 B x op f s)). Qed.
Lemma lem5801008 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term1083 _120521 B x op f s) = (term1084 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5801006 _120521 B x op s f) (@lem5801007 _120521 B x op s f)). Qed.
Lemma lem5801009 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1085 _120521 B x op f) = (term1086 _120521 B x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5801008 _120521 B x op s f)). Qed.
Lemma lem5801010 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5801011 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1071 _120521 B x op f) = (term1087 _120521 B x op f).
Proof. exact (MK_COMB (@lem5801010 _120521) (@lem5801009 _120521 B x op f)). Qed.
Lemma lem5801012 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : ((term1070 _120521 B x op f) = (term1071 _120521 B x op f)) = ((term1066 _120521 B x op f) = (term1087 _120521 B x op f)).
Proof. exact (MK_COMB (@lem5801003 _120521 B x op f) (@lem5801011 _120521 B x op f)). Qed.
Lemma lem5801013 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1066 _120521 B x op f) = (term1087 _120521 B x op f).
Proof. exact (EQ_MP (@lem5801012 _120521 B x op f) (@lem5800990 _120521 B x op f)). Qed.
Lemma lem5801014 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1068 _120521 B op f) = (term1088 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5801013 _120521 B x op f)). Qed.
Lemma lem5801015 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5801016 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1069 _120521 B op f) = (term1089 _120521 B op f).
Proof. exact (MK_COMB (@lem5801015 _120521) (@lem5801014 _120521 B op f)). Qed.
Lemma lem5801017 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1048 _120521 B op f) = (term1089 _120521 B op f).
Proof. exact (TRANS (@lem5800986 _120521 B op f) (@lem5801016 _120521 B op f)). Qed.
Lemma lem5801018 {_120521 B : Type'} (op : type1400 B) : (term1050 _120521 B op) = (term1090 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5801017 _120521 B op f)). Qed.
Lemma lem5801019 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5801020 {_120521 B : Type'} (op : type1400 B) : (term1051 _120521 B op) = (term1091 _120521 B op).
Proof. exact (MK_COMB (@lem5801019 _120521 B) (@lem5801018 _120521 B op)). Qed.
Lemma lem5801021 {_120521 B : Type'} (op : type1400 B) : (term1018 _120521 B op) = (term1091 _120521 B op).
Proof. exact (TRANS (@lem5800959 _120521 B op) (@lem5801020 _120521 B op)). Qed.
Lemma lem5801022 {A B : Type'} (op : type1400 B) : (term1026 A B op) = (term1026 A B op).
Proof. exact (eq_refl (term1026 A B op)). Qed.
Lemma lem5801023 {_120521 A B : Type'} (op : type1400 B) : (term1027 _120521 A B op) = (term1092 _120521 A B op).
Proof. exact (MK_COMB (@lem5801022 A B op) (@lem5801021 _120521 B op)). Qed.
Lemma lem5801027 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1093 A P Q) = (term1094 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem5801028 {A B : Type'} (P : type572 A B) (Q : Prop) : (term1095 A B P Q) = (term1096 A B P Q).
Proof. exact (@lem5801027 (A -> B) P Q). Qed.
Lemma lem5801029 {_120521 A B : Type'} (op : type1400 B) : (term1097 _120521 A B op) = (term1098 _120521 A B op).
Proof. exact (@lem5801028 A B (term1024 A B op) (term1091 _120521 B op)). Qed.
Lemma lem5801030 {A B : Type'} (f : A -> B) (op : type1400 B) : (term1099 A B op f) = ((term1021 A B op f) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (eq_refl (term1099 A B op f)). Qed.
Lemma lem5801031 {A B : Type'} (op : type1400 B) : (term1100 A B op) = (term1024 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5801030 A B f op)). Qed.
Lemma lem5801032 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5801033 {A B : Type'} (op : type1400 B) : (term1101 A B op) = (term1025 A B op).
Proof. exact (MK_COMB (@lem5801032 A B) (@lem5801031 A B op)). Qed.
Lemma lem5801034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5801035 {A B : Type'} (op : type1400 B) : (term1102 A B op) = (term1026 A B op).
Proof. exact (MK_COMB (@lem5801034) (@lem5801033 A B op)). Qed.
Lemma lem5801036 {_120521 B : Type'} (op : type1400 B) : (term1091 _120521 B op) = (term1091 _120521 B op).
Proof. exact (eq_refl (term1091 _120521 B op)). Qed.
Lemma lem5801037 {_120521 A B : Type'} (op : type1400 B) : (term1097 _120521 A B op) = (term1092 _120521 A B op).
Proof. exact (MK_COMB (@lem5801035 A B op) (@lem5801036 _120521 B op)). Qed.
Lemma lem5801038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5801039 {_120521 A B : Type'} (op : type1400 B) : (term1103 _120521 A B op) = (term1104 _120521 A B op).
Proof. exact (MK_COMB (@lem5801038) (@lem5801037 _120521 A B op)). Qed.
Lemma lem5801040 {A B : Type'} (f : A -> B) (op : type1400 B) : (term1099 A B op f) = ((term1021 A B op f) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (eq_refl (term1099 A B op f)). Qed.
Lemma lem5801041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5801042 {A B : Type'} (f : A -> B) (op : type1400 B) : (term1105 A B op f) = (term1106 A B f op).
Proof. exact (MK_COMB (@lem5801041) (@lem5801040 A B f op)). Qed.
Lemma lem5801043 {_120521 B : Type'} (op : type1400 B) : (term1091 _120521 B op) = (term1091 _120521 B op).
Proof. exact (eq_refl (term1091 _120521 B op)). Qed.
Lemma lem5801044 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1107 _120521 A B f op) = (term1108 _120521 A B f op).
Proof. exact (MK_COMB (@lem5801042 A B f op) (@lem5801043 _120521 B op)). Qed.
Lemma lem5801045 {_120521 A B : Type'} (op : type1400 B) : (term1109 _120521 A B op) = (term1110 _120521 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5801044 _120521 A B f op)). Qed.
Lemma lem5801046 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5801047 {_120521 A B : Type'} (op : type1400 B) : (term1098 _120521 A B op) = (term1111 _120521 A B op).
Proof. exact (MK_COMB (@lem5801046 A B) (@lem5801045 _120521 A B op)). Qed.
Lemma lem5801048 {_120521 A B : Type'} (op : type1400 B) : ((term1097 _120521 A B op) = (term1098 _120521 A B op)) = ((term1092 _120521 A B op) = (term1111 _120521 A B op)).
Proof. exact (MK_COMB (@lem5801039 _120521 A B op) (@lem5801047 _120521 A B op)). Qed.
Lemma lem5801049 {_120521 A B : Type'} (op : type1400 B) : (term1092 _120521 A B op) = (term1111 _120521 A B op).
Proof. exact (EQ_MP (@lem5801048 _120521 A B op) (@lem5801029 _120521 A B op)). Qed.
Lemma lem5801051 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1112 A P Q) = (term1113 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5801052 {_120521 B : Type'} (P : Prop) (Q : type572 _120521 B) : (term1114 _120521 B P Q) = (term1115 _120521 B P Q).
Proof. exact (@lem5801051 (_120521 -> B) P Q). Qed.
Lemma lem5801053 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1116 _120521 A B f op) = (term1117 _120521 A B f op).
Proof. exact (@lem5801052 _120521 B ((term1021 A B op f) = (@I ((B -> B -> B) -> B) (@neutral B) op)) (term1090 _120521 B op)). Qed.
Lemma lem5801054 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1118 _120521 B op f) = (term1089 _120521 B op f).
Proof. exact (eq_refl (term1118 _120521 B op f)). Qed.
Lemma lem5801055 {_120521 B : Type'} (op : type1400 B) : (term1119 _120521 B op) = (term1090 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5801054 _120521 B op f)). Qed.
Lemma lem5801056 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5801057 {_120521 B : Type'} (op : type1400 B) : (term1120 _120521 B op) = (term1091 _120521 B op).
Proof. exact (MK_COMB (@lem5801056 _120521 B) (@lem5801055 _120521 B op)). Qed.
Lemma lem5801058 {A B : Type'} (f : A -> B) (op : type1400 B) : (term1106 A B f op) = (term1106 A B f op).
Proof. exact (eq_refl (term1106 A B f op)). Qed.
Lemma lem5801059 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1116 _120521 A B f op) = (term1108 _120521 A B f op).
Proof. exact (MK_COMB (@lem5801058 A B f op) (@lem5801057 _120521 B op)). Qed.
Lemma lem5801060 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5801061 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1121 _120521 A B f op) = (term1122 _120521 A B f op).
Proof. exact (MK_COMB (@lem5801060) (@lem5801059 _120521 A B f op)). Qed.
Lemma lem5801062 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1118 _120521 B op f) = (term1089 _120521 B op f).
Proof. exact (eq_refl (term1118 _120521 B op f)). Qed.
Lemma lem5801063 {A B : Type'} (f : A -> B) (op : type1400 B) : (term1106 A B f op) = (term1106 A B f op).
Proof. exact (eq_refl (term1106 A B f op)). Qed.
Lemma lem5801064 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1123 _120521 A B f op f') = (term1124 _120521 A B f op f').
Proof. exact (MK_COMB (@lem5801063 A B f op) (@lem5801062 _120521 B op f')). Qed.
Lemma lem5801065 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1125 _120521 A B f op) = (term1126 _120521 A B f op).
Proof. exact (fun_ext (fun f' : _120521 -> B => @lem5801064 _120521 A B f op f')). Qed.
Lemma lem5801066 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5801067 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1117 _120521 A B f op) = (term1127 _120521 A B f op).
Proof. exact (MK_COMB (@lem5801066 _120521 B) (@lem5801065 _120521 A B f op)). Qed.
Lemma lem5801068 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : ((term1116 _120521 A B f op) = (term1117 _120521 A B f op)) = ((term1108 _120521 A B f op) = (term1127 _120521 A B f op)).
Proof. exact (MK_COMB (@lem5801061 _120521 A B f op) (@lem5801067 _120521 A B f op)). Qed.
Lemma lem5801069 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1108 _120521 A B f op) = (term1127 _120521 A B f op).
Proof. exact (EQ_MP (@lem5801068 _120521 A B f op) (@lem5801053 _120521 A B f op)). Qed.
Lemma lem5801071 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1112 A P Q) = (term1113 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5801072 {_120521 : Type'} (P : Prop) (Q : _120521 -> Prop) : (term1112 _120521 P Q) = (term1113 _120521 P Q).
Proof. exact (@lem5801071 _120521 P Q). Qed.
Lemma lem5801073 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1128 _120521 A B f op f') = (term1129 _120521 A B f op f').
Proof. exact (@lem5801072 _120521 ((term1021 A B op f) = (@I ((B -> B -> B) -> B) (@neutral B) op)) (term1088 _120521 B op f')). Qed.
Lemma lem5801074 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1130 _120521 B op f x) = (term1087 _120521 B x op f).
Proof. exact (eq_refl (term1130 _120521 B op f x)). Qed.
Lemma lem5801075 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1131 _120521 B op f) = (term1088 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5801074 _120521 B x op f)). Qed.
Lemma lem5801076 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5801077 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term1132 _120521 B op f) = (term1089 _120521 B op f).
Proof. exact (MK_COMB (@lem5801076 _120521) (@lem5801075 _120521 B op f)). Qed.
Lemma lem5801078 {A B : Type'} (f : A -> B) (op : type1400 B) : (term1106 A B f op) = (term1106 A B f op).
Proof. exact (eq_refl (term1106 A B f op)). Qed.
Lemma lem5801079 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1128 _120521 A B f op f') = (term1124 _120521 A B f op f').
Proof. exact (MK_COMB (@lem5801078 A B f op) (@lem5801077 _120521 B op f')). Qed.
Lemma lem5801080 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5801081 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1133 _120521 A B f op f') = (term1134 _120521 A B f op f').
Proof. exact (MK_COMB (@lem5801080) (@lem5801079 _120521 A B f op f')). Qed.
Lemma lem5801082 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1130 _120521 B op f x) = (term1087 _120521 B x op f).
Proof. exact (eq_refl (term1130 _120521 B op f x)). Qed.
Lemma lem5801083 {A B : Type'} (f : A -> B) (op : type1400 B) : (term1106 A B f op) = (term1106 A B f op).
Proof. exact (eq_refl (term1106 A B f op)). Qed.
Lemma lem5801084 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1135 _120521 A B f op f' x) = (term1136 _120521 A B f x op f').
Proof. exact (MK_COMB (@lem5801083 A B f op) (@lem5801082 _120521 B x op f')). Qed.
Lemma lem5801085 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1137 _120521 A B f op f') = (term1138 _120521 A B f op f').
Proof. exact (fun_ext (fun x : _120521 => @lem5801084 _120521 A B f x op f')). Qed.
Lemma lem5801086 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5801087 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1129 _120521 A B f op f') = (term1139 _120521 A B f op f').
Proof. exact (MK_COMB (@lem5801086 _120521) (@lem5801085 _120521 A B f op f')). Qed.
Lemma lem5801088 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : ((term1128 _120521 A B f op f') = (term1129 _120521 A B f op f')) = ((term1124 _120521 A B f op f') = (term1139 _120521 A B f op f')).
Proof. exact (MK_COMB (@lem5801081 _120521 A B f op f') (@lem5801087 _120521 A B f op f')). Qed.
Lemma lem5801089 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1124 _120521 A B f op f') = (term1139 _120521 A B f op f').
Proof. exact (EQ_MP (@lem5801088 _120521 A B f op f') (@lem5801073 _120521 A B f op f')). Qed.
Lemma lem5801091 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1112 A P Q) = (term1113 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5801092 {_120521 : Type'} (P : Prop) (Q : type686 _120521) : (term1140 _120521 P Q) = (term1141 _120521 P Q).
Proof. exact (@lem5801091 (_120521 -> Prop) P Q). Qed.
Lemma lem5801093 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1142 _120521 A B f x op f') = (term1143 _120521 A B f x op f').
Proof. exact (@lem5801092 _120521 ((term1021 A B op f) = (@I ((B -> B -> B) -> B) (@neutral B) op)) (term1086 _120521 B x op f')). Qed.
Lemma lem5801094 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term1144 _120521 B x op f s) = (term1084 _120521 B x op s f).
Proof. exact (eq_refl (term1144 _120521 B x op f s)). Qed.
Lemma lem5801095 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1145 _120521 B x op f) = (term1086 _120521 B x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5801094 _120521 B x op s f)). Qed.
Lemma lem5801096 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5801097 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term1146 _120521 B x op f) = (term1087 _120521 B x op f).
Proof. exact (MK_COMB (@lem5801096 _120521) (@lem5801095 _120521 B x op f)). Qed.
Lemma lem5801098 {A B : Type'} (f : A -> B) (op : type1400 B) : (term1106 A B f op) = (term1106 A B f op).
Proof. exact (eq_refl (term1106 A B f op)). Qed.
Lemma lem5801099 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1142 _120521 A B f x op f') = (term1136 _120521 A B f x op f').
Proof. exact (MK_COMB (@lem5801098 A B f op) (@lem5801097 _120521 B x op f')). Qed.
Lemma lem5801100 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5801101 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1147 _120521 A B f x op f') = (term1148 _120521 A B f x op f').
Proof. exact (MK_COMB (@lem5801100) (@lem5801099 _120521 A B f x op f')). Qed.
Lemma lem5801102 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term1144 _120521 B x op f s) = (term1084 _120521 B x op s f).
Proof. exact (eq_refl (term1144 _120521 B x op f s)). Qed.
Lemma lem5801103 {A B : Type'} (f : A -> B) (op : type1400 B) : (term1106 A B f op) = (term1106 A B f op).
Proof. exact (eq_refl (term1106 A B f op)). Qed.
Lemma lem5801104 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f' : _120521 -> B) : (term1149 _120521 A B f x op f' s) = (term1150 _120521 A B f x op s f').
Proof. exact (MK_COMB (@lem5801103 A B f op) (@lem5801102 _120521 B x op s f')). Qed.
Lemma lem5801105 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1151 _120521 A B f x op f') = (term1152 _120521 A B f x op f').
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5801104 _120521 A B f x op s f')). Qed.
Lemma lem5801106 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5801107 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1143 _120521 A B f x op f') = (term1153 _120521 A B f x op f').
Proof. exact (MK_COMB (@lem5801106 _120521) (@lem5801105 _120521 A B f x op f')). Qed.
Lemma lem5801108 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : ((term1142 _120521 A B f x op f') = (term1143 _120521 A B f x op f')) = ((term1136 _120521 A B f x op f') = (term1153 _120521 A B f x op f')).
Proof. exact (MK_COMB (@lem5801101 _120521 A B f x op f') (@lem5801107 _120521 A B f x op f')). Qed.
Lemma lem5801109 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1136 _120521 A B f x op f') = (term1153 _120521 A B f x op f').
Proof. exact (EQ_MP (@lem5801108 _120521 A B f x op f') (@lem5801093 _120521 A B f x op f')). Qed.
Lemma lem5801110 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1138 _120521 A B f op f') = (term1154 _120521 A B f op f').
Proof. exact (fun_ext (fun x : _120521 => @lem5801109 _120521 A B f x op f')). Qed.
Lemma lem5801111 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5801112 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1139 _120521 A B f op f') = (term1155 _120521 A B f op f').
Proof. exact (MK_COMB (@lem5801111 _120521) (@lem5801110 _120521 A B f op f')). Qed.
Lemma lem5801113 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1124 _120521 A B f op f') = (term1155 _120521 A B f op f').
Proof. exact (TRANS (@lem5801089 _120521 A B f op f') (@lem5801112 _120521 A B f op f')). Qed.
Lemma lem5801114 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1126 _120521 A B f op) = (term1156 _120521 A B f op).
Proof. exact (fun_ext (fun f' : _120521 -> B => @lem5801113 _120521 A B f op f')). Qed.
Lemma lem5801115 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5801116 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1127 _120521 A B f op) = (term1157 _120521 A B f op).
Proof. exact (MK_COMB (@lem5801115 _120521 B) (@lem5801114 _120521 A B f op)). Qed.
Lemma lem5801117 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1108 _120521 A B f op) = (term1157 _120521 A B f op).
Proof. exact (TRANS (@lem5801069 _120521 A B f op) (@lem5801116 _120521 A B f op)). Qed.
Lemma lem5801118 {_120521 A B : Type'} (op : type1400 B) : (term1110 _120521 A B op) = (term1158 _120521 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5801117 _120521 A B f op)). Qed.
Lemma lem5801119 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5801120 {_120521 A B : Type'} (op : type1400 B) : (term1111 _120521 A B op) = (term1159 _120521 A B op).
Proof. exact (MK_COMB (@lem5801119 A B) (@lem5801118 _120521 A B op)). Qed.
Lemma lem5801121 {_120521 A B : Type'} (op : type1400 B) : (term1092 _120521 A B op) = (term1159 _120521 A B op).
Proof. exact (TRANS (@lem5801049 _120521 A B op) (@lem5801120 _120521 A B op)). Qed.
Lemma lem5801122 {_120521 A B : Type'} (op : type1400 B) : (term1027 _120521 A B op) = (term1159 _120521 A B op).
Proof. exact (TRANS (@lem5801023 _120521 A B op) (@lem5801121 _120521 A B op)). Qed.
Lemma lem5801123 {B : Type'} (op : type1400 B) : (term1030 B op) = (term1030 B op).
Proof. exact (eq_refl (term1030 B op)). Qed.
Lemma lem5801124 {_120521 A B : Type'} (op : type1400 B) : (term1031 _120521 A B op) = (term1160 _120521 A B op).
Proof. exact (MK_COMB (@lem5801123 B op) (@lem5801122 _120521 A B op)). Qed.
Lemma lem5801126 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1161 A P Q) = (term1162 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5801127 {A B : Type'} (P : Prop) (Q : type572 A B) : (term1163 A B P Q) = (term1164 A B P Q).
Proof. exact (@lem5801126 (A -> B) P Q). Qed.
Lemma lem5801128 {_120521 A B : Type'} (op : type1400 B) : (term1165 _120521 A B op) = (term1166 _120521 A B op).
Proof. exact (@lem5801127 A B (term1029 B op) (term1158 _120521 A B op)). Qed.
Lemma lem5801129 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1167 _120521 A B op f) = (term1157 _120521 A B f op).
Proof. exact (eq_refl (term1167 _120521 A B op f)). Qed.
Lemma lem5801130 {_120521 A B : Type'} (op : type1400 B) : (term1168 _120521 A B op) = (term1158 _120521 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5801129 _120521 A B f op)). Qed.
Lemma lem5801131 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5801132 {_120521 A B : Type'} (op : type1400 B) : (term1169 _120521 A B op) = (term1159 _120521 A B op).
Proof. exact (MK_COMB (@lem5801131 A B) (@lem5801130 _120521 A B op)). Qed.
Lemma lem5801133 {B : Type'} (op : type1400 B) : (term1030 B op) = (term1030 B op).
Proof. exact (eq_refl (term1030 B op)). Qed.
Lemma lem5801134 {_120521 A B : Type'} (op : type1400 B) : (term1165 _120521 A B op) = (term1160 _120521 A B op).
Proof. exact (MK_COMB (@lem5801133 B op) (@lem5801132 _120521 A B op)). Qed.
Lemma lem5801135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5801136 {_120521 A B : Type'} (op : type1400 B) : (term1170 _120521 A B op) = (term1171 _120521 A B op).
Proof. exact (MK_COMB (@lem5801135) (@lem5801134 _120521 A B op)). Qed.
Lemma lem5801137 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1167 _120521 A B op f) = (term1157 _120521 A B f op).
Proof. exact (eq_refl (term1167 _120521 A B op f)). Qed.
Lemma lem5801138 {B : Type'} (op : type1400 B) : (term1030 B op) = (term1030 B op).
Proof. exact (eq_refl (term1030 B op)). Qed.
Lemma lem5801139 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1172 _120521 A B op f) = (term1173 _120521 A B f op).
Proof. exact (MK_COMB (@lem5801138 B op) (@lem5801137 _120521 A B f op)). Qed.
Lemma lem5801140 {_120521 A B : Type'} (op : type1400 B) : (term1174 _120521 A B op) = (term1175 _120521 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5801139 _120521 A B f op)). Qed.
Lemma lem5801141 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5801142 {_120521 A B : Type'} (op : type1400 B) : (term1166 _120521 A B op) = (term1176 _120521 A B op).
Proof. exact (MK_COMB (@lem5801141 A B) (@lem5801140 _120521 A B op)). Qed.
Lemma lem5801143 {_120521 A B : Type'} (op : type1400 B) : ((term1165 _120521 A B op) = (term1166 _120521 A B op)) = ((term1160 _120521 A B op) = (term1176 _120521 A B op)).
Proof. exact (MK_COMB (@lem5801136 _120521 A B op) (@lem5801142 _120521 A B op)). Qed.
Lemma lem5801144 {_120521 A B : Type'} (op : type1400 B) : (term1160 _120521 A B op) = (term1176 _120521 A B op).
Proof. exact (EQ_MP (@lem5801143 _120521 A B op) (@lem5801128 _120521 A B op)). Qed.
Lemma lem5801146 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1161 A P Q) = (term1162 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5801147 {_120521 B : Type'} (P : Prop) (Q : type572 _120521 B) : (term1163 _120521 B P Q) = (term1164 _120521 B P Q).
Proof. exact (@lem5801146 (_120521 -> B) P Q). Qed.
Lemma lem5801148 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1177 _120521 A B f op) = (term1178 _120521 A B f op).
Proof. exact (@lem5801147 _120521 B (term1029 B op) (term1156 _120521 A B f op)). Qed.
Lemma lem5801149 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1179 _120521 A B f op f') = (term1155 _120521 A B f op f').
Proof. exact (eq_refl (term1179 _120521 A B f op f')). Qed.
Lemma lem5801150 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1180 _120521 A B f op) = (term1156 _120521 A B f op).
Proof. exact (fun_ext (fun f' : _120521 -> B => @lem5801149 _120521 A B f op f')). Qed.
Lemma lem5801151 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5801152 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1181 _120521 A B f op) = (term1157 _120521 A B f op).
Proof. exact (MK_COMB (@lem5801151 _120521 B) (@lem5801150 _120521 A B f op)). Qed.
Lemma lem5801153 {B : Type'} (op : type1400 B) : (term1030 B op) = (term1030 B op).
Proof. exact (eq_refl (term1030 B op)). Qed.
Lemma lem5801154 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1177 _120521 A B f op) = (term1173 _120521 A B f op).
Proof. exact (MK_COMB (@lem5801153 B op) (@lem5801152 _120521 A B f op)). Qed.
Lemma lem5801155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5801156 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1182 _120521 A B f op) = (term1183 _120521 A B f op).
Proof. exact (MK_COMB (@lem5801155) (@lem5801154 _120521 A B f op)). Qed.
Lemma lem5801157 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1179 _120521 A B f op f') = (term1155 _120521 A B f op f').
Proof. exact (eq_refl (term1179 _120521 A B f op f')). Qed.
Lemma lem5801158 {B : Type'} (op : type1400 B) : (term1030 B op) = (term1030 B op).
Proof. exact (eq_refl (term1030 B op)). Qed.
Lemma lem5801159 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1184 _120521 A B f op f') = (term1185 _120521 A B f op f').
Proof. exact (MK_COMB (@lem5801158 B op) (@lem5801157 _120521 A B f op f')). Qed.
Lemma lem5801160 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1186 _120521 A B f op) = (term1187 _120521 A B f op).
Proof. exact (fun_ext (fun f' : _120521 -> B => @lem5801159 _120521 A B f op f')). Qed.
Lemma lem5801161 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5801162 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1178 _120521 A B f op) = (term1188 _120521 A B f op).
Proof. exact (MK_COMB (@lem5801161 _120521 B) (@lem5801160 _120521 A B f op)). Qed.
Lemma lem5801163 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : ((term1177 _120521 A B f op) = (term1178 _120521 A B f op)) = ((term1173 _120521 A B f op) = (term1188 _120521 A B f op)).
Proof. exact (MK_COMB (@lem5801156 _120521 A B f op) (@lem5801162 _120521 A B f op)). Qed.
Lemma lem5801164 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1173 _120521 A B f op) = (term1188 _120521 A B f op).
Proof. exact (EQ_MP (@lem5801163 _120521 A B f op) (@lem5801148 _120521 A B f op)). Qed.
Lemma lem5801166 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1161 A P Q) = (term1162 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5801167 {_120521 : Type'} (P : Prop) (Q : _120521 -> Prop) : (term1161 _120521 P Q) = (term1162 _120521 P Q).
Proof. exact (@lem5801166 _120521 P Q). Qed.
Lemma lem5801168 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1189 _120521 A B f op f') = (term1190 _120521 A B f op f').
Proof. exact (@lem5801167 _120521 (term1029 B op) (term1154 _120521 A B f op f')). Qed.
Lemma lem5801169 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1191 _120521 A B f op f' x) = (term1153 _120521 A B f x op f').
Proof. exact (eq_refl (term1191 _120521 A B f op f' x)). Qed.
Lemma lem5801170 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1192 _120521 A B f op f') = (term1154 _120521 A B f op f').
Proof. exact (fun_ext (fun x : _120521 => @lem5801169 _120521 A B f x op f')). Qed.
Lemma lem5801171 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5801172 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1193 _120521 A B f op f') = (term1155 _120521 A B f op f').
Proof. exact (MK_COMB (@lem5801171 _120521) (@lem5801170 _120521 A B f op f')). Qed.
Lemma lem5801173 {B : Type'} (op : type1400 B) : (term1030 B op) = (term1030 B op).
Proof. exact (eq_refl (term1030 B op)). Qed.
Lemma lem5801174 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1189 _120521 A B f op f') = (term1185 _120521 A B f op f').
Proof. exact (MK_COMB (@lem5801173 B op) (@lem5801172 _120521 A B f op f')). Qed.
Lemma lem5801175 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5801176 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1194 _120521 A B f op f') = (term1195 _120521 A B f op f').
Proof. exact (MK_COMB (@lem5801175) (@lem5801174 _120521 A B f op f')). Qed.
Lemma lem5801177 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1191 _120521 A B f op f' x) = (term1153 _120521 A B f x op f').
Proof. exact (eq_refl (term1191 _120521 A B f op f' x)). Qed.
Lemma lem5801178 {B : Type'} (op : type1400 B) : (term1030 B op) = (term1030 B op).
Proof. exact (eq_refl (term1030 B op)). Qed.
Lemma lem5801179 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1196 _120521 A B f op f' x) = (term1197 _120521 A B f x op f').
Proof. exact (MK_COMB (@lem5801178 B op) (@lem5801177 _120521 A B f x op f')). Qed.
Lemma lem5801180 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1198 _120521 A B f op f') = (term1199 _120521 A B f op f').
Proof. exact (fun_ext (fun x : _120521 => @lem5801179 _120521 A B f x op f')). Qed.
Lemma lem5801181 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5801182 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1190 _120521 A B f op f') = (term1200 _120521 A B f op f').
Proof. exact (MK_COMB (@lem5801181 _120521) (@lem5801180 _120521 A B f op f')). Qed.
Lemma lem5801183 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : ((term1189 _120521 A B f op f') = (term1190 _120521 A B f op f')) = ((term1185 _120521 A B f op f') = (term1200 _120521 A B f op f')).
Proof. exact (MK_COMB (@lem5801176 _120521 A B f op f') (@lem5801182 _120521 A B f op f')). Qed.
Lemma lem5801184 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1185 _120521 A B f op f') = (term1200 _120521 A B f op f').
Proof. exact (EQ_MP (@lem5801183 _120521 A B f op f') (@lem5801168 _120521 A B f op f')). Qed.
Lemma lem5801186 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1161 A P Q) = (term1162 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5801187 {_120521 : Type'} (P : Prop) (Q : type686 _120521) : (term1201 _120521 P Q) = (term1202 _120521 P Q).
Proof. exact (@lem5801186 (_120521 -> Prop) P Q). Qed.
Lemma lem5801188 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1203 _120521 A B f x op f') = (term1204 _120521 A B f x op f').
Proof. exact (@lem5801187 _120521 (term1029 B op) (term1152 _120521 A B f x op f')). Qed.
Lemma lem5801189 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f' : _120521 -> B) : (term1205 _120521 A B f x op f' s) = (term1150 _120521 A B f x op s f').
Proof. exact (eq_refl (term1205 _120521 A B f x op f' s)). Qed.
Lemma lem5801190 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1206 _120521 A B f x op f') = (term1152 _120521 A B f x op f').
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5801189 _120521 A B f x op s f')). Qed.
Lemma lem5801191 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5801192 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1207 _120521 A B f x op f') = (term1153 _120521 A B f x op f').
Proof. exact (MK_COMB (@lem5801191 _120521) (@lem5801190 _120521 A B f x op f')). Qed.
Lemma lem5801193 {B : Type'} (op : type1400 B) : (term1030 B op) = (term1030 B op).
Proof. exact (eq_refl (term1030 B op)). Qed.
Lemma lem5801194 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1203 _120521 A B f x op f') = (term1197 _120521 A B f x op f').
Proof. exact (MK_COMB (@lem5801193 B op) (@lem5801192 _120521 A B f x op f')). Qed.
Lemma lem5801195 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5801196 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1208 _120521 A B f x op f') = (term1209 _120521 A B f x op f').
Proof. exact (MK_COMB (@lem5801195) (@lem5801194 _120521 A B f x op f')). Qed.
Lemma lem5801197 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f' : _120521 -> B) : (term1205 _120521 A B f x op f' s) = (term1150 _120521 A B f x op s f').
Proof. exact (eq_refl (term1205 _120521 A B f x op f' s)). Qed.
Lemma lem5801198 {B : Type'} (op : type1400 B) : (term1030 B op) = (term1030 B op).
Proof. exact (eq_refl (term1030 B op)). Qed.
Lemma lem5801199 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f' : _120521 -> B) : (term1210 _120521 A B f x op f' s) = (term1211 _120521 A B f x op s f').
Proof. exact (MK_COMB (@lem5801198 B op) (@lem5801197 _120521 A B f x op s f')). Qed.
Lemma lem5801200 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1212 _120521 A B f x op f') = (term1213 _120521 A B f x op f').
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5801199 _120521 A B f x op s f')). Qed.
Lemma lem5801201 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5801202 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1204 _120521 A B f x op f') = (term1214 _120521 A B f x op f').
Proof. exact (MK_COMB (@lem5801201 _120521) (@lem5801200 _120521 A B f x op f')). Qed.
Lemma lem5801203 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : ((term1203 _120521 A B f x op f') = (term1204 _120521 A B f x op f')) = ((term1197 _120521 A B f x op f') = (term1214 _120521 A B f x op f')).
Proof. exact (MK_COMB (@lem5801196 _120521 A B f x op f') (@lem5801202 _120521 A B f x op f')). Qed.
Lemma lem5801204 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1197 _120521 A B f x op f') = (term1214 _120521 A B f x op f').
Proof. exact (EQ_MP (@lem5801203 _120521 A B f x op f') (@lem5801188 _120521 A B f x op f')). Qed.
Lemma lem5801205 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1199 _120521 A B f op f') = (term1215 _120521 A B f op f').
Proof. exact (fun_ext (fun x : _120521 => @lem5801204 _120521 A B f x op f')). Qed.
Lemma lem5801206 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5801207 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1200 _120521 A B f op f') = (term1216 _120521 A B f op f').
Proof. exact (MK_COMB (@lem5801206 _120521) (@lem5801205 _120521 A B f op f')). Qed.
Lemma lem5801208 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1185 _120521 A B f op f') = (term1216 _120521 A B f op f').
Proof. exact (TRANS (@lem5801184 _120521 A B f op f') (@lem5801207 _120521 A B f op f')). Qed.
Lemma lem5801209 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1187 _120521 A B f op) = (term1217 _120521 A B f op).
Proof. exact (fun_ext (fun f' : _120521 -> B => @lem5801208 _120521 A B f op f')). Qed.
Lemma lem5801210 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5801211 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1188 _120521 A B f op) = (term1218 _120521 A B f op).
Proof. exact (MK_COMB (@lem5801210 _120521 B) (@lem5801209 _120521 A B f op)). Qed.
Lemma lem5801212 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1173 _120521 A B f op) = (term1218 _120521 A B f op).
Proof. exact (TRANS (@lem5801164 _120521 A B f op) (@lem5801211 _120521 A B f op)). Qed.
Lemma lem5801213 {_120521 A B : Type'} (op : type1400 B) : (term1175 _120521 A B op) = (term1219 _120521 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5801212 _120521 A B f op)). Qed.
Lemma lem5801214 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5801215 {_120521 A B : Type'} (op : type1400 B) : (term1176 _120521 A B op) = (term1220 _120521 A B op).
Proof. exact (MK_COMB (@lem5801214 A B) (@lem5801213 _120521 A B op)). Qed.
Lemma lem5801216 {_120521 A B : Type'} (op : type1400 B) : (term1160 _120521 A B op) = (term1220 _120521 A B op).
Proof. exact (TRANS (@lem5801144 _120521 A B op) (@lem5801215 _120521 A B op)). Qed.
Lemma lem5801217 {_120521 A B : Type'} (op : type1400 B) : (term1031 _120521 A B op) = (term1220 _120521 A B op).
Proof. exact (TRANS (@lem5801124 _120521 A B op) (@lem5801216 _120521 A B op)). Qed.
Lemma lem5801218 {_120521 A B : Type'} : (term1032 _120521 A B) = (term1221 _120521 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5801217 _120521 A B op)). Qed.
Lemma lem5801219 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5801220 {_120521 A B : Type'} : (term1033 _120521 A B) = (term1222 _120521 A B).
Proof. exact (MK_COMB (@lem5801219 B) (@lem5801218 _120521 A B)). Qed.
Lemma lem5801258 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f' : _120521 -> B) : (term1211 _120521 A B f x op s f') = (term1223 _120521 A B f x op s f').
Proof. exact (@lem19490 ((term1021 A B op f) = (@I ((B -> B -> B) -> B) (@neutral B) op)) (term1029 B op) (term1084 _120521 B x op s f')). Qed.
Lemma lem5801265 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term1224 _120521 B x op s f) = (term1225 _120521 B x op s f).
Proof. exact (@lem19490 (term1010 _120521 B x op s f) (term1029 B op) (term1002 _120521 B x op s f)). Qed.
Lemma lem5801268 {A B : Type'} (f : A -> B) (op : type1400 B) : (term1226 A B f op) = (term1226 A B f op).
Proof. exact (eq_refl (term1226 A B f op)). Qed.
Lemma lem5801269 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f' : _120521 -> B) : (term1223 _120521 A B f x op s f') = (term1227 _120521 A B f x op s f').
Proof. exact (MK_COMB (@lem5801268 A B f op) (@lem5801265 _120521 B x op s f')). Qed.
Lemma lem5801271 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f' : _120521 -> B) : (term1211 _120521 A B f x op s f') = (term1227 _120521 A B f x op s f').
Proof. exact (TRANS (@lem5801258 _120521 A B f x op s f') (@lem5801269 _120521 A B f x op s f')). Qed.
Lemma lem5801272 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1213 _120521 A B f x op f') = (term1228 _120521 A B f x op f').
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5801271 _120521 A B f x op s f')). Qed.
Lemma lem5801273 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5801274 {_120521 A B : Type'} (f : A -> B) (x : _120521) (op : type1400 B) (f' : _120521 -> B) : (term1214 _120521 A B f x op f') = (term1229 _120521 A B f x op f').
Proof. exact (MK_COMB (@lem5801273 _120521) (@lem5801272 _120521 A B f x op f')). Qed.
Lemma lem5801275 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1215 _120521 A B f op f') = (term1230 _120521 A B f op f').
Proof. exact (fun_ext (fun x : _120521 => @lem5801274 _120521 A B f x op f')). Qed.
Lemma lem5801276 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5801277 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) (f' : _120521 -> B) : (term1216 _120521 A B f op f') = (term1231 _120521 A B f op f').
Proof. exact (MK_COMB (@lem5801276 _120521) (@lem5801275 _120521 A B f op f')). Qed.
Lemma lem5801278 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1217 _120521 A B f op) = (term1232 _120521 A B f op).
Proof. exact (fun_ext (fun f' : _120521 -> B => @lem5801277 _120521 A B f op f')). Qed.
Lemma lem5801279 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5801280 {_120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1218 _120521 A B f op) = (term1233 _120521 A B f op).
Proof. exact (MK_COMB (@lem5801279 _120521 B) (@lem5801278 _120521 A B f op)). Qed.
Lemma lem5801281 {_120521 A B : Type'} (op : type1400 B) : (term1219 _120521 A B op) = (term1234 _120521 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5801280 _120521 A B f op)). Qed.
Lemma lem5801282 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5801283 {_120521 A B : Type'} (op : type1400 B) : (term1220 _120521 A B op) = (term1235 _120521 A B op).
Proof. exact (MK_COMB (@lem5801282 A B) (@lem5801281 _120521 A B op)). Qed.
Lemma lem5801284 {_120521 A B : Type'} : (term1221 _120521 A B) = (term1236 _120521 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5801283 _120521 A B op)). Qed.
Lemma lem5801285 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5801286 {_120521 A B : Type'} : (term1222 _120521 A B) = (term1237 _120521 A B).
Proof. exact (MK_COMB (@lem5801285 B) (@lem5801284 _120521 A B)). Qed.
Lemma lem5801287 {_120521 A B : Type'} : (term1033 _120521 A B) = (term1237 _120521 A B).
Proof. exact (TRANS (@lem5801220 _120521 A B) (@lem5801286 _120521 A B)). Qed.
Lemma lem5801288 {_120521 A B : Type'} (h1 : term760 _120521 A B) : term1237 _120521 A B.
Proof. exact (EQ_MP (@lem5801287 _120521 A B) (@lem5799021 _120521 A B h1)). Qed.
Lemma lem5801771 {A B : Type'} (_73035 : type1400 B) (h1 : term601 A B) : term1238 A B _73035.
Proof. exact (@lem5799469 A B h1 _73035). Qed.
Lemma lem5801772 {A B : Type'} (_73035 : type1400 B) : (term1238 A B _73035) = (term979 A B _73035).
Proof. exact (eq_refl (term1238 A B _73035)). Qed.
Lemma lem5801773 {A B : Type'} (_73035 : type1400 B) (h1 : term601 A B) : term979 A B _73035.
Proof. exact (EQ_MP (@lem5801772 A B _73035) (@lem5801771 A B _73035 h1)). Qed.
Lemma lem5801774 {A B : Type'} (_73035 : type1400 B) (_73036 : A -> B) (h1 : term601 A B) : term1239 A B _73035 _73036.
Proof. exact (@lem5801773 A B _73035 h1 _73036). Qed.
Lemma lem5801775 {A B : Type'} (_73035 : type1400 B) (_73036 : A -> B) : (term1239 A B _73035 _73036) = (term977 A B _73035 _73036).
Proof. exact (eq_refl (term1239 A B _73035 _73036)). Qed.
Lemma lem5801776 {A B : Type'} (_73035 : type1400 B) (_73036 : A -> B) (h1 : term601 A B) : term977 A B _73035 _73036.
Proof. exact (EQ_MP (@lem5801775 A B _73035 _73036) (@lem5801774 A B _73035 _73036 h1)). Qed.
Lemma lem5801777 {A B : Type'} (_73035 : type1400 B) (_73036 : A -> B) (_73037 : A -> Prop) (h1 : term601 A B) : term1240 A B _73035 _73036 _73037.
Proof. exact (@lem5801776 A B _73035 _73036 h1 _73037). Qed.
Lemma lem5801778 {A B : Type'} (_73035 : type1400 B) (_73037 : A -> Prop) (_73036 : A -> B) : (term1240 A B _73035 _73036 _73037) = ((term973 A B _73035 _73037 _73036) = (term963 A B _73035 _73037 _73036)).
Proof. exact (eq_refl (term1240 A B _73035 _73036 _73037)). Qed.
Lemma lem5801867 {_120521 A B : Type'} (_73067 : type1400 B) (h1 : term760 _120521 A B) : term1241 _120521 A B _73067.
Proof. exact (@lem5801288 _120521 A B h1 _73067). Qed.
Lemma lem5801868 {_120521 A B : Type'} (_73067 : type1400 B) : (term1241 _120521 A B _73067) = (term1235 _120521 A B _73067).
Proof. exact (eq_refl (term1241 _120521 A B _73067)). Qed.
Lemma lem5801869 {_120521 A B : Type'} (_73067 : type1400 B) (h1 : term760 _120521 A B) : term1235 _120521 A B _73067.
Proof. exact (EQ_MP (@lem5801868 _120521 A B _73067) (@lem5801867 _120521 A B _73067 h1)). Qed.
Lemma lem5801870 {_120521 A B : Type'} (_73067 : type1400 B) (_73068 : A -> B) (h1 : term760 _120521 A B) : term1242 _120521 A B _73067 _73068.
Proof. exact (@lem5801869 _120521 A B _73067 h1 _73068). Qed.
Lemma lem5801871 {_120521 A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) : (term1242 _120521 A B _73067 _73068) = (term1233 _120521 A B _73068 _73067).
Proof. exact (eq_refl (term1242 _120521 A B _73067 _73068)). Qed.
Lemma lem5801872 {_120521 A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) (h1 : term760 _120521 A B) : term1233 _120521 A B _73068 _73067.
Proof. exact (EQ_MP (@lem5801871 _120521 A B _73068 _73067) (@lem5801870 _120521 A B _73067 _73068 h1)). Qed.
Lemma lem5801873 {_120521 A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) (_73069 : _120521 -> B) (h1 : term760 _120521 A B) : term1243 _120521 A B _73068 _73067 _73069.
Proof. exact (@lem5801872 _120521 A B _73068 _73067 h1 _73069). Qed.
Lemma lem5801874 {_120521 A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) (_73069 : _120521 -> B) : (term1243 _120521 A B _73068 _73067 _73069) = (term1231 _120521 A B _73068 _73067 _73069).
Proof. exact (eq_refl (term1243 _120521 A B _73068 _73067 _73069)). Qed.
Lemma lem5801875 {_120521 A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) (_73069 : _120521 -> B) (h1 : term760 _120521 A B) : term1231 _120521 A B _73068 _73067 _73069.
Proof. exact (EQ_MP (@lem5801874 _120521 A B _73068 _73067 _73069) (@lem5801873 _120521 A B _73068 _73067 _73069 h1)). Qed.
Lemma lem5801876 {_120521 A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) (_73069 : _120521 -> B) (_73070 : _120521) (h1 : term760 _120521 A B) : term1244 _120521 A B _73068 _73067 _73069 _73070.
Proof. exact (@lem5801875 _120521 A B _73068 _73067 _73069 h1 _73070). Qed.
Lemma lem5801877 {_120521 A B : Type'} (_73068 : A -> B) (_73070 : _120521) (_73067 : type1400 B) (_73069 : _120521 -> B) : (term1244 _120521 A B _73068 _73067 _73069 _73070) = (term1229 _120521 A B _73068 _73070 _73067 _73069).
Proof. exact (eq_refl (term1244 _120521 A B _73068 _73067 _73069 _73070)). Qed.
Lemma lem5801878 {_120521 A B : Type'} (_73068 : A -> B) (_73070 : _120521) (_73067 : type1400 B) (_73069 : _120521 -> B) (h1 : term760 _120521 A B) : term1229 _120521 A B _73068 _73070 _73067 _73069.
Proof. exact (EQ_MP (@lem5801877 _120521 A B _73068 _73070 _73067 _73069) (@lem5801876 _120521 A B _73068 _73067 _73069 _73070 h1)). Qed.
Lemma lem5801879 {_120521 A B : Type'} (_73068 : A -> B) (_73070 : _120521) (_73067 : type1400 B) (_73069 : _120521 -> B) (_73071 : _120521 -> Prop) (h1 : term760 _120521 A B) : term1245 _120521 A B _73068 _73070 _73067 _73069 _73071.
Proof. exact (@lem5801878 _120521 A B _73068 _73070 _73067 _73069 h1 _73071). Qed.
Lemma lem5801880 {_120521 A B : Type'} (_73068 : A -> B) (_73070 : _120521) (_73067 : type1400 B) (_73071 : _120521 -> Prop) (_73069 : _120521 -> B) : (term1245 _120521 A B _73068 _73070 _73067 _73069 _73071) = (term1227 _120521 A B _73068 _73070 _73067 _73071 _73069).
Proof. exact (eq_refl (term1245 _120521 A B _73068 _73070 _73067 _73069 _73071)). Qed.
Lemma lem5801881 {_120521 A B : Type'} (_73068 : A -> B) (_73070 : _120521) (_73067 : type1400 B) (_73071 : _120521 -> Prop) (_73069 : _120521 -> B) (h1 : term760 _120521 A B) : term1227 _120521 A B _73068 _73070 _73067 _73071 _73069.
Proof. exact (EQ_MP (@lem5801880 _120521 A B _73068 _73070 _73067 _73071 _73069) (@lem5801879 _120521 A B _73068 _73070 _73067 _73069 _73071 h1)). Qed.
Lemma lem5801948 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : (@support A B op f s) = (@EMPTY A)) : (term399 A B op f s) = (@EMPTY A).
Proof. exact (EQ_MP (@lem5796260 A B op f s) (@lem5792232 A B op f s h1)). Qed.
Lemma lem5802036 {_120521 A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) (h1 : term760 _120521 A B) : term1246 A B _73068 _73067.
Proof. exact (proj1 (@lem5801881 _120521 A B _73068 (@el _120521) _73067 (@el (_120521 -> Prop)) (@el (_120521 -> B)) h1)). Qed.
Lemma lem5802201 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : (@support A B op f s) = (@EMPTY A)) : (@EMPTY A) = (term399 A B op f s).
Proof. exact (SYM (@lem5801948 A B op f s h1)). Qed.
Lemma lem5802257 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term594 A B s f op) : term966 A B s f op.
Proof. exact (EQ_MP (@lem5796300 A B s f op) (@lem5792238 A B s f op h1)). Qed.
Lemma lem5802537 {A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) : (term1247 A B _73068 _73067) = (term1247 A B _73068 _73067).
Proof. exact (eq_refl (term1247 A B _73068 _73067)). Qed.
Lemma lem5802538 {A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : (@support A B op f s) = (@EMPTY A)) : (term1248 A B _73068 _73067) = (term1249 A B _73068 _73067 op f s).
Proof. exact (MK_COMB (@lem5802537 A B _73068 _73067) (@lem5802201 A B op f s h1)). Qed.
Lemma lem5802539 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : (term1249 A B _73068 _73067 op f s) = (term1250 A B op f s _73068 _73067).
Proof. exact (eq_refl (term1249 A B _73068 _73067 op f s)). Qed.
Lemma lem5802540 {A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) : (term1251 A B _73068 _73067) = (term1251 A B _73068 _73067).
Proof. exact (eq_refl (term1251 A B _73068 _73067)). Qed.
Lemma lem5802541 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : ((term1248 A B _73068 _73067) = (term1249 A B _73068 _73067 op f s)) = ((term1248 A B _73068 _73067) = (term1250 A B op f s _73068 _73067)).
Proof. exact (MK_COMB (@lem5802540 A B _73068 _73067) (@lem5802539 A B op f s _73068 _73067)). Qed.
Lemma lem5802542 {A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) : (term1248 A B _73068 _73067) = (term1246 A B _73068 _73067).
Proof. exact (eq_refl (term1248 A B _73068 _73067)). Qed.
Lemma lem5802543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5802544 {A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) : (term1251 A B _73068 _73067) = (term1252 A B _73068 _73067).
Proof. exact (MK_COMB (@lem5802543) (@lem5802542 A B _73068 _73067)). Qed.
Lemma lem5802545 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : (term1250 A B op f s _73068 _73067) = (term1250 A B op f s _73068 _73067).
Proof. exact (eq_refl (term1250 A B op f s _73068 _73067)). Qed.
Lemma lem5802546 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : ((term1248 A B _73068 _73067) = (term1250 A B op f s _73068 _73067)) = ((term1246 A B _73068 _73067) = (term1250 A B op f s _73068 _73067)).
Proof. exact (MK_COMB (@lem5802544 A B _73068 _73067) (@lem5802545 A B op f s _73068 _73067)). Qed.
Lemma lem5802547 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : ((term1248 A B _73068 _73067) = (term1249 A B _73068 _73067 op f s)) = ((term1246 A B _73068 _73067) = (term1250 A B op f s _73068 _73067)).
Proof. exact (TRANS (@lem5802541 A B op f s _73068 _73067) (@lem5802546 A B op f s _73068 _73067)). Qed.
Lemma lem5802548 {A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : (@support A B op f s) = (@EMPTY A)) : (term1246 A B _73068 _73067) = (term1250 A B op f s _73068 _73067).
Proof. exact (EQ_MP (@lem5802547 A B op f s _73068 _73067) (@lem5802538 A B _73068 _73067 op f s h1)). Qed.
Lemma lem5802549 {_120521 A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term760 _120521 A B) (h2 : (@support A B op f s) = (@EMPTY A)) : term1250 A B op f s _73068 _73067.
Proof. exact (EQ_MP (@lem5802548 A B _73068 _73067 op f s h2) (@lem5802036 _120521 A B _73068 _73067 h1)). Qed.
Lemma lem5804015 {B : Type'} (x : B) (y : B) (z : B) : term1253 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem5804211 {A B : Type'} (_73035 : type1400 B) (_73037 : A -> Prop) (_73036 : A -> B) (h1 : term601 A B) : (term973 A B _73035 _73037 _73036) = (term963 A B _73035 _73037 _73036).
Proof. exact (EQ_MP (@lem5801778 A B _73035 _73037 _73036) (@lem5801777 A B _73035 _73036 _73037 h1)). Qed.
Lemma lem5804212 {A B : Type'} (_73035 : type1400 B) (_73037 : A -> Prop) (_73036 : A -> B) (h1 : term601 A B) : (term973 A B _73035 _73037 _73036) = (term963 A B _73035 _73037 _73036).
Proof. exact (@lem5804211 A B _73035 _73037 _73036 h1). Qed.
Lemma lem5804213 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term601 A B) : (term973 A B op s f) = (term963 A B op s f).
Proof. exact (@lem5804212 A B op s f h1). Qed.
Lemma lem5804214 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term601 A B) : term1254 A B op s f.
Proof. exact (fun h0 : term1255 A B op s f => @lem5804213 A B op s f h1). Qed.
Lemma lem5804216 (p : Prop) : (term539 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5804217 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term1254 A B op s f) = ((term973 A B op s f) = (term963 A B op s f)).
Proof. exact (@lem5804216 ((term973 A B op s f) = (term963 A B op s f))). Qed.
Lemma lem5804218 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term601 A B) : (term973 A B op s f) = (term963 A B op s f).
Proof. exact (EQ_MP (@lem5804217 A B op s f) (@lem5804214 A B op s f h1)). Qed.
Lemma lem5804220 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @I ((B -> B -> B) -> Prop) (@monoidal B) op.
Proof. exact (EQ_MP (@lem5796185 B op) (@lem5792163 B op h1)). Qed.
Lemma lem5804221 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term1256 B op.
Proof. exact (fun h0 : term1029 B op => @lem5804220 B op h1). Qed.
Lemma lem5804223 (p : Prop) : (term539 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5804224 {B : Type'} (op : type1400 B) : (term1256 B op) = (@I ((B -> B -> B) -> Prop) (@monoidal B) op).
Proof. exact (@lem5804223 (@I ((B -> B -> B) -> Prop) (@monoidal B) op)). Qed.
Lemma lem5804225 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @I ((B -> B -> B) -> Prop) (@monoidal B) op.
Proof. exact (EQ_MP (@lem5804224 B op) (@lem5804221 B op h1)). Qed.
Lemma lem5804231 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5804232 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : (term1250 A B op f s _73068 _73067) = (term1257 A B op f s _73068 _73067).
Proof. exact (@lem5804231 ((term1258 A B _73067 op f s _73068) = (@I ((B -> B -> B) -> B) (@neutral B) _73067)) (term1029 B _73067)). Qed.
Lemma lem5804240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5804241 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : (term1259 A B op f s _73068 _73067) = (term1260 A B op f s _73068 _73067).
Proof. exact (MK_COMB (@lem5804240) (@lem5804232 A B op f s _73068 _73067)). Qed.
Lemma lem5804249 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : (term1257 A B op f s _73068 _73067) = (term1257 A B op f s _73068 _73067).
Proof. exact (eq_refl (term1257 A B op f s _73068 _73067)). Qed.
Lemma lem5804250 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : ((term1250 A B op f s _73068 _73067) = (term1257 A B op f s _73068 _73067)) = ((term1257 A B op f s _73068 _73067) = (term1257 A B op f s _73068 _73067)).
Proof. exact (MK_COMB (@lem5804241 A B op f s _73068 _73067) (@lem5804249 A B op f s _73068 _73067)). Qed.
Lemma lem5804252 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5804253 (x : Prop) : (x = x) = True.
Proof. exact (@lem5804252 Prop x). Qed.
Lemma lem5804254 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : ((term1257 A B op f s _73068 _73067) = (term1257 A B op f s _73068 _73067)) = True.
Proof. exact (@lem5804253 (term1257 A B op f s _73068 _73067)). Qed.
Lemma lem5804255 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : ((term1250 A B op f s _73068 _73067) = (term1257 A B op f s _73068 _73067)) = True.
Proof. exact (TRANS (@lem5804250 A B op f s _73068 _73067) (@lem5804254 A B op f s _73068 _73067)). Qed.
Lemma lem5804256 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : True = ((term1250 A B op f s _73068 _73067) = (term1257 A B op f s _73068 _73067)).
Proof. exact (SYM (@lem5804255 A B op f s _73068 _73067)). Qed.
Lemma lem5804257 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : (term1250 A B op f s _73068 _73067) = (term1257 A B op f s _73068 _73067).
Proof. exact (EQ_MP (@lem5804256 A B op f s _73068 _73067) (@lem0)). Qed.
Lemma lem5804258 {_120521 A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term760 _120521 A B) (h2 : (@support A B op f s) = (@EMPTY A)) : term1257 A B op f s _73068 _73067.
Proof. exact (EQ_MP (@lem5804257 A B op f s _73068 _73067) (@lem5802549 _120521 A B _73068 _73067 op f s h1 h2)). Qed.
Lemma lem5804260 (b : Prop) (a : Prop) : (a \/ b) = (term524 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5804261 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : (term1257 A B op f s _73068 _73067) = (term1261 A B op f s _73068 _73067).
Proof. exact (@lem5804260 (term1029 B _73067) ((term1258 A B _73067 op f s _73068) = (@I ((B -> B -> B) -> B) (@neutral B) _73067))). Qed.
Lemma lem5804263 (a : Prop) : (term544 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5804264 {B : Type'} (_73067 : type1400 B) : (term1262 B _73067) = (@I ((B -> B -> B) -> Prop) (@monoidal B) _73067).
Proof. exact (@lem5804263 (@I ((B -> B -> B) -> Prop) (@monoidal B) _73067)). Qed.
Lemma lem5804265 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5804266 {B : Type'} (_73067 : type1400 B) : (term1263 B _73067) = (term1264 B _73067).
Proof. exact (MK_COMB (@lem5804265) (@lem5804264 B _73067)). Qed.
Lemma lem5804267 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : ((term1258 A B _73067 op f s _73068) = (@I ((B -> B -> B) -> B) (@neutral B) _73067)) = ((term1258 A B _73067 op f s _73068) = (@I ((B -> B -> B) -> B) (@neutral B) _73067)).
Proof. exact (eq_refl ((term1258 A B _73067 op f s _73068) = (@I ((B -> B -> B) -> B) (@neutral B) _73067))). Qed.
Lemma lem5804268 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : (term1261 A B op f s _73068 _73067) = (term1265 A B op f s _73068 _73067).
Proof. exact (MK_COMB (@lem5804266 B _73067) (@lem5804267 A B op f s _73068 _73067)). Qed.
Lemma lem5804269 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (_73068 : A -> B) (_73067 : type1400 B) : (term1257 A B op f s _73068 _73067) = (term1265 A B op f s _73068 _73067).
Proof. exact (TRANS (@lem5804261 A B op f s _73068 _73067) (@lem5804268 A B op f s _73068 _73067)). Qed.
Lemma lem5804272 {_120521 A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term760 _120521 A B) (h2 : (@support A B op f s) = (@EMPTY A)) : term1265 A B op f s _73068 _73067.
Proof. exact (EQ_MP (@lem5804269 A B op f s _73068 _73067) (@lem5804258 _120521 A B _73068 _73067 op f s h1 h2)). Qed.
Lemma lem5804273 {_120521 A B : Type'} (_73068 : A -> B) (_73067 : type1400 B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term760 _120521 A B) (h2 : (@support A B op f s) = (@EMPTY A)) : term1265 A B op f s _73068 _73067.
Proof. exact (@lem5804272 _120521 A B _73068 _73067 op f s h1 h2). Qed.
Lemma lem5804274 {_120521 A B : Type'} (_73068 : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term760 _120521 A B) (h2 : (@support A B op f s) = (@EMPTY A)) : term1266 A B f s _73068 op.
Proof. exact (@lem5804273 _120521 A B _73068 op op f s h1 h2). Qed.
Lemma lem5804277 {_120521 A B : Type'} (_73068 : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term760 _120521 A B) (h2 : @monoidal B op) (h3 : (@support A B op f s) = (@EMPTY A)) : (term1267 A B op f s _73068) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5804274 _120521 A B _73068 op f s h1 h3 (@lem5804225 B op h2)). Qed.
Lemma lem5804278 {_120521 A B : Type'} (_73068 : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term760 _120521 A B) (h2 : @monoidal B op) (h3 : (@support A B op f s) = (@EMPTY A)) : (term1267 A B op f s _73068) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5804277 _120521 A B _73068 op f s h1 h2 h3). Qed.
Lemma lem5804279 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term760 _120521 A B) (h2 : @monoidal B op) (h3 : (@support A B op f s) = (@EMPTY A)) : (term973 A B op s f) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5804278 _120521 A B f op f s h1 h2 h3). Qed.
Lemma lem5804280 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term760 _120521 A B) (h2 : @monoidal B op) (h3 : (@support A B op f s) = (@EMPTY A)) : term1268 A B s f op.
Proof. exact (fun h0 : term1269 A B s f op => @lem5804279 _120521 A B op f s h1 h2 h3). Qed.
Lemma lem5804282 (p : Prop) : (term539 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5804283 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1268 A B s f op) = ((term973 A B op s f) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (@lem5804282 ((term973 A B op s f) = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem5804284 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term760 _120521 A B) (h2 : @monoidal B op) (h3 : (@support A B op f s) = (@EMPTY A)) : (term973 A B op s f) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (EQ_MP (@lem5804283 A B s f op) (@lem5804280 _120521 A B op f s h1 h2 h3)). Qed.
Lemma lem5804302 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5804303 {B : Type'} (y : B) (x : B) (z : B) : (term1270 B x y z) = (term1271 B y x z).
Proof. exact (@lem5804302 (y = z) (term1272 B x z)). Qed.
Lemma lem5804313 {B : Type'} (x : B) (y : B) : (term1273 B x y) = (term1273 B x y).
Proof. exact (eq_refl (term1273 B x y)). Qed.
Lemma lem5804314 {B : Type'} (y : B) (x : B) (z : B) : (term1253 B x y z) = (term1274 B y x z).
Proof. exact (MK_COMB (@lem5804313 B x y) (@lem5804303 B y x z)). Qed.
Lemma lem5804318 (q : Prop) (p : Prop) (r : Prop) : (term521 p q r) = (term521 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5804319 {B : Type'} (y : B) (x : B) (z : B) : (term1274 B y x z) = (term1275 B y x z).
Proof. exact (@lem5804318 (y = z) (term1272 B x y) (term1272 B x z)). Qed.
Lemma lem5804341 {B : Type'} (y : B) (x : B) (z : B) : (term1253 B x y z) = (term1275 B y x z).
Proof. exact (TRANS (@lem5804314 B y x z) (@lem5804319 B y x z)). Qed.
Lemma lem5804342 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5804343 {B : Type'} (y : B) (x : B) (z : B) : (term1276 B x y z) = (term1277 B y x z).
Proof. exact (MK_COMB (@lem5804342) (@lem5804341 B y x z)). Qed.
Lemma lem5804365 {B : Type'} (y : B) (x : B) (z : B) : (term1275 B y x z) = (term1275 B y x z).
Proof. exact (eq_refl (term1275 B y x z)). Qed.
Lemma lem5804366 {B : Type'} (y : B) (x : B) (z : B) : ((term1253 B x y z) = (term1275 B y x z)) = ((term1275 B y x z) = (term1275 B y x z)).
Proof. exact (MK_COMB (@lem5804343 B y x z) (@lem5804365 B y x z)). Qed.
Lemma lem5804368 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5804369 (x : Prop) : (x = x) = True.
Proof. exact (@lem5804368 Prop x). Qed.
Lemma lem5804370 {B : Type'} (y : B) (x : B) (z : B) : ((term1275 B y x z) = (term1275 B y x z)) = True.
Proof. exact (@lem5804369 (term1275 B y x z)). Qed.
Lemma lem5804371 {B : Type'} (y : B) (x : B) (z : B) : ((term1253 B x y z) = (term1275 B y x z)) = True.
Proof. exact (TRANS (@lem5804366 B y x z) (@lem5804370 B y x z)). Qed.
Lemma lem5804372 {B : Type'} (y : B) (x : B) (z : B) : True = ((term1253 B x y z) = (term1275 B y x z)).
Proof. exact (SYM (@lem5804371 B y x z)). Qed.
Lemma lem5804373 {B : Type'} (y : B) (x : B) (z : B) : (term1253 B x y z) = (term1275 B y x z).
Proof. exact (EQ_MP (@lem5804372 B y x z) (@lem0)). Qed.
Lemma lem5804374 {B : Type'} (y : B) (x : B) (z : B) : term1275 B y x z.
Proof. exact (EQ_MP (@lem5804373 B y x z) (@lem5804015 B x y z)). Qed.
Lemma lem5804376 (b : Prop) (a : Prop) : (a \/ b) = (term524 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5804377 {B : Type'} (x : B) (y : B) (z : B) : (term1275 B y x z) = (term1278 B x y z).
Proof. exact (@lem5804376 (term1279 B y x z) (y = z)). Qed.
Lemma lem5804379 (a : Prop) (b : Prop) : (term527 a b) = (term528 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5804380 {B : Type'} (y : B) (x : B) (z : B) : (term1280 B y x z) = (term1281 B y x z).
Proof. exact (@lem5804379 (term1272 B x y) (term1272 B x z)). Qed.
Lemma lem5804382 (a : Prop) : (term544 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5804383 {B : Type'} (x : B) (y : B) : (term1282 B x y) = (x = y).
Proof. exact (@lem5804382 (x = y)). Qed.
Lemma lem5804384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5804385 {B : Type'} (x : B) (y : B) : (term1283 B x y) = (term1284 B x y).
Proof. exact (MK_COMB (@lem5804384) (@lem5804383 B x y)). Qed.
Lemma lem5804387 (a : Prop) : (term544 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5804388 {B : Type'} (x : B) (z : B) : (term1282 B x z) = (x = z).
Proof. exact (@lem5804387 (x = z)). Qed.
Lemma lem5804389 {B : Type'} (y : B) (x : B) (z : B) : (term1281 B y x z) = (term1285 B y x z).
Proof. exact (MK_COMB (@lem5804385 B x y) (@lem5804388 B x z)). Qed.
Lemma lem5804390 {B : Type'} (y : B) (x : B) (z : B) : (term1280 B y x z) = (term1285 B y x z).
Proof. exact (TRANS (@lem5804380 B y x z) (@lem5804389 B y x z)). Qed.
Lemma lem5804391 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5804392 {B : Type'} (y : B) (x : B) (z : B) : (term1286 B y x z) = (term1287 B y x z).
Proof. exact (MK_COMB (@lem5804391) (@lem5804390 B y x z)). Qed.
Lemma lem5804393 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5804394 {B : Type'} (x : B) (y : B) (z : B) : (term1278 B x y z) = (term1288 B x y z).
Proof. exact (MK_COMB (@lem5804392 B y x z) (@lem5804393 B y z)). Qed.
Lemma lem5804395 {B : Type'} (x : B) (y : B) (z : B) : (term1275 B y x z) = (term1288 B x y z).
Proof. exact (TRANS (@lem5804377 B x y z) (@lem5804394 B x y z)). Qed.
Lemma lem5804397 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : (@support A B op f s) = (@EMPTY A)) : term1289 A B s f op.
Proof. exact (conj (@lem5804218 A B op s f h1) (@lem5804284 _120521 A B op f s h2 h3 h4)). Qed.
Lemma lem5804399 {B : Type'} (x : B) (y : B) (z : B) : term1288 B x y z.
Proof. exact (EQ_MP (@lem5804395 B x y z) (@lem5804374 B y x z)). Qed.
Lemma lem5804400 {B : Type'} (x : B) (y : B) (z : B) : term1288 B x y z.
Proof. exact (@lem5804399 B x y z). Qed.
Lemma lem5804401 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term1290 A B s f op.
Proof. exact (@lem5804400 B (term973 A B op s f) (term963 A B op s f) (@I ((B -> B -> B) -> B) (@neutral B) op)). Qed.
Lemma lem5804404 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : (@support A B op f s) = (@EMPTY A)) : (term963 A B op s f) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5804401 A B s f op (@lem5804397 _120521 A B op f s h1 h2 h3 h4)). Qed.
Lemma lem5804405 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : (@support A B op f s) = (@EMPTY A)) : term1291 A B s f op.
Proof. exact (fun h0 : term966 A B s f op => @lem5804404 _120521 A B op f s h1 h2 h3 h4). Qed.
Lemma lem5804407 (p : Prop) : (term539 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5804408 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1291 A B s f op) = ((term963 A B op s f) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (@lem5804407 ((term963 A B op s f) = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem5804409 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : (@support A B op f s) = (@EMPTY A)) : (term963 A B op s f) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (EQ_MP (@lem5804408 A B s f op) (@lem5804405 _120521 A B op f s h1 h2 h3 h4)). Qed.
Lemma lem5804412 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5804414 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term966 A B s f op) = (term1292 A B s f op).
Proof. exact (@lem5804412 ((term963 A B op s f) = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem5804417 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term594 A B s f op) : term1292 A B s f op.
Proof. exact (EQ_MP (@lem5804414 A B s f op) (@lem5802257 A B s f op h1)). Qed.
Lemma lem5804420 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : term594 A B s f op) (h5 : (@support A B op f s) = (@EMPTY A)) : False.
Proof. exact (@lem5804417 A B s f op h4 (@lem5804409 _120521 A B op f s h1 h2 h3 h5)). Qed.
Lemma lem5804421 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : term594 A B s f op) (h5 : (@support A B op f s) = (@EMPTY A)) : term589.
Proof. exact (fun h0 : ~ False => @lem5804420 _120521 A B op f s h1 h2 h3 h4 h5). Qed.
Lemma lem5804423 (p : Prop) : (term539 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5804424 : term589 = False.
Proof. exact (@lem5804423 False). Qed.
Lemma lem5804426 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : term594 A B s f op) (h5 : (@support A B op f s) = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem5804424) (@lem5804421 _120521 A B op f s h1 h2 h3 h4 h5)). Qed.
Lemma lem5804427 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : term594 A B s f op) (h5 : (@support A B op f s) = (@EMPTY A)) : (term601 A B) = False.
Proof. exact (prop_ext (fun h6 : term601 A B => @lem5804426 _120521 A B op f s h1 h2 h3 h4 h5) (fun h6 : False => @lem5792454 A B h1)). Qed.
Lemma lem5804428 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : term594 A B s f op) (h5 : (@support A B op f s) = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem5804427 _120521 A B op f s h1 h2 h3 h4 h5) (@lem5792454 A B h1)). Qed.
Lemma lem5804429 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : term594 A B s f op) (h5 : (@support A B op f s) = (@EMPTY A)) : (term594 A B s f op) = False.
Proof. exact (prop_ext (fun h6 : term594 A B s f op => @lem5804428 _120521 A B op f s h1 h2 h3 h4 h5) (fun h6 : False => @lem5792238 A B s f op h4)). Qed.
Lemma lem5804430 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : term594 A B s f op) (h5 : (@support A B op f s) = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem5804429 _120521 A B op f s h1 h2 h3 h4 h5) (@lem5792238 A B s f op h4)). Qed.
Lemma lem5804431 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : term594 A B s f op) (h5 : (@support A B op f s) = (@EMPTY A)) : ((@support A B op f s) = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h6 : (@support A B op f s) = (@EMPTY A) => @lem5804430 _120521 A B op f s h1 h2 h3 h4 h5) (fun h6 : False => @lem5792232 A B op f s h5)). Qed.
Lemma lem5804432 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : term594 A B s f op) (h5 : (@support A B op f s) = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem5804431 _120521 A B op f s h1 h2 h3 h4 h5) (@lem5792232 A B op f s h5)). Qed.
Lemma lem5804433 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : term594 A B s f op) (h5 : (@support A B op f s) = (@EMPTY A)) : (@monoidal B op) = False.
Proof. exact (prop_ext (fun h6 : @monoidal B op => @lem5804432 _120521 A B op f s h1 h2 h3 h4 h5) (fun h6 : False => @lem5792163 B op h3)). Qed.
Lemma lem5804434 {_120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : term594 A B s f op) (h5 : (@support A B op f s) = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem5804433 _120521 A B op f s h1 h2 h3 h4 h5) (@lem5792163 B op h3)). Qed.
Lemma lem5804435 {_120477 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : term594 A B s f op) (h5 : (@support A B op f s) = (@EMPTY A)) : term1293 _120477 _120521 A.
Proof. exact (fun h0 : term719 _120477 _120521 A => @lem5804434 _120521 A B op f s h1 h2 h3 h4 h5). Qed.
Lemma lem5804436 {_120477 _120521 A : Type'} : (term1293 _120477 _120521 A) = (term720 _120477 _120521 A).
Proof. exact (@lem69 (term719 _120477 _120521 A)). Qed.
Lemma lem5804437 {_120477 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : term760 _120521 A B) (h3 : @monoidal B op) (h4 : term594 A B s f op) (h5 : (@support A B op f s) = (@EMPTY A)) : term720 _120477 _120521 A.
Proof. exact (EQ_MP (@lem5804436 _120477 _120521 A) (@lem5804435 _120477 _120521 A B op f s h1 h2 h3 h4 h5)). Qed.
Lemma lem5804438 {_120477 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term762 _120477 _120521 A B.
Proof. exact (fun h0 : term760 _120521 A B => @lem5804437 _120477 _120521 A B op f s h1 h0 h2 h3 h4). Qed.
Lemma lem5804439 {_120477 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term771 _120477 _120521 A B.
Proof. exact (fun h0 : term769 _120477 A B => @lem5804438 _120477 _120521 A B op f s h1 h2 h3 h4). Qed.
Lemma lem5804440 {_120477 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term772 _120477 _120521 A B.
Proof. exact (fun h0 : term769 _120477 _120521 B => @lem5804439 _120477 _120521 A B op f s h1 h2 h3 h4). Qed.
Lemma lem5804441 {_120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term814 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term812 _120519 _120521 A => @lem5804440 _120477 _120521 A B op f s h1 h2 h3 h4). Qed.
Lemma lem5804442 {_120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term823 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term821 _120477 _120519 A => @lem5804441 _120477 _120519 _120521 A B op f s h1 h2 h3 h4). Qed.
Lemma lem5804443 {_120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term830 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term600 A => @lem5804442 _120477 _120519 _120521 A B op f s h1 h2 h3 h4). Qed.
Lemma lem5804444 {_120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term831 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term600 _120521 => @lem5804443 _120477 _120519 _120521 A B op f s h1 h2 h3 h4). Qed.
Lemma lem5804445 {_120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term832 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term600 _120477 => @lem5804444 _120477 _120519 _120521 A B op f s h1 h2 h3 h4). Qed.
Lemma lem5804446 {_120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term839 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term602 _120521 A => @lem5804445 _120477 _120519 _120521 A B op f s h1 h2 h3 h4). Qed.
Lemma lem5804447 {_120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term840 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term602 _120477 A => @lem5804446 _120477 _120519 _120521 A B op f s h1 h2 h3 h4). Qed.
Lemma lem5804448 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term601 A B) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term841 _120308 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term602 _120308 A => @lem5804447 _120477 _120519 _120521 A B op f s h1 h2 h3 h4). Qed.
Lemma lem5804449 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term594 A B s f op) (h3 : (@support A B op f s) = (@EMPTY A)) : term848 _120308 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term601 A B => @lem5804448 _120308 _120477 _120519 _120521 A B op f s h0 h1 h2 h3). Qed.
Lemma lem5804450 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term594 A B s f op) (h3 : (@support A B op f s) = (@EMPTY A)) : term849 _120308 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term601 _120521 B => @lem5804449 _120308 _120477 _120519 _120521 A B op f s h1 h2 h3). Qed.
Lemma lem5804451 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term594 A B s f op) (h3 : (@support A B op f s) = (@EMPTY A)) : term850 _120308 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term601 _120477 B => @lem5804450 _120308 _120477 _120519 _120521 A B op f s h1 h2 h3). Qed.
Lemma lem5804452 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term594 A B s f op) (h3 : (@support A B op f s) = (@EMPTY A)) : term851 _120308 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term601 _120308 B => @lem5804451 _120308 _120477 _120519 _120521 A B op f s h1 h2 h3). Qed.
Lemma lem5804453 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term594 A B s f op) (h3 : (@support A B op f s) = (@EMPTY A)) : term858 _120308 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term603 _120519 A => @lem5804452 _120308 _120477 _120519 _120521 A B op f s h1 h2 h3). Qed.
Lemma lem5804454 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term594 A B s f op) (h3 : (@support A B op f s) = (@EMPTY A)) : term859 _120308 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term603 _120519 _120521 => @lem5804453 _120308 _120477 _120519 _120521 A B op f s h1 h2 h3). Qed.
Lemma lem5804455 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term594 A B s f op) (h3 : (@support A B op f s) = (@EMPTY A)) : term860 _120308 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term601 _120477 _120519 => @lem5804454 _120308 _120477 _120519 _120521 A B op f s h1 h2 h3). Qed.
Lemma lem5804456 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term594 A B s f op) (h3 : (@support A B op f s) = (@EMPTY A)) : term861 _120308 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term601 _120308 _120519 => @lem5804455 _120308 _120477 _120519 _120521 A B op f s h1 h2 h3). Qed.
Lemma lem5804457 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : (@support A B op f s) = (@EMPTY A)) : term862 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (fun h0 : term594 A B s f op => @lem5804456 _120308 _120477 _120519 _120521 A B op f s h1 h0 h2). Qed.
Lemma lem5804458 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term863 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (fun h0 : (@support A B op f s) = (@EMPTY A) => @lem5804457 _120308 _120477 _120519 _120521 A B op f s h1 h0). Qed.
Lemma lem5804459 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term864 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (fun h0 : term0 A B s f op => @lem5804458 _120308 _120477 _120519 _120521 A B s f op h1). Qed.
Lemma lem5804460 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term865 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (fun h0 : @monoidal B op => @lem5804459 _120308 _120477 _120519 _120521 A B s f op h0). Qed.
Lemma lem5804465 {_120308 _120477 _120519 _120521 A B : Type'} (f : A -> B) (op : type1400 B) : term867 _120308 _120477 _120519 _120521 A B f op.
Proof. exact (fun s : A -> Prop => @lem5804460 _120308 _120477 _120519 _120521 A B s f op). Qed.
Lemma lem5804470 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) : term869 _120308 _120477 _120519 _120521 A B op.
Proof. exact (fun f : A -> B => @lem5804465 _120308 _120477 _120519 _120521 A B f op). Qed.
Lemma lem5804475 {_120308 _120477 _120519 _120521 A B : Type'} : term871 _120308 _120477 _120519 _120521 A B.
Proof. exact (fun op : type1400 B => @lem5804470 _120308 _120477 _120519 _120521 A B op). Qed.
Lemma lem5804476 {_120308 _120477 _120519 _120521 A B : Type'} : term675 _120308 _120477 _120519 _120521 A B.
Proof. exact (EQ_MP (@lem5792133 _120308 _120477 _120519 _120521 A B) (@lem5804475 _120308 _120477 _120519 _120521 A B)). Qed.
Lemma lem5804477 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) : term1294 _120308 _120477 _120519 _120521 A B op.
Proof. exact (@lem5804476 _120308 _120477 _120519 _120521 A B op). Qed.
Lemma lem5804478 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) : (term1294 _120308 _120477 _120519 _120521 A B op) = (term671 _120308 _120477 _120519 _120521 A B op).
Proof. exact (eq_refl (term1294 _120308 _120477 _120519 _120521 A B op)). Qed.
Lemma lem5804479 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) : term671 _120308 _120477 _120519 _120521 A B op.
Proof. exact (EQ_MP (@lem5804478 _120308 _120477 _120519 _120521 A B op) (@lem5804477 _120308 _120477 _120519 _120521 A B op)). Qed.
Lemma lem5804480 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) : term1295 _120308 _120477 _120519 _120521 A B op f.
Proof. exact (@lem5804479 _120308 _120477 _120519 _120521 A B op f). Qed.
Lemma lem5804481 {_120308 _120477 _120519 _120521 A B : Type'} (f : A -> B) (op : type1400 B) : (term1295 _120308 _120477 _120519 _120521 A B op f) = (term667 _120308 _120477 _120519 _120521 A B f op).
Proof. exact (eq_refl (term1295 _120308 _120477 _120519 _120521 A B op f)). Qed.
Lemma lem5804482 {_120308 _120477 _120519 _120521 A B : Type'} (f : A -> B) (op : type1400 B) : term667 _120308 _120477 _120519 _120521 A B f op.
Proof. exact (EQ_MP (@lem5804481 _120308 _120477 _120519 _120521 A B f op) (@lem5804480 _120308 _120477 _120519 _120521 A B op f)). Qed.
Lemma lem5804483 {_120308 _120477 _120519 _120521 A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : term1296 _120308 _120477 _120519 _120521 A B f op s.
Proof. exact (@lem5804482 _120308 _120477 _120519 _120521 A B f op s). Qed.
Lemma lem5804484 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1296 _120308 _120477 _120519 _120521 A B f op s) = (term604 _120308 _120477 _120519 _120521 A B s f op).
Proof. exact (eq_refl (term1296 _120308 _120477 _120519 _120521 A B f op s)). Qed.
Lemma lem5804485 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term604 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (EQ_MP (@lem5804484 _120308 _120477 _120519 _120521 A B s f op) (@lem5804483 _120308 _120477 _120519 _120521 A B f op s)). Qed.
Lemma lem5804487 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term604 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (@lem5790107 _120308 _120477 _120519 _120521 A B s f op (@lem5804485 _120308 _120477 _120519 _120521 A B s f op)). Qed.
Lemma lem5804488 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term662 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (@lem5804487 _120308 _120477 _120519 _120521 A B s f op (@lem5783476 B op h1)). Qed.
Lemma lem5804489 {_120308 _120477 _120519 _120521 A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) (h2 : @monoidal B op) : term660 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (@lem5804488 _120308 _120477 _120519 _120521 A B s f op h2 (@lem5783477 A B s f op h1)). Qed.
Lemma lem5804490 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : (@support A B op f s) = (@EMPTY A)) : term657 _120308 _120477 _120519 _120521 A B s f op.
Proof. exact (@lem5804489 _120308 _120477 _120519 _120521 A B s f op h1 h2 (@lem5783478 A B op f s h3)). Qed.
Lemma lem5804491 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term654 _120308 _120477 _120519 _120521 A B.
Proof. exact (@lem5804490 _120308 _120477 _120519 _120521 A B op f s h1 h2 h4 (@lem5790065 A B s f op h3)). Qed.
Lemma lem5804492 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term652 _120308 _120477 _120519 _120521 A B.
Proof. exact (@lem5804491 _120308 _120477 _120519 _120521 A B op f s h1 h2 h3 h4 (@lem5790082 _120308 _120519)). Qed.
Lemma lem5804493 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term650 _120308 _120477 _120519 _120521 A B.
Proof. exact (@lem5804492 _120308 _120477 _120519 _120521 A B op f s h1 h2 h3 h4 (@lem5790090 _120477 _120519)). Qed.
Lemma lem5804494 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term648 _120308 _120477 _120519 _120521 A B.
Proof. exact (@lem5804493 _120308 _120477 _120519 _120521 A B op f s h1 h2 h3 h4 (@lem5790089 _120519 _120521)). Qed.
Lemma lem5804495 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term645 _120308 _120477 _120519 _120521 A B.
Proof. exact (@lem5804494 _120308 _120477 _120519 _120521 A B op f s h1 h2 h3 h4 (@lem5790088 _120519 A)). Qed.
Lemma lem5804496 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term643 _120308 _120477 _120519 _120521 A B.
Proof. exact (@lem5804495 _120308 _120477 _120519 _120521 A B op f s h1 h2 h3 h4 (@lem5790080 _120308 B)). Qed.
Lemma lem5804497 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term641 _120308 _120477 _120519 _120521 A B.
Proof. exact (@lem5804496 _120308 _120477 _120519 _120521 A B op f s h1 h2 h3 h4 (@lem5790087 _120477 B)). Qed.
Lemma lem5804498 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term639 _120308 _120477 _120519 _120521 A B.
Proof. exact (@lem5804497 _120308 _120477 _120519 _120521 A B op f s h1 h2 h3 h4 (@lem5790086 _120521 B)). Qed.
Lemma lem5804499 {_120308 _120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term636 _120308 _120477 _120519 _120521 A B.
Proof. exact (@lem5804498 _120308 _120477 _120519 _120521 A B op f s h1 h2 h3 h4 (@lem5790083 A B)). Qed.
Lemma lem5804500 {_120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term634 _120477 _120519 _120521 A B.
Proof. exact (@lem5804499 Prop _120477 _120519 _120521 A B op f s h1 h2 h3 h4 (@lem5790081 Prop A)). Qed.
Lemma lem5804501 {_120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term632 _120477 _120519 _120521 A B.
Proof. exact (@lem5804500 _120477 _120519 _120521 A B op f s h1 h2 h3 h4 (@lem5790084 _120477 A)). Qed.
Lemma lem5804502 {_120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term629 _120477 _120519 _120521 A B.
Proof. exact (@lem5804501 _120477 _120519 _120521 A B op f s h1 h2 h3 h4 (@lem5790085 _120521 A)). Qed.
Lemma lem5804503 {_120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term627 _120477 _120519 _120521 A B.
Proof. exact (@lem5804502 _120477 _120519 _120521 A B op f s h1 h2 h3 h4 (@lem5790077 _120477)). Qed.
Lemma lem5804504 {_120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term625 _120477 _120519 _120521 A B.
Proof. exact (@lem5804503 _120477 _120519 _120521 A B op f s h1 h2 h3 h4 (@lem5790074 _120521)). Qed.
Lemma lem5804505 {_120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term622 _120477 _120519 _120521 A B.
Proof. exact (@lem5804504 _120477 _120519 _120521 A B op f s h1 h2 h3 h4 (@lem5790075 A)). Qed.
Lemma lem5804506 {_120477 _120519 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term619 _120477 _120519 _120521 A B.
Proof. exact (@lem5804505 _120477 _120519 _120521 A B op f s h1 h2 h3 h4 (@lem5790073 _120477 _120519 A)). Qed.
Lemma lem5804507 {_120477 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term616 _120477 _120521 A B.
Proof. exact (@lem5804506 _120477 Prop _120521 A B op f s h1 h2 h3 h4 (@lem5790070 Prop _120521 A)). Qed.
Lemma lem5804508 {_120477 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term614 _120477 _120521 A B.
Proof. exact (@lem5804507 _120477 _120521 A B op f s h1 h2 h3 h4 (@lem5790066 _120477 _120521 B)). Qed.
Lemma lem5804509 {_120477 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term611 _120477 _120521 A B.
Proof. exact (@lem5804508 _120477 _120521 A B op f s h1 h2 h3 h4 (@lem5790072 _120477 A B)). Qed.
Lemma lem5804510 {_120477 _120521 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : term608 _120477 _120521 A.
Proof. exact (@lem5804509 _120477 _120521 A B op f s h1 h2 h3 h4 (@lem5790069 _120521 A B)). Qed.
Lemma lem5804511 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : False.
Proof. exact (@lem5804510 Prop Prop A B op f s h1 h2 h3 h4 (@lem5790068 Prop Prop A)). Qed.
Lemma lem5804512 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : (term594 A B s f op) = False.
Proof. exact (prop_ext (fun h5 : term594 A B s f op => @lem5804511 A B op f s h1 h2 h3 h4) (fun h5 : False => @lem5790065 A B s f op h3)). Qed.
Lemma lem5804513 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : term594 A B s f op) (h4 : (@support A B op f s) = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem5804512 A B op f s h1 h2 h3 h4) (@lem5790065 A B s f op h3)). Qed.
Lemma lem5804514 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : (@support A B op f s) = (@EMPTY A)) : term593 A B s f op.
Proof. exact (fun h0 : term594 A B s f op => @lem5804513 A B op f s h1 h2 h0 h3). Qed.
Lemma lem5804515 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : (@support A B op f s) = (@EMPTY A)) : (@iterate B A op s f) = (@neutral B op).
Proof. exact (EQ_MP (@lem5790064 A B s f op) (@lem5804514 A B op f s h1 h2 h3)). Qed.
Lemma lem5804516 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : (@support A B op f s) = (@EMPTY A)) : ((@support A B op f s) = (@EMPTY A)) = ((@iterate B A op s f) = (@neutral B op)).
Proof. exact (prop_ext (fun h4 : (@support A B op f s) = (@EMPTY A) => @lem5804515 A B op f s h1 h2 h3) (fun h4 : (@iterate B A op s f) = (@neutral B op) => @lem5783478 A B op f s h3)). Qed.
Lemma lem5804517 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term0 A B s f op) (h2 : @monoidal B op) (h3 : (@support A B op f s) = (@EMPTY A)) : (@iterate B A op s f) = (@neutral B op).
Proof. exact (EQ_MP (@lem5804516 A B op f s h1 h2 h3) (@lem5783478 A B op f s h3)). Qed.
Lemma lem5804518 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) (h2 : @monoidal B op) : ((@support A B op f s) = (@EMPTY A)) = ((@iterate B A op s f) = (@neutral B op)).
Proof. exact (prop_ext (fun h3 : (@support A B op f s) = (@EMPTY A) => @lem5804517 A B op f s h1 h2 h3) (fun h3 : (@iterate B A op s f) = (@neutral B op) => @lem5790060 A B s f op h1 h2)). Qed.
Lemma lem5804519 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) (h2 : @monoidal B op) : (@iterate B A op s f) = (@neutral B op).
Proof. exact (EQ_MP (@lem5804518 A B s f op h1 h2) (@lem5790060 A B s f op h1 h2)). Qed.
Lemma lem5804520 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) (h2 : @monoidal B op) : (term0 A B s f op) = ((@iterate B A op s f) = (@neutral B op)).
Proof. exact (prop_ext (fun h3 : term0 A B s f op => @lem5804519 A B s f op h1 h2) (fun h3 : (@iterate B A op s f) = (@neutral B op) => @lem5783477 A B s f op h1)). Qed.
Lemma lem5804521 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term0 A B s f op) (h2 : @monoidal B op) : (@iterate B A op s f) = (@neutral B op).
Proof. exact (EQ_MP (@lem5804520 A B s f op h1 h2) (@lem5783477 A B s f op h1)). Qed.
Lemma lem5804522 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term1297 A B s f op.
Proof. exact (fun h0 : term0 A B s f op => @lem5804521 A B s f op h0 h1). Qed.
Lemma lem5804527 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term1298 A B f op.
Proof. exact (fun s : A -> Prop => @lem5804522 A B s f op h1). Qed.
Lemma lem5804532 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term1299 A B op.
Proof. exact (fun f : A -> B => @lem5804527 A B f op h1). Qed.
Lemma lem5804533 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = (term1299 A B op).
Proof. exact (prop_ext (fun h2 : @monoidal B op => @lem5804532 A B op h1) (fun h2 : term1299 A B op => @lem5783476 B op h1)). Qed.
Lemma lem5804534 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term1299 A B op.
Proof. exact (EQ_MP (@lem5804533 A B op h1) (@lem5783476 B op h1)). Qed.
Lemma lem5804535 {A B : Type'} (op : type1400 B) : term1300 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem5804534 A B op h0). Qed.
Lemma lem5804540 {A B : Type'} : term1301 A B.
Proof. exact (fun op : type1400 B => @lem5804535 A B op). Qed.
