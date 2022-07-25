import data.real.basic
import group_theory.finiteness
import algebra.group.defs

noncomputable theory

open set
open group
open subgroup
open add_group

-- Let G be a group and S the set of representants of G/mG
variables {G : Type*} [add_comm_group G]

def fin_quotient (S : set G) [finite S] (m : ℕ) := -- m ≥ 2
  ∀ g₀ : G, ∃ s ∈ S, ∃ g : G, g₀ = g + m•s

variables {S : set G} (hS_fin : finite S) (hS_ne : S.nonempty)

-- Heights formulated with a general m
class height (ht : G → ℝ) :=
-- (nonneg : ∀ g : G, 0 ≤ ht g)
(C₁ : G → ℝ)
(upper_bound : ∀ g₀ : G, ∀ g : G, ht(g + g₀) ≤ 2*ht g  + C₁ g₀)
(m : ℕ) (Hm : m ≥ 2)
(C₂ : ℝ)
(lower_bound : ∀ g : G, ht (m•g) ≥ (m^2)*(ht g) - C₂)
(finite_boxes : ∀ C₃ : ℝ, {g : G | ht g ≤ C₃}.finite)

variables (ht : G → ℝ) [height ht]
variables (hfinquot : fin_quotient S (height.m ht))

lemma Rnonempty [fintype S] (hS : S.nonempty) {f : G → ℝ}: (f '' S).to_finset.nonempty :=
begin
obtain ⟨x, hx⟩ := hS,
use f x,
finish,
end

-- let C := max{C₁ Q | Q : S} + max 0 C₂
def C [fintype S] (hS : S.nonempty) (h : fin_quotient S (height.m ht)) : ℝ :=
  ((height.C₁ ht ''S).to_finset.max' (Rnonempty hS)) + max 0 (height.C₂ ht)

-- variable {Cₛ : ℝ} [(C ht S.hs_ne h) Cₛ]   

-- If P∈S, then C₁ P ≤ C
lemma C₁S_le_C [fintype S] (hS : S.nonempty) (h : fin_quotient S (height.m ht))
(P : G) (hP : P ∈ S) : (height.C₁ ht P) ≤ (C ht hS h) :=
begin
  calc 
  (height.C₁ ht P) ≤ (height.C₁ ht '' S).to_finset.max' (Rnonempty hS) : by {
    apply finset.le_max',
    simp,
    use P,
    tauto,
  }
  ... ≤ (height.C₁ ht '' S).to_finset.max' (Rnonempty hS) + max 0 (height.C₂ ht) : by {
    have H : 0 ≤ max 0 (height.C₂ ht), by simp,
    linarith,
  }
end

-- lemma C₂_le_C [fintype S] (hS : S.nonempty) (h : fin_quotient S (height.m ht)) :
--   (height.C₂ ht) ≤ (C ht hS h) :=
-- begin
--   sorry
-- end


-- This C has two important properties that combine C₁ and C₂
lemma useful_C [fintype S] (hS : S.nonempty) (h : fin_quotient S (height.m ht)) (g g₀ : G) (hg₀ : g₀ ∈ S) :
(ht (g - g₀) ≤ 2*(ht g) + (C ht hS h))
:=
begin
  -- calc 
  -- ht (g - g₀) ≤ 2*(ht g) + height.C₁ ht g₀ : by {
  --   have H := (ht.upper_bound),
  --   sorry
  -- }
  -- ... ≤ 2*(ht g) + (C ht hS h) : by linarith [C₁S_le_C ht hS h g₀ hg₀],
  sorry
end

lemma useful_C' [fintype S] (hS : S.nonempty) (h : fin_quotient S (height.m ht)) (g₀ : S) (g : G) :
(∀ g : G, ht ((height.m ht)•g) ≥ ((height.m ht)^2)*(ht g) + (C ht hS h))
:=
begin
  sorry
end

-- Set of generators: S ∪ {g : G | ht g ≤ C}
def U [fintype S] (hS : S.nonempty) (h : fin_quotient S (height.m ht)) : set G :=
begin
  exact S ∪ {g : G | ht g ≤ (C ht hS h)},
end


def seq_P (P : G) [fintype S] (hS : S.nonempty) (h : fin_quotient S (height.m ht)) : ℕ → G 
| 0 := P
| (n+1) := P
  -- Idea de la seqüencia:
  -- seq_P 0 = P
  -- seq_P succ n := el Q : G tal que seq_P n - Qₐ{iₙ} = mQ



-- Falta lemma diferents altures => diferents punts ?
-- Falten lemmes que reescriuen les desigualtats com s'utilitzen

lemma elem_with_height_less_C [fintype S] (hS : S.nonempty) (h : fin_quotient S (height.m ht)) (P : G) 
(seq : ℕ → G) :
∃ (Pᵢ : G), ∃ (n : ℕ), (seq_P ht P hS h) n = Pᵢ ∧ ht Pᵢ ≤ (C ht hS h) :=
begin
  sorry

  -- Idea de la demo:
  -- Suposem el contrari
  -- Llavors per les desigualtats veiem que l'altura es va fent petita (altres lemmes?)
  -- Dir que tots els punts son diferents
  -- Dir que el conjunt de punts amb altura  ≤ ht P és infinit
  -- Arribem a contradicció 
end


-- Descent theorem
lemma main_theorem (S : set G) [finite S] (m : ℕ) (Hm : m ≥ 2) (h : fin_quotient S m) 
(ht : G → ℝ) [height ht] : 
fg G :=
begin
  rw add_group.fg_iff,

  use S,
  split,


  

  
  -- Usar el lema usefull_C per obtenir la C
  -- Donar el subconjunt generador S ∪ {g : G | ht g ≤ C} (per propietats és finit)
  -- A partir d'aquí no entenc com funciona...
  -- Donat un P
  -- Definim la seq. {P_j} (amb les seves definicions/hipotesis) 
  -- Veiem que dins de la seq. hi ha elements d'altura ≤ C, diem-li Pⱼ
  -- S'ha d veure que podem escriure P com a combinació de Qᵢ i algun Pⱼ
  -- Ho usem pel Pⱼ que té altura ≤ C
  
  sorry
end
