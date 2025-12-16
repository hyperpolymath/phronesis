# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.State do
  @moduledoc """
  State model for the Phronesis interpreter.

  Based on the formal operational semantics:

      State = (PolicyTable, ConsensusLog, Environment, PendingActions)

      where:
        PolicyTable    : Map<PolicyID, Policy>
        ConsensusLog   : List<(Action, Votes, Timestamp)>
        Environment    : Map<Variable, Value>
        PendingActions : Queue<Action>

  ## Consensus Safety

  Per Rule 2 (ACTION-EXECUTE) in the operational semantics:

  > An action executes only if consensus approves it, and it's logged immutably.

  The state enforces this invariant by requiring consensus approval before
  any action can be executed.

  ## Non-Repudiation

  Every executed action appears in the ConsensusLog with:
  - The action itself
  - Vote results from all agents
  - Timestamp of execution

  This ensures full auditability.
  """

  alias Phronesis.AST

  defstruct [
    :policy_table,
    :consensus_log,
    :environment,
    :pending_actions,
    :agents,
    :consensus_threshold,
    :modules
  ]

  @type policy_id :: String.t()
  @type vote :: boolean()
  @type agent_id :: String.t()
  @type votes :: %{agent_id() => vote()}
  @type timestamp :: DateTime.t()

  @type log_entry :: %{
          action: AST.action(),
          votes: votes(),
          timestamp: timestamp(),
          result: :approved | :rejected
        }

  @type t :: %__MODULE__{
          policy_table: %{policy_id() => AST.policy()},
          consensus_log: [log_entry()],
          environment: map(),
          pending_actions: :queue.queue(AST.action()),
          agents: [agent_id()],
          consensus_threshold: float(),
          modules: map()
        }

  @default_threshold 0.51

  @doc """
  Create a new execution state.

  ## Options

  - `:consensus_threshold` - Required vote percentage (default: 0.51)
  - `:agents` - List of agent IDs for consensus voting (default: ["local"])
  - `:environment` - Initial variable bindings (default: %{})
  """
  @spec new(keyword()) :: t()
  def new(opts \\ []) do
    %__MODULE__{
      policy_table: %{},
      consensus_log: [],
      environment: Keyword.get(opts, :environment, %{}),
      pending_actions: :queue.new(),
      agents: Keyword.get(opts, :agents, ["local"]),
      consensus_threshold: Keyword.get(opts, :consensus_threshold, @default_threshold),
      modules: %{}
    }
  end

  @doc """
  Register a policy in the policy table.
  """
  @spec register_policy(t(), AST.policy()) :: t()
  def register_policy(%__MODULE__{} = state, {:policy, name, _, _, _} = policy) do
    %{state | policy_table: Map.put(state.policy_table, name, policy)}
  end

  @doc """
  Get a policy by ID.
  """
  @spec get_policy(t(), policy_id()) :: {:ok, AST.policy()} | :error
  def get_policy(%__MODULE__{policy_table: table}, id) do
    case Map.fetch(table, id) do
      {:ok, policy} -> {:ok, policy}
      :error -> :error
    end
  end

  @doc """
  Bind a variable in the environment.
  """
  @spec bind(t(), String.t(), any()) :: t()
  def bind(%__MODULE__{} = state, name, value) do
    %{state | environment: Map.put(state.environment, name, value)}
  end

  @doc """
  Look up a variable in the environment.
  """
  @spec lookup(t(), String.t()) :: {:ok, any()} | :error
  def lookup(%__MODULE__{environment: env}, name) do
    Map.fetch(env, name)
  end

  @doc """
  Queue an action for consensus voting.

  Per operational semantics, actions must go through consensus before execution.
  """
  @spec queue_action(t(), AST.action()) :: t()
  def queue_action(%__MODULE__{pending_actions: queue} = state, action) do
    %{state | pending_actions: :queue.in(action, queue)}
  end

  @doc """
  Get the next pending action.
  """
  @spec next_pending_action(t()) :: {:ok, AST.action(), t()} | :empty
  def next_pending_action(%__MODULE__{pending_actions: queue} = state) do
    case :queue.out(queue) do
      {{:value, action}, new_queue} ->
        {:ok, action, %{state | pending_actions: new_queue}}

      {:empty, _} ->
        :empty
    end
  end

  @doc """
  Check if consensus is achieved for an action.

  Per Rule 5 (CONSENSUS-VOTE):

      consensus_approved(action, threshold) =
        (count(votes == true) / |agents|) >= threshold
  """
  @spec consensus_approved?(votes(), [agent_id()], float()) :: boolean()
  def consensus_approved?(votes, agents, threshold) do
    total = length(agents)

    if total == 0 do
      true
    else
      approved_count = Enum.count(votes, fn {_agent, vote} -> vote == true end)
      approved_count / total >= threshold
    end
  end

  @doc """
  Log an action execution to the consensus log.

  Per Rule 2 (ACTION-EXECUTE), state transition includes:

      ConsensusLog' = ConsensusLog ++ [(action, votes, timestamp)]

  This happens atomically before action execution to ensure non-repudiation.
  """
  @spec log_action(t(), AST.action(), votes(), :approved | :rejected) :: t()
  def log_action(%__MODULE__{consensus_log: log} = state, action, votes, result) do
    entry = %{
      action: action,
      votes: votes,
      timestamp: DateTime.utc_now(),
      result: result
    }

    %{state | consensus_log: [entry | log]}
  end

  @doc """
  Register a module implementation.
  """
  @spec register_module(t(), [String.t()], module()) :: t()
  def register_module(%__MODULE__{modules: modules} = state, path, impl) do
    key = Enum.join(path, ".")
    %{state | modules: Map.put(modules, key, impl)}
  end

  @doc """
  Look up a module by path.
  """
  @spec lookup_module(t(), [String.t()]) :: {:ok, module()} | :error
  def lookup_module(%__MODULE__{modules: modules}, path) do
    key = Enum.join(path, ".")
    Map.fetch(modules, key)
  end

  @doc """
  Get all policies sorted by priority (highest first).
  """
  @spec policies_by_priority(t()) :: [AST.policy()]
  def policies_by_priority(%__MODULE__{policy_table: table}) do
    table
    |> Map.values()
    |> Enum.sort_by(fn {:policy, _, _, _, %{priority: p}} -> -p end)
  end
end
