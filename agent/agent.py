import argparse
import asyncio
from claude_agent_sdk import (
    query,
    ClaudeAgentOptions,
    AssistantMessage,
    ResultMessage,
    SystemMessage,
    UserMessage,
    ToolUseBlock,
    ToolResultBlock,
    TextBlock,
    ThinkingBlock,
)

DEFAULT_PROJECT_DIR = "/home/zicon/xpaxos/consensus_rocq"
DEFAULT_PROTOCOL_NAME = "EPaxos"
DEFAULT_PAPER_PATH = "/home/zicon/xpaxos/papers/epaxos.pdf"
DEFAULT_OUTPUT_FILE = "EPaxos.v"
DEFAULT_MODEL = "claude-opus-4-8"

PROMPT_TEMPLATE = r"""
You are working in the Rocq/Coq project directory:

`__PROJECT_DIR__`

Your task is to implement a fast-path adopt-commit abstraction for the distributed consensus protocol named:

`__PROTOCOL_NAME__`

The protocol paper is located at:

`__PAPER_PATH__`

The target output file is:

`__OUTPUT_FILE__`

Correctness of the formal model matters more than merely making `make` succeed.

A compiling file that is just a renamed copy of an existing implementation is not acceptable.
A file that uses `Admitted`, `admit`, or `Axiom` is not complete.

## Scope

This task is NOT to formalize the full protocol from the paper.

The goal is similar in scope to `FastPaxos.v`: implement a small adopt-commit instantiation that captures the protocol's fast-path quorum idea and proves the same four high-level framework properties.

Implement and prove ONLY the fast path.

Do NOT model:

- Accept phase
- AcceptReply phase
- slow path fallback
- full recovery protocol
- multi-instance execution
- dependency graph execution
- liveness
- performance optimizations

It is acceptable and expected that `__OUTPUT_FILE__` is not a complete formalization of `__PROTOCOL_NAME__`.

At the top of `__OUTPUT_FILE__`, include a comment saying clearly:

```coq
(*
  This file formalizes only a fast-path __PROTOCOL_NAME__-style
  adopt-commit abstraction.

  It is NOT a full formalization of __PROTOCOL_NAME__.

  Modeled:
  - one command/value proposed through a fast-path quorum
  - the protocol's fast-path quorum-intersection idea
  - adopt-commit-level Validity, Agreement, Convergence, and Recoverability

  Not modeled:
  - slow path
  - Accept / AcceptReply
  - recovery protocol
  - multi-instance execution
  - dynamic dependency graph execution
  - liveness or performance behavior
*)
```

## Important project files

The project directory contains:

- `AdoptCommit.v`: this file models the adopt-commit abstraction and the arbitrary executions allowed by asynchronous networks. It defines `ACProtocol`, `Reachable`, and high-level properties such as Validity, Agreement, Convergence, and Recoverability.
- `FastPaxos.v`: this file instantiates the adopt-commit model with the fast path of FastPaxos and proves its safety and recoverability. Use it as the main proof-structure reference for this task.
- `Makefile`: builds the project using `rocq compile`.

Network model (from `AdoptCommit.v`): messages between each (src, dst) pair are delivered in FIFO order and are never duplicated or reordered. Message loss is modeled as non-delivery — the `step` relation is a no-op when the queue is empty. Do NOT add duplication, reordering, or replay logic to `acp_step_fn`.

Type convention (from `AdoptCommit.v`): `ProcessId := nat` serves as both process identifier and proposed value. Each proposer proposes its own ID. Do not introduce a separate value type — doing so will be incompatible with the framework's `ACOutput` and property definitions.

Your new file `__OUTPUT_FILE__` should follow the same level of abstraction as `FastPaxos.v`: it should model only the fast path of `__PROTOCOL_NAME__` within the adopt-commit framework, rather than the full protocol.

## Step 1 — Enter the project directory

Run:

```bash
cd __PROJECT_DIR__
pwd
ls -lh
```

## Step 2 — Read the protocol paper

Read the protocol paper directly using the `Read` tool:

`__PAPER_PATH__`

Use the paper only to identify the protocol's fast-path quorum intuition and fast-path decision rule.

Do not attempt to model the whole protocol.

From the paper, extract only the fast-path mechanisms that matter for this abstraction:

1. system model
2. replicas or processes
3. proposers or command leaders, if any
4. proposed values or commands
5. fast-path message pattern
6. fast-path commit or decision condition
7. fast quorum size
8. quorum-intersection requirement
9. failure assumptions
10. the safety property relevant to the fast path

Before writing any Coq code, create a top-level design note in `__OUTPUT_FILE__` explaining how the paper's fast path is mapped into the available adopt-commit framework.

## Step 3 — Read the existing Coq framework

Read:

```bash
AdoptCommit.v
FastPaxos.v
Makefile
```

Use `FastPaxos.v` as the main proof-structure template.

Determine:

1. What `ACProtocol` allows a protocol to define.
2. What the global and local states look like.
3. What the step function can express.
4. What the existing properties mean:
   - Validity
   - Agreement
   - Convergence
   - Recoverability
5. How `FastPaxos.v` proves these four properties.

The new `__OUTPUT_FILE__` should have a similar level of abstraction to `FastPaxos.v`.

## Step 4 — Implement a fast-path-only abstraction

Write:

```bash
__PROJECT_DIR__/__OUTPUT_FILE__
```

Note that write the file in segments, writing every 80 lines at a time.

The model should be intentionally simple:

- message type similar to `FastPaxos.v`, but protocol-specific
- local state similar to `FastPaxos.v`, but protocol-specific
- one accepted command/value per process
- a list of fast-path acknowledgments or acceptors
- output is `Some (Commit v)` only when a fast quorum is reached
- no `Adopt`
- no `Accept`
- no `AcceptReply`
- no slow-path state
- no slow-path messages

You may include simplified protocol-specific metadata, such as dependencies or sequence numbers, only if they do not make the proof significantly more complex.

Important:
If the current `ACOutput` type cannot express metadata such as attributes, dependencies, sequence numbers, or execution order, do not claim to prove metadata agreement.
Instead, state clearly that this adopt-commit abstraction proves agreement only on the committed value.

Use names prefixed by `__PROTOCOL_NAME__` or a suitable lowercase abbreviation.

Do not simply rename an existing implementation. You may reuse proof structure and lemma ideas from `FastPaxos.v`, but the top comment must explain the protocol-specific fast-path mapping.

Output stability: the framework does NOT enforce that a process's output is stable once set (this is a known limitation noted in `AdoptCommit.v`). You must design `acp_step_fn` so that once a process reaches a commit state, its local state never transitions to produce a different output. The standard pattern is to make the commit state absorbing: any message received in that state leaves the local state unchanged.

## Step 5 — Fast quorum

Derive the fast quorum size from the paper.

Do not invent quorum formulas.

Do not implement separate slow quorum, classic quorum, or Accept quorum.

For this fast-path-only abstraction, the main required property is quorum intersection, for example:

```coq
n < 2 * fast_quorum
```

or an equivalent lemma sufficient to prove Agreement.

Be careful with integer division and ceiling/floor behavior.

If the paper uses a ceiling-style expression, encode it explicitly or use a stronger integer formula with a comment explaining the relationship.

Use helper lemmas and arithmetic tactics as in `FastPaxos.v`, including `lia`, `Nat.div_mod`, and `Nat.mod_upper_bound` if needed.

The framework provides only `f_lt_n : f < n` as its base hypothesis. The comment in `AdoptCommit.v` notes that liveness would require `2 * f < n`, but safety proofs only have `f_lt_n` available by default. If the fast quorum formula for `__PROTOCOL_NAME__` requires a stronger assumption (e.g., `n = 2 * f + 1` for EPaxos and SwiftPaxos), add it as an explicit `Hypothesis` in your file and justify it with a reference to the paper.

If extra assumptions on `n` and `f` are required, state them explicitly and justify them in comments.

Do not silently add arbitrary assumptions merely to make proofs pass.

## Step 6 — Prove the four framework properties

Prove the same four theorem names, adapted to `__PROTOCOL_NAME__`:

```coq
__PROTOCOL_NAME___Validity
__PROTOCOL_NAME___Agreement
__PROTOCOL_NAME___Convergence
__PROTOCOL_NAME___Recoverability
```

These theorems should be interpreted at the adopt-commit abstraction level.

Important:

- `__PROTOCOL_NAME___Validity` should show that every output value (Commit or Adopt) was proposed by a valid proposer.
- `__PROTOCOL_NAME___Agreement` should show that if any process commits v, then every process that produces any output (Commit OR Adopt) must output v. This is stronger than "two commits agree" — it constrains Adopt outputs as well.
- `__PROTOCOL_NAME___Convergence` should use the uniqueness of valid proposer values as in the framework: with a unique proposer, every terminating process must Commit (Adopt is not acceptable).
- `__PROTOCOL_NAME___Recoverability` captures the precise property defined in `AdoptCommit.v`: for any two reachable states s and s' that agree on the local states of at least n-f processes, if s has a Commit of v and s' has a Commit of w, then v = w. Intuitively, this means the fast-path quorum must be large enough that any n-f survivors retain enough evidence to rule out a conflicting commit — which is what makes safe adoption possible in any subsequent recovery phase.
- If Recoverability cannot be proved with the chosen assumptions, strengthen and document the assumptions explicitly, but do not silently add arbitrary assumptions.

## Step 7 — Absolutely no admitted proofs

Do not use any of the following under any circumstance:

```coq
Admitted.
admit.
Axiom
```

If a theorem cannot be proved in the current framework, do not state it with `Admitted`.
Instead, either:
1. fix the model and supporting lemmas until the theorem is provable, or
2. replace the theorem with a clearly documented comment explaining why the current framework is insufficient.

After editing, run:

```bash
grep -RInE '\bAdmitted\b|\badmit\b|\bAxiom\b' __OUTPUT_FILE__
```

If this command prints anything, the task is not complete.

## Step 8 — Update the Makefile and compile

Add `__OUTPUT_FILE__` to the `Makefile` after the existing protocol files.

For example:

```make
$(ROCQC) __OUTPUT_FILE__
```

Then run:

```bash
make
```

If compilation fails:

1. Read the error carefully.
2. Fix the actual code or proof error.
3. Run `make` again.
4. Repeat until both conditions hold:
   - `make` succeeds
   - the grep command for `Admitted`, `admit`, and `Axiom` prints nothing

Do not hide proof failures by weakening the model without justification.

## Step 9 — Final audit report

After success, print a concise final report containing:

1. whether `make` succeeded
2. whether `__OUTPUT_FILE__` is fast-path-only
3. the fast quorum formula used
4. the extra assumptions on `n` and `f`, if any
5. which properties were proved
6. confirmation that no `Admitted`, `admit`, or `Axiom` remains
7. the final list of changed files
8. a clear statement that this is not a full formalization of `__PROTOCOL_NAME__`

Remember: the goal is not only to pass `make`; the goal is to build a small, honest, fast-path-only, paper-grounded adopt-commit model similar in scope to `FastPaxos.v`.
"""



def build_prompt(project_dir: str, protocol_name: str, paper_path: str, output_file: str) -> str:
    """Build the agent prompt without using str.format.

    We intentionally use string replacement instead of str.format so that Coq,
    Markdown, and shell snippets containing braces cannot break prompt rendering.
    """
    return (
        PROMPT_TEMPLATE
        .replace("__PROJECT_DIR__", project_dir)
        .replace("__PROTOCOL_NAME__", protocol_name)
        .replace("__PAPER_PATH__", paper_path)
        .replace("__OUTPUT_FILE__", output_file)
    )


def _truncate_text(text: str, max_chars: int = 6000) -> str:
    """Avoid flooding the terminal with huge outputs."""
    if len(text) <= max_chars:
        return text
    return text[:max_chars] + f"\n... [truncated {len(text) - max_chars} chars]"


def _stringify_tool_content(content) -> str:
    """Convert ToolResultBlock.content into printable text.

    Depending on SDK/tool versions, content may be:
    - str
    - list[dict], often with {"type": "text", "text": "..."}
    - None
    - another structured object
    """
    if content is None:
        return ""

    if isinstance(content, str):
        return content

    if isinstance(content, list):
        parts = []
        for item in content:
            if isinstance(item, dict):
                if item.get("type") == "text":
                    parts.append(str(item.get("text", "")))
                else:
                    parts.append(repr(item))
            else:
                parts.append(repr(item))
        return "\n".join(parts)

    return repr(content)


def print_block(
    block,
    *,
    source: str = "unknown",
    show_thinking: bool = False,
    show_tool_results: bool = True,
    max_tool_result_chars: int = 6000,
) -> bool:
    """Print one content block.

    The SDK message is a container. What matters in the terminal is the block:
    - AssistantMessage usually contains TextBlock or ToolUseBlock.
    - UserMessage often contains ToolResultBlock.

    Returns True if visible output was printed.
    """
    if isinstance(block, TextBlock):
        text = block.text.strip()
        if not text:
            return False
        prefix = "Assistant -> text:" if source == "assistant" else "User/tool -> text:"
        print(f"\n{prefix}", flush=True)
        print(text, flush=True)
        return True

    if isinstance(block, ToolUseBlock):
        print(f"\nAssistant -> tool call: {block.name}", flush=True)
        print(block.input, flush=True)
        return True

    if isinstance(block, ToolResultBlock):
        if not show_tool_results:
            return False

        content = _stringify_tool_content(block.content).strip()
        if not content:
            return False

        is_error = bool(getattr(block, "is_error", False))
        prefix = "Tool result: ERROR" if is_error else "Tool result:"
        print(f"\n{prefix}", flush=True)
        print(_truncate_text(content, max_tool_result_chars), flush=True)
        return True

    if isinstance(block, ThinkingBlock):
        if not show_thinking:
            return False
        thinking = block.thinking.strip()
        if not thinking:
            return False
        print("\nAssistant -> thinking:", flush=True)
        print(_truncate_text(thinking, max_tool_result_chars), flush=True)
        return True

    # Future-proof handling for SDK block types not imported by this script.
    block_type = type(block).__name__

    if block_type == "ServerToolUseBlock":
        name = getattr(block, "name", "unknown")
        input_data = getattr(block, "input", None)
        print(f"\nAssistant -> server tool call: {name}", flush=True)
        if input_data is not None:
            print(input_data, flush=True)
        return True

    if block_type == "ServerToolResultBlock":
        content = getattr(block, "content", None)
        text = _stringify_tool_content(content).strip()
        if not text:
            return False
        print("\nServer tool result:", flush=True)
        print(_truncate_text(text, max_tool_result_chars), flush=True)
        return True

    print(f"\nUnknown block ({block_type}) from {source}:", flush=True)
    print(repr(block), flush=True)
    return True


def _has_visible_content(
    content,
    *,
    show_thinking: bool,
    show_tool_results: bool,
) -> bool:
    """Check visibility before printing anything for a message."""
    if content is None:
        return False

    if isinstance(content, str):
        return bool(content.strip())

    if isinstance(content, list):
        for block in content:
            if isinstance(block, TextBlock) and block.text.strip():
                return True
            if isinstance(block, ToolUseBlock):
                return True
            if isinstance(block, ToolResultBlock) and show_tool_results:
                return bool(_stringify_tool_content(block.content).strip())
            if isinstance(block, ThinkingBlock) and show_thinking:
                return bool(block.thinking.strip())

            if type(block).__name__ in {"ServerToolUseBlock", "ServerToolResultBlock"}:
                return True

        return False

    return True


def print_message(
    message,
    *,
    show_thinking: bool = False,
    show_tool_results: bool = True,
    max_tool_result_chars: int = 6000,
) -> None:
    """Pretty-print Claude Agent SDK messages without confusing nested headers.

    We intentionally do NOT print generic headers like "[assistant message]".

    In the SDK:
    - AssistantMessage is a container that may contain TextBlock, ToolUseBlock,
      or ThinkingBlock.
    - UserMessage may contain ToolResultBlock. Therefore we should not drop all
      UserMessage values, or tool results disappear.

    Suppressed by default:
    - SystemMessage bookkeeping, such as thinking token events
    - RateLimitEvent bookkeeping
    - ThinkingBlock content, unless show_thinking=True
    """
    message_type = type(message).__name__

    # Noisy SDK bookkeeping.
    if isinstance(message, SystemMessage) or message_type == "RateLimitEvent":
        return

    if isinstance(message, ResultMessage):
        print(f"\nAgent finished: {message.subtype}", flush=True)

        is_error = bool(getattr(message, "is_error", False))
        if is_error:
            print("Result status: ERROR", flush=True)

        result = getattr(message, "result", None)
        if result:
            print(_truncate_text(str(result), max_tool_result_chars), flush=True)

        errors = getattr(message, "errors", None)
        if errors:
            print("\nErrors:", flush=True)
            print(errors, flush=True)

        return

    content = getattr(message, "content", None)

    if not _has_visible_content(
        content,
        show_thinking=show_thinking,
        show_tool_results=show_tool_results,
    ):
        return

    if isinstance(message, AssistantMessage):
        source = "assistant"
    elif isinstance(message, UserMessage):
        source = "user"
    else:
        source = message_type

    if isinstance(content, str):
        text = content.strip()
        if text:
            prefix = "Assistant -> text:" if source == "assistant" else f"{source} -> text:"
            print(f"\n{prefix}", flush=True)
            print(text, flush=True)
        return

    if isinstance(content, list):
        for block in content:
            print_block(
                block,
                source=source,
                show_thinking=show_thinking,
                show_tool_results=show_tool_results,
                max_tool_result_chars=max_tool_result_chars,
            )
        return

    print(f"\n{message_type} content:", flush=True)
    print(repr(content), flush=True)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run a Claude Agent SDK workflow to implement a paper-grounded Rocq/Coq consensus protocol model."
    )
    parser.add_argument(
        "--project-dir",
        default=DEFAULT_PROJECT_DIR,
        help=f"Rocq/Coq project directory. Default: {DEFAULT_PROJECT_DIR}",
    )
    parser.add_argument(
        "--protocol",
        default=DEFAULT_PROTOCOL_NAME,
        help=f"Protocol name, e.g., EPaxos or SwiftPaxos. Default: {DEFAULT_PROTOCOL_NAME}",
    )
    parser.add_argument(
        "--paper",
        default=DEFAULT_PAPER_PATH,
        help=f"Path to the protocol paper PDF. Default: {DEFAULT_PAPER_PATH}",
    )
    parser.add_argument(
        "--output",
        default=DEFAULT_OUTPUT_FILE,
        help=f"Target Coq file name. Default: {DEFAULT_OUTPUT_FILE}",
    )
    parser.add_argument(
        "--model",
        default=DEFAULT_MODEL,
        help=f"Claude model name. Default: {DEFAULT_MODEL}",
    )
    return parser.parse_args()


async def main() -> None:
    args = parse_args()

    prompt = build_prompt(
        project_dir=args.project_dir,
        protocol_name=args.protocol,
        paper_path=args.paper,
        output_file=args.output,
    )

    print("Starting fast-path consensus protocol agent...\n", flush=True)
    print(f"Project dir: {args.project_dir}", flush=True)
    print(f"Protocol:    {args.protocol}", flush=True)
    print(f"Paper:       {args.paper}", flush=True)
    print(f"Output file: {args.output}", flush=True)
    print(f"Model:       {args.model}\n", flush=True)

    options = ClaudeAgentOptions(
        cwd=args.project_dir,
        allowed_tools=["Read", "Write", "Edit", "Bash"],
        permission_mode="acceptEdits",
        model=args.model,
    )

    async for message in query(
        prompt=prompt,
        options=options,
    ):
        print_message(
            message,
            show_thinking=False,
            show_tool_results=True,
            max_tool_result_chars=2000,
        )


if __name__ == "__main__":
    asyncio.run(main())
