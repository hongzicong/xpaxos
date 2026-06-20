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

PROTOCOL_OVERRIDES = {
    "EPaxos": r"""
## EPaxos mandatory override

The fast quorum size in EPaxos is `f + floor((f + 1) / 2)` under `n = 2 * f + 1`. Do not add +1, use ceil, or change the quorum size.

In this adopt-commit abstraction, values are ProcessIds. Treat value v as the command whose command leader is process v.

Unlike FastPaxos, only command leader v may output Commit v; other replicas may only pre-accept v and acknowledge it. Prove:

    ep_output (local s p) = Some (Commit v) -> p = v

For EPaxos Recoverability, absolutely do not follow the Recoverability proof strategy in `FastPaxos.v`; that fast-quorum/live-quorum intersection argument is false for the optimized quorum.

In particular, DO NOT define

    B := Aw ∩ alive

and DO NOT try to prove

    Av ∩ B ≠ ∅
    or
    n < |Av| + |B|

This is exactly the wrong FastPaxos-style proof route and is false for the EPaxos optimized quorum.

Instead count non-alive nodes: if different values v and w are committed in two reachable states equal on alive replicas, then leaders v and w and every node in the intersection of the two commit certificates Av ∩ Aw must be non-alive. These sets are disjoint, so non-alive nodes are at least:

    2 + (2 * ep_quorum - n)

With `n = 2 * f + 1` and `ep_quorum = f + floor((f + 1) / 2)`, this is `2 * floor((f + 1) / 2) + 1 > f`, contradicting that at most f nodes are non-alive.

When implementing Recoverability, first prove helper lemmas for:
1. all replicas in Av ∩ Aw are non-alive;
2. leader v is non-alive;
3. leader w is non-alive;
4. these three groups are disjoint;
5. together they imply more than f non-alive nodes.

Do not attempt to repair any proof obligation of the form `n < length Av + length (Aw ∩ alive)`; delete that route instead.
""",

    "SwiftPaxos": r"""
## SwiftPaxos mandatory override

Do not model SwiftPaxos as renamed Fast Paxos.

The model must include a distinguished leader.

Every direct fast quorum used for fast commit must include the leader.

The model must distinguish at least two kinds of acknowledgements:

1. ordinary acknowledgement of a proposal;
2. leader-choice acknowledgement, meaning that the sender knows this value is the one accepted/forwarded by the leader.

The model must include the leader-choice fast path:

1. the leader forwards or broadcasts the first proposal it accepts;
2. a replica receiving the leader-forwarded proposal overrides its tentative accepted value with the leader's value;
3. the replica records that this value is the leader's accepted choice;
4. the replica sends a distinct leader-choice acknowledgement;
5. a proposer may fast-commit either:
   - by receiving acknowledgements from a fast quorum that includes the leader; or
   - by receiving f + 1 leader-choice acknowledgements.

The second case is still part of the fast path, even though it goes through the leader.

If modeling the fixed-quorum variant of SwiftPaxos, define one predetermined quorum of size f + 1 that includes the leader. In that case, do not also use FastPaxos-sized quorums.

Do not replace the leader-choice path with a generic FastPaxos quorum-intersection proof.
"""
}

PROMPT_TEMPLATE = r"""
You are working in the Rocq project directory:

`__PROJECT_DIR__`

Your task is to implement a fast-path adopt-commit abstraction for the distributed consensus protocol named:

`__PROTOCOL_NAME__`

The protocol paper is located at:

`__PAPER_PATH__`

The target output file is:

`__OUTPUT_FILE__`

`make` success is a hard requirement for this task.

A compiling file that is just a renamed copy of an existing implementation is not acceptable.

Work autonomously. Do not ask for user input, confirmation, or preference at any point. If you face a decision, choose the path most likely to produce a compilable, Admitted-free proof.

## Scope

This task is NOT to formalize the full protocol from the paper.

The goal is to implement a small adopt-commit instantiation that captures the protocol's fast-path quorum idea and proves the same four high-level framework properties.

Implement and prove ONLY the fast path.

## Important project files

The project directory contains:

- `AdoptCommit.v`: this file models the adopt-commit abstraction and the arbitrary executions allowed by asynchronous networks. It defines `ACProtocol`, `Reachable`, and high-level properties such as Validity, Agreement, Convergence, and Recoverability.
- `FastPaxos.v`: this file instantiates the adopt-commit model with the fast path of FastPaxos and proves its Validity, Agreement, Convergence, and Recoverability.
- `Makefile`: builds the project using `rocq compile`.

# Phase 1 — Read

## Step 1 — Read the existing Coq framework

Read `AdoptCommit.v`, `FastPaxos.v`, and `Makefile`.

The goal is to understand what the framework expects from an instantiation — what types to define, what the `step` function must express, and how the four high-level properties are stated.

Use `FastPaxos.v` as an interface and proof-style reference, not as a protocol-specific proof template.

## Step 2 — Read the protocol paper

Read the protocol paper at `__PAPER_PATH__`.

The goal is to understand `__PROTOCOL_NAME__`'s fast-path commit condition clearly enough to translate it into a `step` function and commit certificate type, and to identify where it differs from FastPaxos.

__PROTOCOL_OVERRIDE__

# Phase 2 — Think

## Step 3 — Analyze protocol-specific properties

Identify every place where `__PROTOCOL_NAME__`'s fast path differs from FastPaxos — each difference means a different type, a different lemma, or a different proof strategy.

Create `__PROJECT_DIR__/__OUTPUT_FILE__` containing only a comment block that records the analysis. Do not write any Rocq definitions or theorems yet.

# Phase 3 — Implement

## Step 4 — Implement a fast-path-only abstraction

Expand the comment-only file created in Step 3 into a skeleton with type and definition declarations. Use Edit calls (~80 lines each) to add content incrementally.

Use names prefixed by `__PROTOCOL_NAME__` or a suitable lowercase abbreviation.

Add `__OUTPUT_FILE__` to the `Makefile` immediately after the existing protocol files:

```make
$(ROCQC) __OUTPUT_FILE__
```

## Step 5 — Prove the four properties

Prove the four properties incrementally. Write exactly one new lemma or theorem per edit. Do not append multiple helper lemmas and a theorem in one large edit. After each new lemma or theorem, run `make` before adding the next one.
```
__PROTOCOL_NAME___Validity
__PROTOCOL_NAME___Agreement
__PROTOCOL_NAME___Convergence
__PROTOCOL_NAME___Recoverability
```

These theorems should be interpreted at the adopt-commit abstraction level.

Important:

- `__PROTOCOL_NAME___Validity` should show that every output value (Commit or Adopt) was proposed by a valid proposer.
- `__PROTOCOL_NAME___Agreement` should show that if any process commits v, then every process that produces any output (Commit OR Adopt) must output v.
- `__PROTOCOL_NAME___Convergence` should use the uniqueness of valid proposer values as in the framework: with a unique proposer, every terminating process must Commit (Adopt is not acceptable).
- `__PROTOCOL_NAME___Recoverability` captures the precise property defined in `AdoptCommit.v`: for any two reachable states `s` and `s'` that agree on the local states of at least `n - f` processes, if `s` has a `Commit v` and `s'` has a `Commit w`, then `v = w`.

The framework provides only `f_lt_n : f < n` as its base hypothesis. If the fast quorum formula for `__PROTOCOL_NAME__` requires a stronger assumption, for example `n = 2 * f + 1` and `0 < f`, add it as an explicit `Hypothesis` in your file and justify it with a reference to the paper.

After all four properties are proved, run a final `make` and verify:

```bash
grep -rn "Admitted\|admit\b\|^Axiom" __OUTPUT_FILE__
```

The grep must print nothing. Do not hide proof failures by weakening the model without justification.

# Phase 4 — Summary

## Step 6 — Final audit report

After success, print a concise final report containing:

1. whether `make` succeeded
2. whether `__OUTPUT_FILE__` is fast-path-only
3. the fast quorum formula used
4. the extra assumptions on `n` and `f`, if any
5. which properties were proved
6. confirmation that no `Admitted`, `admit`, or `Axiom` remains
7. the final list of changed files
8. a clear statement that this is not a full formalization of `__PROTOCOL_NAME__`
"""



def build_prompt(project_dir: str, protocol_name: str, paper_path: str, output_file: str) -> str:
    override = PROTOCOL_OVERRIDES.get(protocol_name, "")
    return (
        PROMPT_TEMPLATE
        .replace("__PROJECT_DIR__", project_dir)
        .replace("__PROTOCOL_NAME__", protocol_name)
        .replace("__PAPER_PATH__", paper_path)
        .replace("__OUTPUT_FILE__", output_file)
        .replace("__PROTOCOL_OVERRIDE__", override)
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
        description="Run a Claude Agent SDK workflow to implement a paper-grounded Rocq consensus protocol model."
    )
    parser.add_argument(
        "--project-dir",
        default=DEFAULT_PROJECT_DIR,
        help=f"Rocq project directory. Default: {DEFAULT_PROJECT_DIR}",
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
        effort="xhigh",
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
