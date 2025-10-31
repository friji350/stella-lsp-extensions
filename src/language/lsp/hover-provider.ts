import { AstNode, CstUtils, LangiumDocument, MaybePromise } from "langium";
import { AstNodeHoverProvider } from "langium/lsp";
import { Hover, HoverParams } from "vscode-languageserver";
import { isExtension } from "../generated/ast.js";
import { extensionDocLinks, isRecognizedExtension } from "../extensions.js";
import { StellaServices } from "../stella-module.js";
import { isType } from "typir";
import { TypirStellaServices } from "../type-system/stella-type-checker.js";

export class HoverProvider extends AstNodeHoverProvider {
  private typir: TypirStellaServices;

  constructor(services: StellaServices) {
    super(services);
    this.typir = services.typir;
  }

  override async getHoverContent(
    document: LangiumDocument,
    params: HoverParams
  ): Promise<Hover | undefined> {
    const root = document.parseResult.value.$cstNode;
    if (!root) {
      return;
    }
    const offset = document.textDocument.offsetAt(params.position);
    const cstNode = CstUtils.findLeafNodeAtOffset(root, offset);

    if (!cstNode) {
      return;
    }

    if (isExtension(cstNode.astNode) && isRecognizedExtension(cstNode.text)) {
      // Extension specifically needs the LeafCstNode at hover position (not provided to `getAstNodeHoverContent`)
      // TODO: open a PR to Langium to provide the HoverParams (or at least the position) to `getAstNodeHoverContent`

      const link = extensionDocLinks[cstNode.text];
      if (!link) {
        return;
      }

      return {
        contents: {
          kind: "markdown",
          value: `Go to [${cstNode.text} documentation](${link})`,
        },
        range: cstNode.range,
      };
    }

    return super.getHoverContent(document, params);
  }

  protected override getAstNodeHoverContent(
    node: AstNode
  ): MaybePromise<string | undefined> {
    const type = this.typir.Inference.inferType(node);
    if (isType(type)) {
      return type.getName();
    }

    return undefined;
  }
}
