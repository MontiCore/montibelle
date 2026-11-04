export class MissingGitlabToken extends Error {

  constructor() {
    super(`Could not find a valid Gitlab token in "~/.montibelle/accesstoken.txt"`);
  }

}