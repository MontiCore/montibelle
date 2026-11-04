from urllib.parse import urlparse

from flask import make_response, redirect, render_template, request, url_for, current_app
from flask_login import current_user, login_required, login_user, logout_user

from forms.auth import LoginForm
from cluster.deployment import CodeServerDeployment
from services.user_service import check_user, get_user, is_pro_or_admin


@login_required
def index():
  logout = request.args.get(key="logout", default=False)
  if logout:
    resp = make_response(render_template(
      "index.html",
      logout="True",
      is_pro=is_pro_or_admin(current_user.username),
    ))
    deployments, _ = CodeServerDeployment.get_all()
    if deployments:
      user_deployments = list(filter(lambda d: d.is_owner(str(logout)), deployments))

      for deployment in user_deployments:
        current_app.logger.debug(f"Clearing cookie for instance {deployment.name()}")
        resp.set_cookie(
          key="code-server-session",
          value="clear",
          path=f"/instances/{deployment.name()}",
          domain="." + urlparse(request.base_url).hostname,
          max_age=0,
        )

    return resp

  return render_template(
    "index.html", is_pro=is_pro_or_admin(current_user.username)
  )


def login():
  form = LoginForm()
  next_url = request.values.get("next")

  if form.validate_on_submit():
    if check_user(form.username.data, form.password.data):
      login_user(get_user(form.username.data), remember=form.remember.data)
      current_app.logger.debug(f"[/login] next url: {next_url}")
      if next_url and urlparse(next_url).netloc == "":
        return redirect(next_url)
      return redirect(url_for("index"))

    return "<h1>Invalid username or password</h1>"

  return render_template("login.html", form=form, next_url=next_url)


@login_required
def logout():
  id = current_user.id
  logout_user()
  return redirect(url_for("index") + f"?logout={id}")
