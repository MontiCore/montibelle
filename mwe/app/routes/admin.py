from flask import redirect, render_template, request, url_for
from flask_login import current_user, login_required

from forms.auth import CreateUserForm
from services.user_service import (
  change_password,
  create_user,
  delete_user,
  get_user,
  get_users,
  is_admin,
  make_admin,
  make_pro,
  revoke_admin,
  revoke_pro,
)


@login_required
def admin_panel():
  if not is_admin(current_user.username):
    return "unauthorized", 403

  _delete_username = request.args.get("delete")
  if _delete_username:
    if _delete_username == current_user.username:
      return "your cant delete yourself", 403
    delete_user(_delete_username)

  _promote_admin = request.args.get("makeadmin")
  if _promote_admin:
    if _promote_admin == current_user.username:
      return "your cant delete yourself", 403
    make_admin(_promote_admin)

  _revoke_admin = request.args.get("revokeadmin")
  if _revoke_admin:
    if _revoke_admin == current_user.username:
      return "your cant demote yourself", 403
    revoke_admin(_revoke_admin)

  _promote_pro = request.args.get("makepro")
  if _promote_pro:
    make_pro(_promote_pro)

  _revoke_pro = request.args.get("revokepro")
  if _revoke_pro:
    revoke_pro(_revoke_pro)

  form = CreateUserForm()
  if form.validate_on_submit():
    if get_user(form.username.data):
      return "<h1>username does already exist</h1>"

    create_user(form.username.data, form.mail.data, form.password.data)
    return redirect(url_for("admin_panel"))

  __username_change_password = request.form.get("changepassword")
  __new_password = request.form.get("password")
  if __username_change_password and __new_password:
    change_password(__username_change_password, __new_password)
    return redirect(
      url_for("admin_panel") + "?success='Password changed!'"
    )

  if request.args.get("success"):
    return render_template(
      "admin.html",
      users=get_users(),
      success="Password changed!",
      form=form,
    )

  return render_template("admin.html", users=get_users(), form=form)
